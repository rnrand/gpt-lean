import os

import click
from llama_cpp import Llama
from prompt_toolkit.lexers import PygmentsLexer
from prompt_toolkit.shortcuts import prompt
from rich.columns import Columns
from rich.console import Console
from rich.panel import Panel
from rich.prompt import Confirm
from rich.syntax import Syntax

from coq_to_lean import PROJECT_ROOT, truncate
from coq_to_lean.destinations import Err
from coq_to_lean.destinations.lean4 import Lean4
from coq_to_lean.languages import LANGUAGES
from coq_to_lean.sources.coq import Coq

Q_TEMPLATE = """\
Q:
```{lang1}
{cmd1}```

A:"""

QA_TEMPLATE = (
    Q_TEMPLATE
    + """\

```{lang2}
{cmd2}```

"""
)


@click.command()
@click.option(
    "--project_root",
    default=PROJECT_ROOT / "data" / "lf",
    help="Root of the source project",
)
@click.option(
    "--model",
    default=os.getenv("MODEL_PATH"),
    help="What LLM to use for translation",
)
@click.option("--ctx-size", default=4096, help="Context size")
@click.option(
    "--src-lang",
    default="coq",
    type=click.Choice(list(LANGUAGES.keys())),
    help="The source language",
)
@click.option(
    "--dest-lang",
    default="lean4",
    type=click.Choice(list(LANGUAGES.keys())),
    help="The destination language",
)
@click.argument("file")
def main(project_root, file, model, src_lang, dest_lang, ctx_size):
    console = Console()

    src_lang_spec = LANGUAGES[src_lang]
    dest_lang_spec = LANGUAGES[dest_lang]

    with console.status(
        f"[bold green]Starting {src_lang_spec['human_readable_name']}..."
    ):
        src_manager = src_lang_spec["src_manager"](project_root, file)

    with console.status("[bold green]Loading model..."):
        llm = Llama(model, n_gpu_layers=-1, n_ctx=ctx_size, verbose=False)

    examples = "".join(
        QA_TEMPLATE.format(lang2=dest_lang, lang1=src_lang, cmd2=cmd2, cmd1=cmd1)
        for cmd1, cmd2 in zip(src_lang_spec["examples"], dest_lang_spec["examples"])
    )

    with console.status(
        f"[bold green]Loading {dest_lang_spec['human_readable_name']}..."
    ):
        dest_manager = dest_lang_spec["dest_manager"]()

    for cmd1 in src_manager.commands[3:]:
        messages = examples + Q_TEMPLATE.format(lang1=src_lang, cmd1=cmd1)

        # print(f"Trying to translate the following command:\n{cmd}")

        while True:
            with console.status("[bold green]Translating..."):
                completion = llm(
                    truncate(llm, messages, ctx_size), max_tokens=ctx_size, stop="Q:"
                )

            cmd2 = (
                completion["choices"][0]["text"]
                .strip()
                .removeprefix(f"```{dest_lang}\n")
                .removesuffix("```")
            )
            cmd1_syntax = Syntax(
                cmd1, src_lang_spec["syntax_name"], background_color="default"
            )
            cmd2_syntax = Syntax(
                cmd2, dest_lang_spec["syntax_name"], background_color="default"
            )

            console.print(
                Columns(
                    [
                        Panel(cmd1_syntax, title=src_lang_spec["human_readable_name"]),
                        Panel(cmd2_syntax, title=dest_lang_spec["human_readable_name"]),
                    ],
                    expand=True,
                    equal=True,
                    align="left",
                )
            )
            good = Confirm.ask("Looks good?")
            if not good:
                cmd2 = prompt(
                    f"{dest_lang}> ",
                    lexer=PygmentsLexer(dest_lang_spec["lexer"]),
                    multiline=True,
                    default=cmd2,
                )

            new_state = dest_manager.check(cmd2)
            if not isinstance(new_state, Err):
                dest_manager.state = new_state

                messages += QA_TEMPLATE.format(
                    lang1=src_lang, cmd1=cmd1, lang2=dest_lang, cmd2=cmd2
                )
                break
            console.print(
                f"[bold red]:bomb: That did not work. Error was:\n{new_state.error}\nLet's try again."
            )


if __name__ == "__main__":
    main()
