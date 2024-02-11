import os

import click
from lean_dojo import Dojo, LeanError, LeanGitRepo
from llama_cpp import Llama
from prompt_toolkit.lexers import PygmentsLexer
from prompt_toolkit.shortcuts import prompt
from pygments.lexers.lean import Lean3Lexer
from rich.columns import Columns
from rich.console import Console
from rich.panel import Panel
from rich.prompt import Confirm
from rich.syntax import Syntax

from coq_to_lean import PROJECT_ROOT, truncate
from coq_to_lean.examples import EXAMPLES
from coq_to_lean.sources import Coq

Q_TEMPLATE = """\
Q:
```coq
{coq_src}```

A:"""

SRC_TEMPLATE = (
    Q_TEMPLATE
    + """\

```lean
{lean_src}```

"""
)


@click.command()
@click.option(
    "--project_root",
    default=PROJECT_ROOT / "data" / "lf",
    help="Root of the Coq project",
)
@click.option(
    "--model",
    default=os.getenv("MODEL_PATH"),
    help="What LLM to use for translation",
)
@click.argument("file")
def main(project_root, file, model):
    console = Console()

    with console.status("[bold green]Starting Coq LSP..."):
        coq = Coq(project_root, file)

    with console.status("[bold green]Loading model..."):
        llm = Llama(model, n_gpu_layers=-1, n_ctx=4096, verbose=False)

    examples = "".join(
        SRC_TEMPLATE.format(coq_src=coq_src, lean_src=lean_src)
        for coq_src, lean_src in zip(*EXAMPLES.values())
    )

    with console.status("[bold green]Loading Lean Dojo..."):
        repo = LeanGitRepo("https://github.com/f64u/lean_example", "main")
        dojo, state = Dojo((repo, "LeanExample/Basic.lean", 2)).__enter__()

    for cmd in coq.commands[3:]:
        messages = examples + Q_TEMPLATE.format(coq_src=cmd)

        # print(f"Trying to translate the following command:\n{cmd}")

        while True:
            with console.status("[bold green]Translating..."):
                completion = llm(
                    truncate(llm, messages, 2048), max_tokens=2048, stop="Q:"
                )

            lean_cmd = (
                completion["choices"][0]["text"]
                .strip()
                .removeprefix("```lean\n")
                .removesuffix("```")
            )
            coq_syntax = Syntax(cmd, "coq", background_color="default")
            lean_syntax = Syntax(lean_cmd, "lean", background_color="default")
            console.print(
                Columns(
                    [
                        Panel(coq_syntax, title="Coq"),
                        Panel(lean_syntax, title="Lean 4"),
                    ],
                    expand=True,
                    equal=True,
                    align="left",
                )
            )
            good = Confirm.ask("Looks good?")
            if not good:
                lean_cmd = prompt(
                    "lean4> ",
                    lexer=PygmentsLexer(Lean3Lexer),
                    multiline=True,
                    default=lean_cmd,
                )

            new_state = dojo.run_cmd(state, lean_cmd)
            if not isinstance(new_state, LeanError):
                state = new_state

                messages += SRC_TEMPLATE.format(coq_src=cmd, lean_src=lean_cmd)
                break
            console.print(
                f"[bold red]:bomb: That did not work. Error was:\n{new_state.error}\nLet's try again."
            )

    dojo.__exit__()


if __name__ == "__main__":
    main()
