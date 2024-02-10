import os
import pprint
from pathlib import Path

from dotenv import load_dotenv
from lean_dojo import Dojo, LeanError, LeanGitRepo
from llama_cpp import Llama

from coq_to_lean.examples import EXAMPLES
from coq_to_lean.sources import Coq

load_dotenv()

_d = os.path.dirname
PROJECT_ROOT = Path(_d(_d(_d(__file__)))) / "data" / "lf"


Q_TEMPLATE = "Q:\n```coq\n{cmd}```\n\nA:"


def main():
    coq = Coq(PROJECT_ROOT, "Basics.v")

    llm = Llama(
        os.getenv("MODEL_PATH"),
        n_gpu_layers=-1,
        n_ctx=4096,
    )

    examples = "".join(
        f"""\
Q:
```coq
{coq_src}```

A:
```lean
{lean_src}```

"""
        for coq_src, lean_src in zip(*EXAMPLES.values())
    )

    repo = LeanGitRepo("https://github.com/f64u/lean_example", "main")
    with Dojo((repo, "LeanExample/Basic.lean", 2), hard_timeout=15) as (dojo, state):
        for cmd in coq.commands[3:]:
            messages = examples + Q_TEMPLATE.format(cmd=cmd)

            print(f"Trying to translate the following command:\n{cmd}")

            while True:
                completion = llm(messages, max_tokens=2048, stop="Q:")
                pprint.pprint(completion)

                lean_cmd = (
                    completion["choices"][0]["text"]
                    .strip()
                    .lstrip("```lean\n")
                    .rstrip("```")
                )
                new_state = dojo.run_cmd(state, lean_cmd)
                if not isinstance(new_state, LeanError):
                    state = new_state
                    print(f"Translated lean:\n{lean_cmd}\n")
                    break

                print(f"Error executing the lean command, error is {new_state}")

                messages += f"""\
A: ```lean
{lean_cmd}```

Q: Error was {new_state.error}. Try again.

A:"""


if __name__ == "__main__":
    main()
