import asyncio
import subprocess
import json
import os
from pathlib import Path
import pprint
from lean_dojo import *
from llama_cpp import Llama
from dotenv import load_dotenv

load_dotenv()

PROJECT_ROOT = Path(os.path.dirname(os.path.dirname(__file__))) / "data/lf"

SYSTEM_MESSAGE = """\
You are to translate valid Coq code to valid Lean 4 code. You'll be given a snippet of Coq code, and your task is to translate the code to valid Lean 4 code. You should only answer with the valid Lean 4 code. Remember that Lean 4 does _not_ use "begin" nor "end" for its tactic language, though Lean 3 does. You are to provide code in Lean 4. Only translate the singular Coq item given; do not translate other dependencies. Do not answer in anything but code.

Here's an example:

Coq:
```coq
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.```

Lean 4:
```lean
inductive day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday```

Now go ahead and do the same."""

USER_MESSAGE_TEMPLATE = """\
Coq:
```coq
{}```

Lean 4:
"""

ERROR_MESSAGE_TEMPLATE = """\
The code you gave resulted in the following error:
{}

Try again to provide valid Lean 4 code while still following the rules prescribed earlier. Only provide the code.
"""

LSP_MESSAGE_TEMPLATE = {
    "jsonrpc": "2.0",
    "id": 0,
    "method": None,
    "params": None,
}


class Coq:

    def __init__(self, project_root):
        self.backlog = []
        self.process = subprocess.Popen(["coq-lsp"],
                                        stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT)

        self.communicate("initialize", {
            "rootUri": f"file://{project_root}",
        })

        self.send_notification("initialized", {})

    def _write_message(self, method, params, is_notification=False) -> int:
        message = LSP_MESSAGE_TEMPLATE.copy()
        message["method"] = method
        message["params"] = params
        if not is_notification:
            message["id"] = LSP_MESSAGE_TEMPLATE["id"] = message["id"] + 1
        else:
            del message["id"]

        message_json = json.dumps(message)

        self.process.stdin.write(
            bytes(f"Content-Length: {len(message_json)}\r\n\r\n", "utf-8"))
        self.process.stdin.write(bytes(message_json, "utf-8"))
        self.process.stdin.flush()

        return message.get("id") or -1

    def _read_message(self) -> dict:
        self.process.stdout.readline()
        self.process.stdout.readline()
        return json.loads(self.process.stdout.readline().strip())

    # This function assumes synchronous execution
    def communicate(self, method, params) -> dict:
        id_ = self._write_message(method, params)
        while True:
            response = self._read_message()
            if response.get("id") == id_:
                return response
            self.backlog.append(response)

    def send_notification(self, method, params):
        self._write_message(method, params, is_notification=True)


async def main():

    coq = Coq(PROJECT_ROOT)

    file_path = PROJECT_ROOT / 'Basics.v'
    file_uri = f"file://{file_path}"
    with open(file_path) as f:
        file_content = f.read()

    coq.send_notification(
        "textDocument/didOpen",
        {
            "textDocument": {
                "uri": file_uri,
                "languageId": "coq",
                "version": 1,
                "text": file_content,
            }
        },
    )

    value = coq.communicate("textDocument/documentSymbol",
                            {"textDocument": {
                                "uri": file_uri,
                            }})

    commands = []
    for term in value["result"]:
        start = term["range"]["start"]["offset"]
        end = term["range"]["end"]["offset"]
        commands.append(file_content[start:end])

    llm = Llama(
        os.getenv("MODEL_PATH"),
        n_gpu_layers=-1,
        n_ctx=2048,
    )

    repo = LeanGitRepo("https://github.com/f64u/lean_example", "main")
    with Dojo((repo, "LeanExample/Basic.lean", 4)) as (dojo, state):
        for cmd in commands:
            messages = [{
                "role": "system",
                "content": SYSTEM_MESSAGE,
            }, {
                "role": "user",
                "content": USER_MESSAGE_TEMPLATE.format(cmd),
            }]

            while True:
                completion = llm.create_chat_completion(messages=messages)
                pprint.pprint(completion)

                lean_cmd = completion["choices"][0]["message"][
                    "content"].lstrip("```lean\n").rstrip("```")
                new_state = dojo.run_cmd(state, lean_cmd)
                if not isinstance(new_state, LeanError):
                    state = new_state
                    print(lean_cmd)
                    print(state)
                    break

                messages.extend([
                    {
                        "role": "assistant",
                        "content":
                        completion["choices"][0]["message"]["content"]
                    },
                    {
                        "role": "user",
                        "content":
                        ERROR_MESSAGE_TEMPLATE.format(new_state.error)
                    },
                ])


if __name__ == "__main__":
    asyncio.run(main())
