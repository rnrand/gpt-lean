import json
import os
import subprocess
from typing import Any


class Lsp:
    LSP_MESSAGE_TEMPLATE: dict[str, Any] = {
        "jsonrpc": "2.0",
        "id": None,
        "method": None,
        "params": None,
    }

    def __init__(self, command, project_root: os.PathLike):
        self.next_id = 1
        self.backlog: list[dict] = []
        self.process = subprocess.Popen(
            command.split(),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )

        self.communicate(
            "initialize",
            {
                "rootUri": f"file://{project_root}",
            },
        )
        # time.sleep(1)

        self.send_notification("initialized", {})

    def _write_message(self, method, params, is_notification=False) -> int:
        message = Lsp.LSP_MESSAGE_TEMPLATE.copy()
        message["method"] = method
        message["params"] = params
        if not is_notification:
            message["id"] = self.next_id
            self.next_id += 1
        else:
            del message["id"]

        message_json = json.dumps(message)

        if self.process.stdin is None:
            raise Exception("It's a pipe??")

        self.process.stdin.write(
            bytes(f"Content-Length: {len(message_json)}\r\n\r\n", "utf-8")
        )
        self.process.stdin.write(bytes(message_json, "utf-8"))
        self.process.stdin.flush()

        return message.get("id") or -1

    def _read_message(self) -> dict:
        assert self.process.stdout is not None, "It's a pipe??"

        content = int(self.process.stdout.readline().split()[1])
        self.process.stdout.readline()
        json_ = self.process.stdout.read(content).strip()
        return json.loads(json_)

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
