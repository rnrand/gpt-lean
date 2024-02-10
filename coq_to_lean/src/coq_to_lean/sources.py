import abc
import json
import os
import subprocess
from pathlib import Path
from typing import Any, Iterable, Iterator, Optional


class CoqLsp:
    LSP_MESSAGE_TEMPLATE: dict[str, Any] = {
        "jsonrpc": "2.0",
        "id": None,
        "method": None,
        "params": None,
    }

    def __init__(self, project_root: os.PathLike):
        self.next_id = 1
        self.backlog: list[dict] = []
        self.process = subprocess.Popen(
            ["coq-lsp"],
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

        self.send_notification("initialized", {})

    def _write_message(self, method, params, is_notification=False) -> int:
        message = CoqLsp.LSP_MESSAGE_TEMPLATE.copy()
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
        if self.process.stdout is None:
            raise Exception("It's a pipe??")

        self.process.stdout.readline()
        self.process.stdout.readline()
        return json.loads(self.process.stdout.readline().strip())

    # This function assumes synchronous execution
    def communicate(self, method, params) -> dict:
        id_ = self._write_message(method, params)
        print(f"{id_=}")
        while True:
            response = self._read_message()
            if response.get("id") == id_:
                return response
            self.backlog.append(response)

    def send_notification(self, method, params):
        self._write_message(method, params, is_notification=True)


class Source(abc.ABC, Iterable[str]):
    @abc.abstractmethod
    def get_next_part(self) -> str:
        raise NotImplementedError

    def __iter__(self):
        return self

    def __next__(self):
        return self.get_next_part()


class Coq(Source):
    def __init__(self, project_root: os.PathLike, file: Optional[str] = None):
        self.project_root = Path(project_root)
        self.active_file = file
        self.commands: list[str] = []
        self._iter: Optional[Iterator[str]] = None
        self.coq_lsp = CoqLsp(project_root)
        if file is not None:
            self.set_active_file(file)

    def set_active_file(self, file: str):
        self._file = file
        full_path = self.project_root / file
        with open(full_path) as f:
            file_content = f.read()

        file_uri = f"file://{full_path}"

        self.coq_lsp.send_notification(
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

        message = self.coq_lsp.communicate(
            "textDocument/documentSymbol",
            {
                "textDocument": {
                    "uri": file_uri,
                }
            },
        )

        commands = []
        for term in message["result"]:
            start = term["range"]["start"]["offset"]
            end = term["range"]["end"]["offset"]
            commands.append(file_content[start:end])

        self.commands = commands
        self._iter = iter(commands)

    def get_next_part(self) -> str:
        if self._iter is None:
            raise Exception("self._iter is None")

        return next(self._iter)
