import os
from pathlib import Path
from typing import Iterator, Optional

from coq_to_lean.lsp import Lsp
from coq_to_lean.sources import Source


class Coq(Source):
    def __init__(self, project_root: os.PathLike, file: Optional[str] = None):
        self.project_root = Path(project_root)
        self.active_file = file
        self.commands: list[str] = []
        self._iter: Optional[Iterator[str]] = None
        self.coq_lsp = Lsp("coq-lsp", project_root)
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
