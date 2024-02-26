import os
import subprocess
from pathlib import Path
from typing import Iterator, Optional

from coq_to_lean.lsp import Lsp
from coq_to_lean.sources import Source


class Lean4(Source):
    def __init__(self, project_root: os.PathLike, file: Optional[str] = None):
        self.project_root = Path(project_root)
        self.active_file = file
        self.commands: list[str] = []
        self._iter: Optional[Iterator[str]] = None
        os.chdir(project_root)
        subprocess.run(["lake", "build"])
        self.coq_lsp = Lsp("lean --server", project_root)
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
                    "languageId": "lean",
                    "version": 1,
                    "text": file_content,
                }
            },
        )

        response = self.coq_lsp.communicate(
            "textDocument/documentSymbol",
            {
                "textDocument": {
                    "uri": file_uri,
                }
            },
        )

        commands = []
        file_lines = file_content.split(os.linesep)
        for term in response["result"]:
            start_line = term["range"]["start"]["line"]
            start_char = term["range"]["start"]["character"]
            end_line = term["range"]["end"]["line"]
            end_char = term["range"]["end"]["character"]

            commands.append(
                (
                    file_lines[start_line][start_char:]
                    + os.linesep
                    + os.linesep.join(file_lines[start_line + 1 : end_line])
                    + os.linesep
                    + file_lines[end_line][:end_char]
                )
                if start_line != end_line
                else file_lines[start_line][start_char:end_char]
            )

        self.commands = commands
        self._iter = iter(commands)

    def get_next_part(self) -> str:
        if self._iter is None:
            raise Exception("self._iter is None")

        return next(self._iter)
