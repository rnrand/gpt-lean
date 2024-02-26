from pathlib import Path
import os
from typing import Iterator, Optional

from coq_to_lean.sources import Source


class English(Source):
    def __init__(self, project_root: os.PathLike, file: Optional[str] = None):
        self.project_root = Path(project_root)
        self.active_file = file
        self.commands: list[str] = []
        self._iter: Optional[Iterator[str]] = None
        if file is not None:
            self.set_active_file(file)

    def set_active_file(self, file: str):
        full_path = self.project_root / file

        with open(full_path) as f:
            self.commands = f.read().split(os.linesep * 2)

        self._iter = iter(self.commands)

    def get_next_part(self) -> str:
        if self._iter is None:
            raise Exception("self._iter is None")

        return next(self._iter)
