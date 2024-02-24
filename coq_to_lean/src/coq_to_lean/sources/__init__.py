import abc
from typing import Iterable


class Source(abc.ABC, Iterable[str]):
    @abc.abstractmethod
    def get_next_part(self) -> str:
        raise NotImplementedError

    def __iter__(self):
        return self

    def __next__(self):
        return self.get_next_part()
