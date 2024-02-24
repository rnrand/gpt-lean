import abc
import dataclasses
from typing import Generic, TypeVar

T = TypeVar("T")
E = TypeVar("E")


@dataclasses.dataclass
class State(Generic[T, E]):
    pass


@dataclasses.dataclass
class Ok(State[T, E]):
    value: T


@dataclasses.dataclass
class Err(State[T, E]):
    error: E


class Destination(abc.ABC):
    @property
    def state(self) -> State[T, E]:
        raise NotImplementedError

    @state.setter
    def state(self, new_state: State[T, E]):
        raise NotImplementedError

    def check(self, part) -> State[T, E]:
        raise NotImplementedError
