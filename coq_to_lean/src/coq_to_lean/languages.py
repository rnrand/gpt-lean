from typing import Optional, Type, TypedDict

from pygments.lexer import Lexer
from pygments.lexers.lean import Lean3Lexer
from pygments.lexers.theorem import CoqLexer

from coq_to_lean.destinations import Destination
from coq_to_lean.destinations.lean4 import Lean4 as Lean4Dest
from coq_to_lean.sources import Source
from coq_to_lean.sources.coq import Coq as CoqSrc


class LanguageSpec(TypedDict):
    human_readable_name: str
    syntax_name: str
    lexer: Type[Lexer]
    src_manager: Optional[Type[Source]]
    dest_manager: Optional[type[Destination]]
    examples: list[str]


LANGUAGES: dict[str, LanguageSpec] = {
    "coq": {
        "human_readable_name": "Coq",
        "syntax_name": "coq",
        "lexer": CoqLexer,
        "src_manager": CoqSrc,
        "dest_manager": None,
        "examples": [
            """\
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
""",
            """\
Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.
""",
            """\
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.""",
        ],
    },
    "lean4": {
        "human_readable_name": "Lean 4",
        "syntax_name": "lean",
        "lexer": Lean3Lexer,
        "src_manager": None,
        "dest_manager": Lean4Dest,
        "examples": [
            """\
inductive Day where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday""",
            """\
def next_weekday (d : Day) : Day :=
   match d with
   | .monday => .tuesday
   | .tuesday => .wednesday
   | .wednesday => .thursday
   | .thursday => .friday
   | .friday => .monday
   | .saturday => .monday
   | .sunday => .monday""",
            """\
example : (next_weekday (next_weekday .saturday)) = .tuesday := sorry""",
        ],
    },
}

_lengths = [len(ls["examples"]) for ls in LANGUAGES.values()]
_sum = sum(_lengths)

if not all(length == _sum / len(LANGUAGES) for length in _lengths):
    raise Exception("You should have the same number of examples for all languages!")
