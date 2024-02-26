from typing import Optional, Type, TypedDict

from pygments.lexer import Lexer
from pygments.lexers.lean import Lean3Lexer
from pygments.lexers.textfmts import NotmuchLexer
from pygments.lexers.theorem import CoqLexer

from coq_to_lean.destinations import Destination
from coq_to_lean.destinations.english import English as EnglishDest
from coq_to_lean.destinations.lean4 import Lean4 as Lean4Dest
from coq_to_lean.sources import Source
from coq_to_lean.sources.coq import Coq as CoqSrc
from coq_to_lean.sources.english import English as EnglishSrc


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
    "english": {
        "human_readable_name": "English",
        "syntax_name": "english",
        "dest_manager": EnglishDest,
        "src_manager": EnglishSrc,
        "lexer": NotmuchLexer,
        "examples": [
            "A day is either Sunday, Monday, Tuesday, Wednesday, Thursday, Friday, or Saturday.",
            "To express the notion of a function 'next weekday' : day -> day, we say monday maps to tuesday, tuesday maps to wednesday, wednesday maps to thursday, thursday maps to friday, and all of friday saturday and sunday map to monday.",
            "As an example, we can prove that the next weekday of the next weekday of saturday is tuesday.",
        ],
    },
}

_lengths = [len(ls["examples"]) for ls in LANGUAGES.values()]
_sum = sum(_lengths)

if not all(length == _sum / len(LANGUAGES) for length in _lengths):
    raise Exception("You should have the same number of examples for all languages!")
