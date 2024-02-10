EXAMPLES: dict[str, list[str]] = {
    "coq": [
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
    "lean4": [
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
example text_next_weekday : (next_weekday (next_weekday .saturday)) = .tuesday := sorry""",
    ],
}

_lengths = [len(ts) for ts in EXAMPLES.values()]
_sum = sum(_lengths)

if not all(length == _sum / len(EXAMPLES) for length in _lengths):
    raise Exception("You should have the same number of examples for all languages!")
