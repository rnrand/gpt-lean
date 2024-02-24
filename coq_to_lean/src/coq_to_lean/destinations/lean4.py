from lean_dojo import CommandState, Dojo, LeanError, LeanGitRepo

from coq_to_lean.destinations import Destination, Err, Ok, State


class Lean4(Destination):
    def __init__(self):
        repo = LeanGitRepo("https://github.com/f64u/lean_example", "main")
        self.dojo, state = Dojo((repo, "LeanExample/Basic.lean", 2)).__enter__()
        if isinstance(state, LeanError):
            raise Exception("Cannot initialize Lean 4")
        self._state = Ok(state)

    @property
    def state(self) -> State[CommandState, LeanError]:
        return self._state

    @state.setter
    def state(self, new_state: State[CommandState, LeanError]):
        self._state = new_state

    def check(self, part) -> State[CommandState, LeanError]:
        if isinstance(self.state, Err):
            return self.state

        # This is mainly for the type checker.
        assert isinstance(self.state, Ok)

        new_state = self.dojo.run_cmd(self.state.value, part)
        if isinstance(new_state, CommandState):
            return Ok(new_state)
        else:
            return Err(new_state)

    def __del__(self):
        self.dojo.__exit__(None, None, None)
