from coq_to_lean.destinations import Destination, Ok


class English(Destination):
    @property
    def state(self):
        return Ok(())

    @state.setter
    def state(self, new_state):
        pass

    def check(self, part):
        return Ok(())
