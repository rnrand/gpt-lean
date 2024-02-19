from abc import ABC, abstractmethod
from collections.abc import Iterable
from functools import partial as prt
from multiprocessing import Pool

import json
import pexpect
from pprint import pprint

import ipdb
from rich.console import Console
from rich.syntax import Syntax
from src.get_lean_repls import get_repl_v

console = Console()
syntax_lean = prt(Syntax, lexer="lean")


class LanguageServer(ABC):
    @abstractmethod
    def run_code(self, code: str, env=None, verbose=False):
        raise NotImplementedError


class LanguageServers:
    def __init__(self, language: str, version: str, num_servers: int = 1):
        if language == "lean":
            language_server_cls = LeanServer
        else:
            raise ValueError(f"Unknown language : {language}")
        path = get_repl_v(version)
        self.servers = tuple(language_server_cls(path) for _ in range(num_servers))

    def __getitem__(self, index):
        return self.servers[index]

    def run_code_batch(self, codes: Iterable[str], env=None, verbose=False):
        # TODO : need to work on it
        assert len(codes) <= len(self.servers)
        with Pool(len(codes)) as pool:
            return tuple(
                pool.starmap(
                    lambda server, code: server.run_code(code, env, verbose),
                    zip(self.servers, codes),
                )
            )


class LeanServer:
    """Adapted from https://github.com/zhangir-azerbayev/repl/blob/master/pylean/pylean/__init__.py"""

    def __init__(self, path_to_repl: str):
        # self.proc = pexpect.spawn(
        #     "lake env lean --run REPL/Main.lean", cwd=path_to_repl, encoding="utf-8"
        # )
        self.proc = pexpect.spawn("lake exe repl", cwd=path_to_repl, encoding="utf-8")

    def run_code(self, code, env=None, verbose=False):
        if env:
            command = json.dumps(dict(cmd=code, env=env))  # [1:-1] removes single quotes
        else:
            command = (
                '{ "cmd" : "' + repr(code)[1:-1] + '" }'
            )  # [1:-1] removes single quotes

        if verbose:
            print(" command :")
            pprint(command)
            lean_syntax = syntax_lean(code)
            console.print("input : ", lean_syntax)

        self.proc.sendline(command)
        self.proc.expect_exact(command + "\r\n")
        self.proc.sendline()
        self.proc.expect_exact("\r\n")
        try:
            index = self.proc.expect('env": \d+\}', timeout=20)
            output_str = self.proc.before + self.proc.match.group()
            output = json.loads(output_str)
            if verbose:
                print(" output_str :")
                pprint(output)
                data_collected = (
                    syntax_lean(e["data"]) for e in output.get("messages", ())
                )
                console.print("output data: ", *data_collected)
            return output
        except (pexpect.exceptions.EOF, pexpect.exceptions.TIMEOUT) as error:
            if verbose:
                print(error)
                ipdb.set_trace()
            raise error


if __name__ == "__main__":
    path_to_repl = "lean_repls/repl-4.5.0"
    path_to_repl = "lean_repls/repl-master"
    lean = LeanServer(path_to_repl)

    code1 = """
import Mathlib.Data.Nat.Prime

theorem test_thm (m n : Nat) (h : m.coprime n) : m.gcd n = 1 := by {}
"""
    state1 = lean.run_code(code1, verbose=True)

    header = """
import Mathlib.Data.Nat.Prime

"""
    theorem_statement = """theorem thm1 (a b c : Nat) : a + b = c → a ≤ c := by {}"""
    code2 = header + theorem_statement
    state2 = lean.run_code(code2, verbose=True)

    ipdb.set_trace()
