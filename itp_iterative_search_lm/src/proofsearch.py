# Lean proof search with LeanDojo interaction
# Adapted by Chih-chan Tien from Sean Welleck https://github.com/wellecks/llemma_formal2formal

from collections.abc import Callable, Iterable
import concurrent
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from datetime import datetime
from functools import partial as prt
import logging
import heapq
import json
import os
import time

import ipdb

from rich.console import Console
from rich import print
from rich.pretty import pprint
import torch
import transformers
from transformers import PreTrainedTokenizerFast
import vllm
from tqdm import tqdm

from src.lean import LeanServer, LanguageServers
from src.lean import syntax_lean as syntax
from src.language_models import PromptFewshotGenerator, generate_vllm

console = Console()
assert logging.DEBUG == 10
assert logging.INFO == 20


def repr_proof(proof: Iterable[str]) -> str:
    code = format_code


def get_goal(state: dict) -> str | None:
    goal = None
    # TODO : Not geting messages when complete (strange)
    for msg in state.get("messages", []):
        if msg["data"].startswith("unsolved goals\n"):
            goal = "\n".join(msg["data"].split("\n")[1:])
        elif msg["severity"] == "error":
            return None
    return goal


def is_done(state):
    sorries = state.get("sorries", [])  # TODO : Somehow I am not getting sorries
    messages = state.get("messages", [])  # TODO : Not geting messages when complete
    return sorries == [] and messages == []


def _run_code(code: str, langauge_server: LeanServer, verbosity: int):
    return langauge_server.run_code(code, verbose=verbosity <= 10)


def format_code(header: str, statement: str, steps: Iterable[str]) -> str:
    return header + (statement.replace(" {}", "") + "\n" + "\n".join(steps))


def _print_current(theorem_statement, steps):
    print(
        "--- current:\n\t%s\n\t%s"
        % (theorem_statement.replace("{}", ""), "\n\t".join(steps))
    )


def _print_type_checked_candidates(results):
    print(
        "--- type-checked candidates:\n\t"
        + "\n\t".join(
            "(%.3f) %s" % (step_score, step)
            for state, step, step_score in results
            if (get_goal(state) is not None or is_done(state))
        )
    )


def best_first_search(
    language_servers: LanguageServers,
    model: vllm.LLM,
    header: str,
    statement: str,
    prompt_fn: PromptFewshotGenerator,
    max_iters: int,
    temperatures: Iterable[float | int],
    num_samples: int,
    timeout: int = 600,
    max_tokens: int = 256,
    verbosity: int = 20,
) -> dict:
    run_code: Callable[[str], dict] = prt(
        _run_code, langauge_server=language_servers[0], verbosity=verbosity
    )
    goal = get_goal(run_code(header + statement))
    if goal is None:
        return {
            "theorem_statement": statement,
            "success": False,
            "msg": run_code(header + statement),
        }

    attempt_results: list[dict] = []
    start_time = time.time()
    proof_finished = False
    queue = [(0.0, (), goal)]  # Score, steps-so-far, goal state
    visited = set()
    for iteration in tqdm(range((max_iters))):
        if len(queue) == 0 or proof_finished:
            break

        # Dequeue the tuple with minimum score
        score, steps, goal = heapq.heappop(queue)
        visited.add(goal)
        if verbosity <= 10:
            _print_current(statement, steps)
        # Generate next-step candidates
        if verbosity <= 9:
            print(f"Generating with prompt: {prompt_fn(goal)}")
        step_cands, step_scores = generate_vllm(
            model, prompt_fn(goal), prompt_fn.stop, num_samples, temperatures, max_tokens
        )
        step_cands = tuple(s.strip() for s in step_cands)
        if verbosity <= 10:
            print(
                "--- generated candidates:\n\t"
                + "\n\t".join(
                    f"({step_score:.4f}) {step}"
                    for step, step_score in zip(step_cands, step_scores)
                )
            )
        # # Run type checking in parallel via futures.
        # with ThreadPoolExecutor(max_workers=16) as executor:
        #     # We need to save the step and score associated to each future.
        #     future2step = {}
        #     for step, step_score in zip(step_cands, step_scores):
        #         code = format_code(header, statement, steps + (step,))
        #         future = executor.submit(run_code, **dict(code=code))
        #         future2step[future] = (step, step_score)

        #     # Collect the type checking results as they complete.
        #     results = []
        #     for future in tqdm(
        #         concurrent.futures.as_completed(future2step.keys()),
        #         total=len(future2step),
        #     ):
        #         result = future.result()
        #         results.append((result, *future2step[future]))

        # TODO: parallelize this
        results = []
        for step, step_score in zip(step_cands, step_scores):
            code = format_code(header, statement, steps + (step,))
            result = run_code(code)
            results.append((result, step, step_score))

        if verbosity <= 10:
            _print_type_checked_candidates(results)
        for state, step, step_score in results:
            if is_done(state):
                attempt_results.append(
                    {
                        "header": header,
                        "theorem_statement": statement,
                        "proof": steps + (step,),
                        "state": state,
                        "score": score - step_score,
                        "success": True,
                    }
                )
                proof_finished = True
                break

            goal_cand = get_goal(state)
            # Add new candidates to the queue.
            if goal_cand is not None and goal_cand not in visited:
                # Score is normalized negative log probability summed across steps
                new_score = score - step_score
                heapq.heappush(queue, (new_score, steps + (step,), goal_cand))

    if proof_finished:
        codes = (format_code(header, statement, rs["proof"]) for rs in attempt_results)
        for code in codes:
            pprint("Proof found :")
            console.print(syntax(code))
        return tuple(attempt_results)
    return ({"header": header, "theorem_statement": statement, "success": False},)
