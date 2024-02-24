from collections.abc import Callable, Iterable
from dataclasses import dataclass
from datetime import datetime
from functools import partial as prt
import heapq
import json
import os
from pathlib import Path
import re
import subprocess
import time
from operator import contains, eq

import ipdb

from rich.console import Console
from rich import print
import torch
from torch import Tensor
import transformers
from transformers import PreTrainedTokenizerFast
import vllm
from tqdm import tqdm, trange

console = Console()
os.environ["TOKENIZERS_PARALLELISM"] = "false"


def unique_sorted_descending(
    *args: Iterable,
    unique_key_id: int = 0,
    sort_key_id: int = -1,
) -> tuple[tuple]:
    row_based_table: list[Iterable] = []
    unique_collection: set = set()
    for row in sorted(zip(*args), key=lambda x: -x[sort_key_id]):
        if row[unique_key_id] not in unique_collection:
            row_based_table.append(row)
            unique_collection.add(row[unique_key_id])
    return tuple(zip(*map(tuple, row_based_table)))


def generate_vllm(
    model: vllm.LLM,
    prompt: str,
    stop: Iterable[str] | None,
    num_samples: int,
    temperatures: Iterable[float | int],
    max_tokens: int,
) -> tuple[tuple[str], tuple[float]]:
    tokenizer = model.get_tokenizer()
    texts, scores = [], []
    # temps = []
    for temperature in temperatures:
        params = vllm.SamplingParams(
            n=num_samples,
            temperature=temperature,
            use_beam_search=temperature == 0.0,
            max_tokens=max_tokens,
            stop=stop,
        )
        outputs = model.generate([prompt], sampling_params=params, use_tqdm=False)
        if len(outputs) == 0:
            continue
        for output in outputs[0].outputs:  # len(outputs) == 1
            text = output.text.replace(tokenizer.eos_token, "")
            score = output.cumulative_logprob / max(len(output.token_ids), 1)
            texts.append(text)
            scores.append(score)
            # temps.append(temperature)

    return unique_sorted_descending(texts, scores)


@dataclass(frozen=True)
class PromptFewshotGenerator:
    template: str
    stop: tuple[str]

    def __post_init__(self) -> None:
        assert isinstance(self.stop, (tuple, list)), "stop ought to be a tuple of str"
        object.__setattr__(self, "stop", tuple(self.stop))

    def __call__(self, ts: str) -> str:
        return self.template.format(ts)
