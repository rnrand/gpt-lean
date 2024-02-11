import os
from pathlib import Path

from dotenv import load_dotenv
from llama_cpp import Llama

load_dotenv()

_d = os.path.dirname
PROJECT_ROOT = Path(_d(_d(_d(__file__))))


def truncate(llama: Llama, input: str, maxlen: int) -> str:
    tokens = llama.tokenize(input.encode("utf-8"))
    return llama.detokenize(tokens[max(len(tokens) - maxlen, 0) :]).decode("utf-8")
