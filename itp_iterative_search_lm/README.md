Here we use [vllm](https://github.com/vllm-project/vllm).  
Quantized models in the format of GPTQ, AWQ, SqueezeLLM, FP8 KV Cache are supported,
but [not GGUF](https://github.com/vllm-project/vllm/issues/1002) as of v0.3.1 (2024-02-16).

Default configuration at `cnfgr/cnfgr.yaml`, and can be overridden via [hydra](https://github.com/facebookresearch/hydra) syntax.
Example use

```sh
python search_proof_lean.py llm.model=TheBloke/llemma_7b-AWQ llm.dtype=float16
```
