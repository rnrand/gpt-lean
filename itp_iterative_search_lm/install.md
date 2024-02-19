## Lean 4

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake
```

## Python env

```sh
conda remove -y -n itp_lm --all
conda create -y --name itp_lm python=3.11  # vllm does not support python 3.12 as of v0.3.1 (2024-02-16)
conda activate itp_lm

conda install pytorch=2.1.2 torchvision torchaudio pytorch-cuda=12.1 -c pytorch -c nvidia  # vllm does not support torch=2.2 as of v0.3.1 (2024-02-16)
# conda install -y pytorch=2.1.2 torchvision torchaudio cpuonly -c pytorch  # cpu only

pip install -r requirements.txt

```

## llemma_formal2formal

```sh
wget https://raw.githubusercontent.com/wellecks/llemma_formal2formal/master/data/minif2f.jsonl -P data/
```

<!-- ## Lean repl

Adapted from [Welleck's](https://github.com/wellecks/ntptutorial/blob/main/partI_nextstep/README.md).

```sh
git submodule add git@github.com:cctien/lean_repl.git externals/lean_repl
git submodule update --init --recursive
cd externals/lean_repl
git checkout 172f69a72ca4506df50cef302aa3c481d3eb4624  # Parent being bddf452 on 18 Jun 2023
conda activate itp_lm
pip install -e pylean
cd ../..
``` -->

v0.3.1
