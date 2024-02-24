import json
import os.path as osp
from time import time

import ipdb
import hydra
from omegaconf import OmegaConf, DictConfig
from rich import print
from rich.pretty import pprint
from tqdm import tqdm
import vllm

from src.language_models import PromptFewshotGenerator
from src.lean import LanguageServers
from src.proofsearch import best_first_search
from src.utils import omegaconf_load_continaer


def main(cnfgr: DictConfig):
    data_dir = "data"
    download_dir_lms = osp.join(data_dir, "lms")
    theorems_to_prove = json.load(open("fixtures/lean_examples.json"))
    prompt_generator = PromptFewshotGenerator(**omegaconf_load_continaer(cnfgr.prompt))
    llm = vllm.LLM(
        **OmegaConf.to_container(cnfgr.llm),
        download_dir=download_dir_lms,
    )
    language_servers = LanguageServers(**OmegaConf.to_container(cnfgr.language_server))

    start = time()
    for iteration in tqdm(range(len(theorems_to_prove))):
        theorem = theorems_to_prove[iteration]
        results = best_first_search(
            language_servers,
            llm,
            theorem["header"],
            theorem["theorem_statement"],
            prompt_generator,
            **OmegaConf.to_container(cnfgr.search),
        )
        print("Attempted result :")
        pprint(results)
    end = time()
    print(f"Time taken total : {end - start:.2f} seconds")
    print(
        f"Time taken per example : {(end - start) / len(theorems_to_prove):.2f} seconds"
    )


hydrated_main = hydra.main(config_path="cnfgr", config_name="cnfgr.yaml")(main)
if __name__ == "__main__":
    hydrated_main()
