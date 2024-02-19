from toolz import compose as cmp

from omegaconf import OmegaConf, DictConfig

omegaconf_load_continaer = cmp(OmegaConf.to_container, OmegaConf.load)
