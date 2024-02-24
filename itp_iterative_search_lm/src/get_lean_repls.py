import os
import subprocess

parent_dir = "lean_repls"


def get_mathlib_commit_hash(version: str):
    default = "30e83bf01a2c9f78c6d85567e5546b35a571149f"
    mathlib4_commit_hash = {
        "4.3.0": "f04afed5ac9fea0e1355bc6f6bee2bd01f4a888d",
        "4.4.0-rc1": "75641abe702d35c946b6e59b8dc672c7e6d80b13",
        "4.4.0": "cf8e23a62939ed7cc530fbb68e83539730f32f86",
        "4.5.0": "feec58a7ee9185f92abddcf7631643b53181a7d3",
    }
    return mathlib4_commit_hash.get(version, default)


def run_lake_v(repl_dir: str, version: str):
    lakefilepath = os.path.join(repl_dir, "lakefile.lean")
    with open(lakefilepath, "a") as f:
        f.write(
            f'\n\nrequire mathlib from git\n  "https://github.com/leanprover-community/mathlib4.git" @ "{get_mathlib_commit_hash(version)}"\n'
        )

    subprocess.run(f"lake update".split(), cwd=repl_dir)
    subprocess.run(f"lake exe cache get".split(), cwd=repl_dir)
    subprocess.run(f"lake build".split(), cwd=repl_dir)


def get_repl_v(version: str, parent_dir: str = parent_dir) -> str:
    dirname = f"repl-{version}"
    repl_dir = os.path.join(parent_dir, dirname)
    if os.path.exists(repl_dir):
        return repl_dir

    tag = f"v{version}"
    archivename = f"{tag}.tar.gz"
    subprocess.run(
        f"wget https://github.com/leanprover-community/repl/archive/{archivename}".split(),
        cwd=parent_dir,
    )
    subprocess.run(f"tar -xzf {archivename}".split(), cwd=parent_dir)
    os.remove(os.path.join(parent_dir, archivename))
    run_lake_v(repl_dir, version=version)
    return repl_dir


def get_repl_commit_hash(commit_hash: str, parent_dir: str = parent_dir) -> str:
    dirname = f"repl-{commit_hash}"
    repl_dir = os.path.join(parent_dir, dirname)
    if os.path.exists(repl_dir):
        return repl_dir
    raise NotImplementedError  # TODO


def get_repl_master(parent_dir: str = parent_dir):

    subprocess.run(
        f"wget https://github.com/leanprover-community/repl/archive/refs/heads/master.zip".split(),
        cwd=parent_dir,
    )
    subprocess.run(f"unzip master.zip".split(), cwd=parent_dir)
    os.remove(os.path.join(parent_dir, "master.zip"))
    repl_dir = os.path.join(parent_dir, "repl-master")
    run_lake_v(repl_dir, version="master")


if __name__ == "__main__":
    os.makedirs(parent_dir, exist_ok=True)
    versions = ("4.3.0", "4.4.0-rc1", "4.4.0", "4.5.0")
    for version in versions:
        _ = get_repl_v(version)
