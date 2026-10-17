"""Picker fixtures; the canonical CLI query is a mocked boundary here."""
import csv
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def production(repository):
    with tempfile.TemporaryDirectory(prefix="production-dispatch-picker-") as temporary:
        root = Path(temporary)
        subprocess.run(["git", "init", "-q", str(root)], check=True, capture_output=True)
        scripts = root / "tools/scripts/agent"
        scripts.mkdir(parents=True)
        for name in ("prime_pick.sh", "default_dispatch_filter.py"):
            shutil.copyfile(repository / "tools/scripts/agent" / name, scripts / name)
        cli_dir = root / "tools/StrataLint.Cli/bin/Release/net10.0"
        shutil.copytree(repository / "tools/StrataLint.Cli/bin/Release/net10.0", cli_dir)
        cas = root / "Meta/Digestion/atoms/sha256"
        cas.mkdir(parents=True)
        ids = []
        sources = ("contextual-spacetime-arithmetic", "contextual-spacetime-arithmetic-ml", "ordered-simplex-l2-projection")
        for source in sources:
            text = f"## 定理 prime {source}\n" + "\n".join(
                f"$x_{i}$ 因为构造存在素数" for i in range(14)) + "\n"
            atom = hashlib.sha256(text.encode()).hexdigest()
            ids.append(atom)
            ledger = root / "Meta/Digestion/backfill" / source
            (ledger / "residual-open").mkdir(parents=True)
            (ledger / "residual-open" / f"{atom}.yaml").write_text("invalid: [")
            metadata = (repository / "Meta/Digestion/backfill" / source / "source.toml").read_bytes()
            if source == sources[2] and b'default_dispatch = "excluded"' not in metadata:
                metadata += b'default_dispatch = "excluded"\n'
            (ledger / "source.toml").write_bytes(metadata)
            (cas / atom).write_text(text)
        def run(*args):
            result = subprocess.run(args, cwd=root, capture_output=True, text=True)
            assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
            return result
        before = {str(path.relative_to(root)): path.read_bytes() for path in (root / "Meta").rglob("*") if path.is_file()}
        batch = ["dotnet", str(cli_dir / "StrataLint.dll"), "source-dispatch"]
        for source in sources[:2]:
            batch += ["--source", source]
        assert run(*batch).stdout.count("default=eligible") == 2
        fresh = root / "fresh.tsv"
        script = ["/bin/bash", str(scripts / "prime_pick.sh"), str(root)]
        assert "PRIME_PICK_OK ranked=2 scanned=3" in run(*script, str(fresh)).stdout
        with fresh.open() as stream:
            rows = list(csv.DictReader(stream, delimiter="\t"))
        assert {row["atom_id"] for row in rows} == set(ids[:2])
        assert "changed=2" in run(*batch, "--default", "excluded").stdout
        empty = root / "empty.tsv"
        assert "PRIME_PICK_OK ranked=0 scanned=3" in run(*script, str(empty)).stdout
        stale = root / "stale.tsv"
        assert "PRIME_PICK_OK ranked=0 scanned=2" in run(*script, str(stale), "--pool", str(fresh)).stdout
        assert "changed=0" in run(*batch, "--default", "excluded").stdout
        assert "changed=2" in run(*batch, "--default", "eligible").stdout
        after = {str(path.relative_to(root)): path.read_bytes() for path in (root / "Meta").rglob("*") if path.is_file()}
        assert before == after
        assert "PRIME_PICK_OK ranked=2 scanned=3" in run(*script, str(fresh)).stdout
    print("PRODUCTION_DISPATCH_PICKERS_OK")


def main():
    repository = Path(sys.argv[1])
    with tempfile.TemporaryDirectory(prefix="dispatch-picker-") as temporary:
        root = Path(temporary)
        scripts = root / "tools/scripts/agent"
        scripts.mkdir(parents=True)
        for name in ("prime_pick.sh", "pick_atom.sh", "default_dispatch_filter.py"):
            shutil.copyfile(repository / "tools/scripts/agent" / name, scripts / name)
        (root / ".git").mkdir()
        cli = root / "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
        cli.parent.mkdir(parents=True)
        cli.touch()
        cas = root / "Meta/Digestion/atoms/sha256"
        cas.mkdir(parents=True)
        ids = []
        for source in ("left", "right"):
            text = f"## 定理 prime {source}\n" + "\n".join(
                f"$x_{i}$ 因为构造存在素数" for i in range(14)) + "\n"
            atom = hashlib.sha256(text.encode()).hexdigest()
            ids.append(atom)
            ledger = root / "Meta/Digestion/backfill" / source
            (ledger / "residual-open").mkdir(parents=True)
            (ledger / "residual-open" / f"{atom}.yaml").write_text("invalid: [")
            (ledger / "source.toml").write_text(f'source_id = "{source}"\n')
            (cas / atom).write_text(text)
        bin_dir = root / "bin"
        bin_dir.mkdir()
        fake_dotnet = bin_dir / "dotnet"
        fake_dotnet.write_text("""#!/usr/bin/env python3
import pathlib, sys
root = pathlib.Path.cwd()
assert sys.argv[2:5] == ["search-atoms", "--selection", "default-dispatch"]
args = sys.argv[5:]
ids = [args[i + 1] for i, arg in enumerate(args) if arg == "--atom-id"]
for atom in ids:
    for path in sorted((root / "Meta/Digestion/backfill").glob("*/residual-open/" + atom + ".yaml")):
        source = path.parent.parent
        data = dict(line.split(" = ", 1) for line in (source / "source.toml").read_text().splitlines())
        if data.get("default_dispatch", '"eligible"') == '"eligible"':
            print(f"ATOM source_id={source.name} atom_id={atom} state=residual-open path={path.relative_to(root)}")
""")
        fake_dotnet.chmod(0o755)
        for name in ("git", "ps"):
            path = bin_dir / name
            path.write_text("#!/bin/sh\nexit 0\n")
            path.chmod(0o755)
        env = dict(os.environ, PATH=str(bin_dir) + os.pathsep + os.environ["PATH"])
        def run(name, *args, success=True):
            result = subprocess.run(["/bin/bash", str(scripts / name), str(root), *map(str, args)],
                                    cwd=root, env=env, capture_output=True, text=True)
            assert (result.returncode == 0) == success, (name, result.returncode, result.stdout, result.stderr)
            return result
        def rows(path):
            with path.open() as stream:
                return list(csv.DictReader(stream, delimiter="\t"))
        old = root / "old.tsv"
        run("prime_pick.sh", old)
        assert {row["atom_id"] for row in rows(old)} == set(ids)
        pick_pool = root / "pick.tsv"
        pick_pool.write_text("".join(f"CLEAN\t{100 - i}\t80\t{atom}\tprime fixture\n" for i, atom in enumerate(ids)))
        opted = root / "Meta/Digestion/backfill/left/source.toml"
        opted.write_text(opted.read_text() + 'default_dispatch = "excluded"\n')
        fresh = root / "fresh.tsv"
        stale = root / "stale.tsv"
        run("prime_pick.sh", fresh)
        run("prime_pick.sh", stale, "--pool", old)
        assert [row["atom_id"] for row in rows(fresh)] == [ids[1]]
        assert [row["atom_id"] for row in rows(stale)] == [ids[1]]
        emitted = run("pick_atom.sh", pick_pool, "2")
        assert ids[1] in emitted.stdout and ids[0] not in emitted.stdout
        opted.write_text('source_id = "left"\n')
        restored = root / "restored.tsv"
        run("prime_pick.sh", restored, "--pool", old)
        assert {row["atom_id"] for row in rows(restored)} == set(ids)
        assert all(atom in run("pick_atom.sh", pick_pool, "2").stdout for atom in ids)
        fake_dotnet.write_text("#!/bin/sh\nexit 2\n")
        failure = run("pick_atom.sh", pick_pool, "2", success=False)
        assert not failure.stdout
    print("DEFAULT_DISPATCH_PICKERS_OK")


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[2] == "--production":
        production(Path(sys.argv[1]))
    else:
        main()
