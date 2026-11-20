"""Run the pinned FILEMAP checker against the current checkout."""

import hashlib
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[2]
VERSION = "v0.1.0-dev.1"
SHA256 = "93d31431dd2abe01eaa8513a75520c063908981b090163e207130bcff5f55378"
ASSET = "trureturing-tools.tar.gz"
CACHE = ROOT / "build/tools-releases"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def cached_archive():
    cache_path = CACHE / (SHA256 + ".tar.gz")
    if cache_path.is_file() and digest(cache_path) == SHA256:
        return cache_path
    url = f"https://github.com/the-omega-institute/trureturing-tools/releases/download/{VERSION}/{ASSET}"
    with tempfile.TemporaryDirectory(dir=CACHE) as temporary:
        download = Path(temporary) / ASSET
        with urlopen(url, timeout=60) as source, download.open("wb") as target:
            shutil.copyfileobj(source, target)
        if digest(download) != SHA256:
            raise ValueError(f"SHA-256 mismatch for tools {VERSION}")
        download.replace(cache_path)
    return cache_path


def main():
    CACHE.mkdir(parents=True, exist_ok=True)
    archive = cached_archive()
    with tempfile.TemporaryDirectory(dir=CACHE, prefix=SHA256 + "-") as directory:
        with tarfile.open(archive, "r:gz") as package:
            for member in package:
                parts = member.name.split("/")
                if (parts[0] != "tools" or any(part in {"", ".", "..", ".git"} for part in parts)
                        or not (member.isdir() or member.isfile())):
                    raise ValueError(f"unexpected tools archive entry {member.name!r}")
                package.extract(member, directory, filter="data")
        tools = Path(directory) / "tools"
        print(f"FILEMAP tools {VERSION} sha256={SHA256}", flush=True)
        return subprocess.run(["make", "-C", tools, "filemap-conform",
                               f"REPOSITORY={ROOT}", "CI_DOTNET_PREPARED=0"]).returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, tarfile.TarError) as exc:
        sys.exit(f"filemap release: {exc}")
