"""Copy report ZIPs from a pinned ordinary module Release."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
from urllib.parse import quote


def download(base, version, asset, destination):
    url = f"{base}/{quote(version, safe='')}/{quote(asset, safe='')}"
    subprocess.run([
        "curl", "--fail", "--location", "--silent", "--show-error", "--retry", "3",
        "--output", destination, "--", url,
    ], check=True)


def copy_reports(shard, members, destination):
    wanted = {}
    for name in members:
        filename = name + ".zip"
        if filename != Path(filename).name or "\\" in filename:
            raise ValueError(f"unsafe report filename: {filename!r}")
        wanted[f"lean-inspector/modules/{filename}"] = destination / filename

    with tarfile.open(shard, "r|gz") as archive:
        for member in archive:
            if member.isfile() and (output := wanted.get(member.name)) is not None:
                with archive.extractfile(member) as source, output.open("xb") as report:
                    shutil.copyfileobj(source, report)


def read_reports(base, version, destination):
    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as stage:
        asset = Path(stage) / "asset"
        download(base, version, "index.json", asset)
        with asset.open("rb") as stream:
            index = json.load(stream)
        for shard in index["shards"].values():
            download(base, shard["version"], shard["asset"], asset)
            copy_reports(asset, shard["members"], destination)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="GitHub Releases download URL prefix")
    parser.add_argument("version", help="pinned lean-modules-<commit> tag")
    parser.add_argument("destination", type=Path, help="Inspector module report directory")
    args = parser.parse_args()
    read_reports(args.base, args.version, args.destination)
