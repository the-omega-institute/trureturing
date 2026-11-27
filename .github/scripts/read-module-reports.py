"""Select published report rows and fetch replacement ZIPs from the published report shards."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from urllib.parse import quote


REPORT_TAG = re.compile(r"lean-modules-([0-9a-f]{40})-report")
REPORT_ASSET_TAG = re.compile(REPORT_TAG.pattern + r"(?:-part-([2-9]|[1-9][0-9]+))?")
PUBLICATION = "truth-release-publication.v1.json"
BUNDLE_FILES = {
    PUBLICATION, "release-manifest.v1.json", "source-snapshot.v1.json", "truth-graph.v1.json",
    "raw-lean-report.json", "truth-export.v1.json", "blueprint-index.v1.json", "SHA256SUMS",
}


def download(base, version, asset, destination, *, optional=False):
    url = f"{base}/{quote(version, safe='')}/{quote(asset, safe='')}"
    result = subprocess.run([
        "curl", "--fail", "--location", "--silent", "--show-error", "--retry", "3",
        "--output", destination, "--write-out", "%{http_code}", "--", url,
    ], stdout=subprocess.PIPE, text=True)
    if optional and result.returncode == 22 and result.stdout == "404":
        return False
    result.check_returncode()
    return True


def copy_reports(shard, members, destination):
    wanted = {}
    for name in members:
        filename = name + ".zip"
        if filename != Path(filename).name or "\\" in filename:
            raise ValueError(f"unsafe report filename: {filename!r}")
        wanted[f"lean-inspector/modules/{filename}"] = destination / filename

    copied = set()
    with tarfile.open(shard, "r|gz") as archive:
        for member in archive:
            if member.isfile() and (output := wanted.get(member.name)) is not None:
                with archive.extractfile(member) as source, output.open("xb") as report:
                    shutil.copyfileobj(source, report)
                copied.add(member.name)
    missing = wanted.keys() - copied
    if missing:
        raise ValueError(f"report shard is missing {min(missing)}")


def select_release(repository, source, *, retry=False):
    owner, name = repository.split("/")
    query = """
      query($owner: String!, $name: String!, $endCursor: String) {
        repository(owner: $owner, name: $name) {
          releases(first: 100, after: $endCursor) {
            nodes { tagName tagCommit { oid } publishedAt isPrerelease isDraft }
            pageInfo { hasNextPage endCursor }
          }
        }
      }"""
    raw = subprocess.check_output([
        "gh", "api", "graphql", "--paginate", "--slurp", "-f", "query=" + query,
        "-f", "owner=" + owner, "-f", "name=" + name,
    ])
    releases = sorted((r for page in json.loads(raw) for r in page["data"]["repository"]["releases"]["nodes"]
                       if not r["isDraft"] and not r["isPrerelease"]
                       and re.fullmatch(r"truth-release-[0-9a-f]{64}", r["tagName"])),
                      key=lambda r: r["publishedAt"], reverse=True)
    for release in releases:
        if release["tagCommit"]["oid"] == source:
            return None, release
    predecessor = None
    for release in releases:
        previous = release["tagCommit"]["oid"]
        status = subprocess.check_output([
            "gh", "api", f"repos/{repository}/compare/{previous}...{source}?per_page=1",
            "--jq", ".status",
        ], text=True).strip()
        if status == "behind":
            return None, release
        if status == "ahead" and predecessor is None:
            predecessor = release
            if not retry:
                break
        if status not in ("ahead", "diverged"):
            raise ValueError(f"unexpected commit comparison: {status}")
    return predecessor, None


def load_report_index(path, version):
    index = json.loads(path.read_bytes())
    tag = REPORT_TAG.fullmatch(version)
    if (not tag or index.get("schema") != "lean-module-shards-v1" or index.get("kind") != "report"
            or index.get("version") != version or index.get("source") != tag[1]
            or index.get("compiler_version") != version.removesuffix("-report")):
        raise ValueError(f"invalid published report index for {version}")
    members = set()
    targets = index["targets"]
    for owner, shard in index["shards"].items():
        asset = shard["asset"]
        if (not REPORT_ASSET_TAG.fullmatch(shard["version"]) or shard["artifact_kind"] != "report"
                or asset != shard["key"] or not asset.endswith("-report") or asset != Path(asset).name
                or "\\" in asset):
            raise ValueError(f"invalid report shard coordinate for {owner}")
        for name in shard["members"]:
            row = targets.get(name)
            if (not row or row["shard"] != owner or name in members or "report_inputs" not in row
                    or not re.fullmatch(r"[0-9a-f]{64}", row["key"])):
                raise ValueError(f"invalid report target {name} in shard {owner}")
            members.add(name)
    if members != targets.keys():
        raise ValueError("report index does not cover every target")
    return index


def copy_base_bundle(archive, destination):
    copied = set()
    with tarfile.open(archive, "r|gz") as contents:
        for member in contents:
            name = member.name.removeprefix("./")
            if name not in BUNDLE_FILES:
                continue
            if not member.isfile() or name in copied:
                raise ValueError(f"invalid Truth Release bundle member: {member.name}")
            with contents.extractfile(member) as source, (destination / name).open("xb") as output:
                shutil.copyfileobj(source, output)
            copied.add(name)
    return copied == BUNDLE_FILES


def compatible_report(path):
    # Use the exact envelope produced by the source checkout's Inspector.
    sys.path.insert(0, str(Path.cwd() / "tools/lean-inspector"))
    import materials

    empty = materials.canonical_json({"modules": [], "schema": materials.REPORT_SCHEMA})
    before, after = empty.split(b"[]", 1)
    prefix, suffix = before + b"[", b"]" + after
    with path.open("rb") as source:
        if source.read(len(prefix)) != prefix or source.seek(0, os.SEEK_END) < len(empty):
            return False
        source.seek(-len(suffix), os.SEEK_END)
        return source.read(len(suffix)) == suffix


def prepare_base(base, index, release, stage, destination):
    tag = release["tagName"]
    source = release["tagCommit"]["oid"]
    asset = stage / "previous"
    download(base, tag, PUBLICATION, asset)
    coordinate = json.loads(asset.read_bytes())
    if coordinate["source_commit"] != source or coordinate["release_digest"] != "sha256:" + tag.removeprefix("truth-release-"):
        raise ValueError(f"published coordinate differs from its release: {tag}")

    previous_version = "lean-modules-" + source + "-report"
    if not download(base, previous_version, "index.json", asset, optional=True):
        return set()
    previous = load_report_index(asset, previous_version)
    if previous["mathlib"] != index["mathlib"]:
        return set()
    old = previous["targets"]
    reusable = {name for name, row in index["targets"].items()
                if name in old and row["key"] == old[name]["key"]}

    download(base, tag, tag + ".tar.gz", asset)
    bundle = stage / "bundle"
    bundle.mkdir()
    if not copy_base_bundle(asset, bundle):
        return set()
    if json.loads((bundle / PUBLICATION).read_bytes()) != coordinate:
        raise ValueError("the baseline bundle has another publication coordinate")
    if not compatible_report(bundle / "raw-lean-report.json"):
        print("Using current module ZIPs for an incompatible predecessor report", flush=True)
        return set()
    (bundle / "reuse.json").write_text(json.dumps(sorted(reusable)) + "\n", encoding="utf-8")
    bundle.rename(destination)
    return reusable


def read_reports(base, version, destination, *, base_directory=None, previous=None):
    tag = REPORT_TAG.fullmatch(version)
    if not tag:
        raise ValueError(f"invalid report release: {version}")
    source = tag[1]
    if previous and previous["tagCommit"]["oid"] == source:
        print(f"Source {source} is published as {previous['tagName']}", flush=True)
        return previous["tagName"]

    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=base_directory.parent if base_directory is not None else None) as temporary:
        stage = Path(temporary)
        asset = stage / "asset"
        download(base, version, "index.json", asset)
        index = load_report_index(asset, version)
        reused = prepare_base(base, index, previous, stage, base_directory) if previous else set()
        needed = index["targets"].keys() - reused
        shards = 0
        for shard in index["shards"].values():
            members = needed.intersection(shard["members"])
            if members:
                download(base, shard["version"], shard["asset"], asset)
                with asset.open("rb") as stream:
                    if (asset.stat().st_size != shard["bytes"]
                            or hashlib.file_digest(stream, "sha256").hexdigest() != shard["sha256"]):
                        raise ValueError(f"report shard differs from the index: {shard['asset']}")
                copy_reports(asset, members, destination)
                shards += 1
        print(f"TRUTH_RELEASE_REPORTS reused={len(reused)} downloaded_shards={shards} release={version}", flush=True)
    return None


if __name__ == "__main__" and sys.argv[1:2] == ["select"]:
    parser = argparse.ArgumentParser(description="Select the published predecessor for a pinned source")
    parser.add_argument("source")
    parser.add_argument("selection", type=Path, nargs="?")
    args = parser.parse_args(sys.argv[2:])
    previous, covered = select_release(os.environ["GITHUB_REPOSITORY"], args.source,
                                       retry=os.environ.get("GITHUB_RUN_ATTEMPT", "1") != "1")
    if args.selection:
        args.selection.write_text(json.dumps(previous))
    if covered:
        print(f"Source {args.source} is covered by {covered['tagName']} at {covered['tagCommit']['oid']}", flush=True)
        with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
            print("existing=" + covered["tagName"], file=output)
elif __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="GitHub Releases download URL prefix")
    parser.add_argument("version", help="pinned lean-modules-<commit>-report tag")
    parser.add_argument("destination", type=Path, help="Inspector module report directory")
    parser.add_argument("--previous-bundle", type=Path, help="stage the prior Truth bundle and row selection here")
    parser.add_argument("--selection", type=Path, help="predecessor chosen for this source")
    args = parser.parse_args()
    read_reports(args.base, args.version, args.destination, base_directory=args.previous_bundle,
                 previous=json.loads(args.selection.read_bytes()) if args.selection else None)
