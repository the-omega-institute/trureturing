"""Select published report rows and fetch only ordinary shards containing their replacements."""

import argparse
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

    with tarfile.open(shard, "r|gz") as archive:
        for member in archive:
            if member.isfile() and (output := wanted.get(member.name)) is not None:
                with archive.extractfile(member) as source, output.open("xb") as report:
                    shutil.copyfileobj(source, report)


def select_release(repository, source):
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
            return release
    for release in releases:
        previous = release["tagCommit"]["oid"]
        ancestor = subprocess.check_output([
            "gh", "api", f"repos/{repository}/compare/{previous}...{source}?per_page=1",
            "--jq", ".merge_base_commit.sha",
        ], text=True).strip()
        if ancestor == previous:
            return release
    return None


def report_keys(index):
    # The producer's report key includes the effective compiler inputs and the report-only inputs.
    # Compiler-only siblings may have compiler_input but do not have report_inputs.
    return {name: row["key"] for name, row in index.get("targets", {}).items() if "report_inputs" in row}


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

    previous_version = "lean-modules-" + coordinate["source_commit"]
    if not download(base, previous_version, "index.json", asset, optional=True):
        return set()
    previous = json.loads(asset.read_bytes())
    if previous.get("schema") != index.get("schema") or previous.get("mathlib") != index.get("mathlib"):
        return set()
    old = report_keys(previous)
    reusable = {name for name, key in report_keys(index).items() if key and key == old.get(name)}
    if not old:
        return set()

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
    source = version.removeprefix("lean-modules-")
    if previous and previous["tagCommit"]["oid"] == source:
        print(f"Source {source} is published as {previous['tagName']}", flush=True)
        return previous["tagName"]

    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=base_directory.parent if base_directory is not None else None) as temporary:
        stage = Path(temporary)
        asset = stage / "asset"
        download(base, version, "index.json", asset)
        index = json.loads(asset.read_bytes())
        reused = prepare_base(base, index, previous, stage, base_directory) if previous else set()
        keys = report_keys(index)
        needed = set(keys) - reused
        shards = 0
        for shard in index["shards"].values():
            members = needed.intersection(shard["members"]) if keys else shard["members"]
            if members:
                download(base, shard["version"], shard["asset"], asset)
                copy_reports(asset, members, destination)
                shards += 1
        print(f"TRUTH_RELEASE_REPORTS reused={len(reused)} downloaded_shards={shards} release={version}", flush=True)
    return None


if __name__ == "__main__" and sys.argv[1:2] == ["select"]:
    parser = argparse.ArgumentParser(description="Select the published predecessor for a pinned source")
    parser.add_argument("source")
    parser.add_argument("selection", type=Path)
    args = parser.parse_args(sys.argv[2:])
    release = select_release(os.environ["GITHUB_REPOSITORY"], args.source)
    args.selection.write_text(json.dumps(release))
    if release and release["tagCommit"]["oid"] == args.source:
        print(f"Source {args.source} is published as {release['tagName']}", flush=True)
        with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
            print("existing=" + release["tagName"], file=output)
elif __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="GitHub Releases download URL prefix")
    parser.add_argument("version", help="pinned lean-modules-<commit> tag")
    parser.add_argument("destination", type=Path, help="Inspector module report directory")
    parser.add_argument("--previous-bundle", type=Path, help="stage the prior Truth bundle and row selection here")
    parser.add_argument("--selection", type=Path, help="predecessor chosen for this source")
    args = parser.parse_args()
    read_reports(args.base, args.version, args.destination, base_directory=args.previous_bundle,
                 previous=json.loads(args.selection.read_bytes()) if args.selection else None)
