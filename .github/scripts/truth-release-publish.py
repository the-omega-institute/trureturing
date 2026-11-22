"""Package verified truth artifacts and publish their immutable GHCR and GitHub copies."""

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile


REPO = "the-omega-institute/trureturing"
REGISTRY = f"ghcr.io/{REPO}/truth-release"
ARTIFACT_TYPE = "application/vnd.theomega.truth-release.bundle.v1"
LAYER_TYPE = ARTIFACT_TYPE + "+tar+gzip"
PUBLICATION = "truth-release-publication.v1.json"
ARTIFACTS = ("blueprint-index.v1.json", "raw-lean-report.json", "source-snapshot.v1.json",
             "truth-export.v1.json", "truth-graph.v1.json")
BUNDLE = (*ARTIFACTS, "SHA256SUMS", "release-manifest.v1.json", PUBLICATION)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def output(**values):
    with Path(os.environ["GITHUB_OUTPUT"]).open("a", encoding="utf-8") as target:
        for name, value in values.items():
            print(f"{name}={value}", file=target)


def publication(directory, digest, commit):
    coordinate = json.loads((directory / PUBLICATION).read_bytes())
    require(coordinate["schema"] == "truth-release-publication.v1"
            and coordinate["release_digest"] == coordinate["bundle_ref"] == digest
            and coordinate["source_commit"] == commit, "publication coordinate mismatch")


def prepare(bundle, dag, assets, commit):
    require(set(p.name for p in bundle.iterdir()) == set(BUNDLE)
            and all(p.is_file() and not p.is_symlink() for p in bundle.iterdir()),
            "unexpected bundle members")
    sums = bundle / "SHA256SUMS"
    expected = "".join(f"{sha(bundle / name)}  {name}\n" for name in sorted(ARTIFACTS))
    require(sums.read_bytes() == expected.encode(), "invalid bundle checksums")
    digest = "sha256:" + sha(sums)
    publication(bundle, digest, commit)
    snapshot = json.loads((bundle / "source-snapshot.v1.json").read_bytes())
    dag_hash = sha(dag)
    require(snapshot["source_repo"] == REPO and snapshot["source_commit"] == commit
            and snapshot["dag_md_sha256"] == "sha256:" + dag_hash, "DAG or source mismatch")

    assets.mkdir(parents=True, exist_ok=True)
    archive = assets / f"truth-release-{digest[7:]}.tar.gz"
    # Fix all transport metadata so rebuilding the same bundle reproduces the asset.
    with archive.open("wb") as raw, gzip.GzipFile(
        filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=6
    ) as compressed, tarfile.open(mode="w|", fileobj=compressed) as contents:
        for name in sorted(BUNDLE):
            path = bundle / name
            info = tarfile.TarInfo("./" + name)
            info.size = path.stat().st_size
            with path.open("rb") as source:
                contents.addfile(info, source)
    shutil.copyfile(bundle / PUBLICATION, assets / PUBLICATION)
    shutil.copyfile(dag, assets / "DAG.md")
    output(release_digest=digest, archive_sha256=sha(archive), dag_sha256=dag_hash,
           publication_sha256=sha(assets / PUBLICATION))


def query(*args, missing=None):
    result = subprocess.run(args, capture_output=True, text=True)
    if result.returncode:
        if missing and re.search(missing, result.stderr, flags=re.I):
            return None
        raise ValueError(f"{args[0]} {args[1]} failed: {result.stderr.strip()}")
    return json.loads(result.stdout)


def protected_source(commit):
    branch = query("gh", "api", f"repos/{REPO}/branches/dev")
    require(branch["protected"], "dev is unprotected")
    tip = branch["commit"]["sha"]
    if tip != commit:
        comparison = query("gh", "api", f"repos/{REPO}/compare/{commit}...{tip}?per_page=1")
        require(comparison["merge_base_commit"]["sha"] == commit, "source has left protected dev")


def oci(archive, digest, commit):
    tag = f"{REGISTRY}:release-{digest[7:]}"
    annotations = {
        "org.opencontainers.image.source": f"https://github.com/{REPO}/commit/{commit}",
        "org.opencontainers.image.revision": commit,
        "org.theomega.truth-release.release-digest": digest,
    }
    describe = ("oras", "manifest", "fetch", "--descriptor", tag)
    descriptor = query(*describe, missing=r"MANIFEST_UNKNOWN|manifest unknown|: not found\s*$")
    if descriptor is None:
        flags = [flag for key, value in annotations.items() for flag in ("--annotation", f"{key}={value}")]
        subprocess.run(["oras", "push", tag, "--artifact-type", ARTIFACT_TYPE, *flags,
                        f"{archive.name}:{LAYER_TYPE}"], cwd=archive.parent, check=True)
        descriptor = query(*describe)
    manifest_digest = descriptor["digest"]
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", manifest_digest), "invalid OCI digest")
    reference = f"{REGISTRY}@{manifest_digest}"
    manifest = query("oras", "manifest", "fetch", reference)
    layers = manifest["layers"]
    require(manifest["schemaVersion"] == 2 and manifest["artifactType"] == ARTIFACT_TYPE
            and all(manifest["annotations"].get(k) == v for k, v in annotations.items())
            and len(layers) == 1 and layers[0]["mediaType"] == LAYER_TYPE
            and layers[0]["digest"] == "sha256:" + os.environ["ARCHIVE_SHA256"]
            and layers[0]["size"] == archive.stat().st_size
            and layers[0]["annotations"]["org.opencontainers.image.title"] == archive.name,
            "OCI manifest does not bind the expected archive")
    require(query(*describe)["digest"] == manifest_digest, "OCI tag moved")
    output(reference=reference, digest=manifest_digest)


def mirror(assets, hashes, digest, commit, reference):
    require(re.fullmatch(re.escape(REGISTRY) + r"@sha256:[0-9a-f]{64}", reference),
            "unexpected attested OCI reference")
    tag = f"truth-release-{digest[7:]}"
    ref = ("gh", "api", f"repos/{REPO}/git/ref/tags/{tag}")
    binding = {"type": "commit", "sha": commit}
    existing = query(*ref, missing=r"\(HTTP 404\)")
    if existing is not None:
        require(binding.items() <= existing["object"].items(), "existing tag names another source")

    view = ("gh", "release", "view", tag, "--repo", REPO, "--json",
            "tagName,targetCommitish,isDraft,isPrerelease,assets")
    release = query(*view, missing=r"^release not found\s*$")
    if release is None:
        subprocess.run(["gh", "release", "create", tag, "--repo", REPO, "--draft",
                        "--target", commit, "--title", f"Truth release {digest[7:]}",
                        "--notes", f"DAG and verified truth bundle for {commit}. OCI: {reference}."],
                       check=True)
        release = query(*view)
    require(release["tagName"] == tag and release["targetCommitish"] == commit
            and not release["isPrerelease"], "release identity mismatch")
    expected = {name: "sha256:" + value for name, value in hashes.items()}
    uploaded = {}
    for asset in release["assets"]:
        name = asset["name"]
        require(name in expected and name not in uploaded, f"unexpected release asset: {name}")
        if release["isDraft"] and asset["state"] == "starter":
            # GitHub can leave an empty starter asset after an interrupted upload.
            subprocess.run(["gh", "release", "delete-asset", tag, name, "--repo", REPO, "--yes"],
                           check=True)
            continue
        require(asset["state"] == "uploaded" and asset["digest"] == expected[name],
                f"published bytes differ: {name}")
        uploaded[name] = asset["digest"]
    if release["isDraft"]:
        missing = [assets / name for name in expected if name not in uploaded]
        if missing:
            subprocess.run(["gh", "release", "upload", tag, *missing, "--repo", REPO], check=True)
        require(release_hashes(query(*view)) == expected, "draft asset set or digest mismatch")
        subprocess.run(["gh", "release", "edit", tag, "--repo", REPO, "--draft=false",
                        "--latest=false"], check=True)
    final = query(*view)
    require(not final["isDraft"] and release_hashes(final) == expected
            and binding.items() <= query(*ref)["object"].items(), "published release verification failed")
    print(f"GitHub Release {tag} verified for {commit}")


def release_hashes(release):
    hashes = {}
    for asset in release["assets"]:
        name = asset["name"]
        require(asset["state"] == "uploaded" and name not in hashes, f"incomplete or duplicate asset: {name}")
        hashes[name] = asset["digest"]
    return hashes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    pack = commands.add_parser("prepare")
    pack.add_argument("bundle", type=Path)
    pack.add_argument("dag", type=Path)
    for command in (pack, commands.add_parser("oci"), commands.add_parser("mirror")):
        command.add_argument("assets", type=Path)
    commands.choices["mirror"].add_argument("reference")
    args = parser.parse_args()
    commit = os.environ.get("SOURCE_COMMIT") or os.environ["GITHUB_SHA"]
    require(re.fullmatch(r"[0-9a-f]{40}", commit) and os.environ["GITHUB_REPOSITORY"] == REPO,
            "unexpected publication source")
    if args.command == "prepare":
        prepare(args.bundle, args.dag, args.assets, commit)
        return
    digest = os.environ["RELEASE_DIGEST"]
    require(re.fullmatch(r"sha256:[0-9a-f]{64}", digest), "invalid release digest")
    archive = args.assets / f"truth-release-{digest[7:]}.tar.gz"
    hashes = {archive.name: os.environ["ARCHIVE_SHA256"], "DAG.md": os.environ["DAG_SHA256"],
              PUBLICATION: os.environ["PUBLICATION_SHA256"]}
    for name, expected in hashes.items():
        require(sha(args.assets / name) == expected, f"transfer checksum mismatch: {name}")
    publication(args.assets, digest, commit)
    protected_source(commit)
    if args.command == "oci":
        oci(archive, digest, commit)
    else:
        mirror(args.assets, hashes, digest, commit, args.reference)


if __name__ == "__main__":
    main()
