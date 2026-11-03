"""Private GitHub executable fixture used by release transport tests."""

FAKE_GH = '''#!/usr/bin/env python3
import hashlib, json, os, pathlib, shutil, sys
args = sys.argv[1:]
root = pathlib.Path(os.environ["FAKE_REMOTE"])
if "FAKE_GH_LOG" in os.environ:
    with pathlib.Path(os.environ["FAKE_GH_LOG"]).open("a") as log:
        log.write(json.dumps(args) + "\\n")
verb = args[0] if args and args[0] == "api" else (args[1] if len(args) > 1 else "")
if os.environ.get("FAKE_HANG") == verb:
    import signal
    signal.pause()
def fail():
    sys.stderr.write(os.environ.get("FAKE_FAIL_STDERR", ""))
    sys.exit(23)
if len(args) > 1 and os.environ.get("FAKE_FAIL") == verb and verb != "upload": fail()
if args[:2] == ["release", "list"] and "FAKE_LIST_JSON" in os.environ:
    print(os.environ["FAKE_LIST_JSON"]); sys.exit(0)
if args[0] == "api" and args[1].endswith("/branches/dev"):
    print(os.environ["FAKE_DEV_BRANCH"]); sys.exit(0)
if args[0] == "api" and "/compare/" in args[1] and "FAKE_VERIFICATION_API" not in os.environ:
    print(os.environ["FAKE_DEV_COMPARE"]); sys.exit(0)
if args[0] == "api" and "FAKE_API_JSON" in os.environ:
    print(os.environ["FAKE_API_JSON"]); sys.exit(0)
if args[0] == "api" and "FAKE_VERIFICATION_API" in os.environ:
    responses = json.loads(pathlib.Path(os.environ["FAKE_VERIFICATION_API"]).read_text())
    if args[1] in responses:
        print(json.dumps(responses[args[1]])); sys.exit(0)
def option(name): return args[args.index(name)+1]
def metadata(directory):
    value = json.loads((directory / "release.json").read_text())
    value["assets"] = [{"name": p.name, "size": p.stat().st_size, "digest": "sha256:" + hashlib.sha256(p.read_bytes()).hexdigest()}
                       for p in directory.iterdir() if p.name != "release.json"]
    if "FAKE_MANIFEST_DIGEST" in os.environ:
        for asset in value["assets"]:
            if asset["name"] == "manifest.json": asset["digest"] = os.environ["FAKE_MANIFEST_DIGEST"]
    if "FAKE_PART_ASSET" in os.environ:
        for asset in value["assets"]:
            if asset["name"].startswith("lean-build.tgz"):
                asset.update(json.loads(os.environ["FAKE_PART_ASSET"]))
    return value
if args[:2] == ["release", "list"]:
    print(json.dumps([{"tagName": p.parent.name, "createdAt": p.parent.name, "isDraft": json.loads(p.read_text())["draft"]}
                      for p in root.glob("*/release.json")]))
elif args[0] == "api":
    directory = root / args[1].split("/")[-1]
    phase = "FAKE_POST_EDIT_API" if (root.parent / ("gh-edited-" + str(os.getppid()))).exists() else "FAKE_LOOKUP_API"
    if phase + "_JSON" in os.environ:
        print(os.environ[phase + "_JSON"])
        sys.stderr.write(os.environ.get(phase + "_STDERR", ""))
        sys.exit(int(os.environ.get(phase + "_EXIT", "0")))
    if not directory.exists():
        print(json.dumps({"message": "Not Found", "status": "404"}))
        sys.exit(1)
    print(json.dumps(metadata(directory)))
else:
    verb, tag = args[1:3]
    directory = root / tag
    if verb == "create":
        directory.mkdir()
        (directory / "release.json").write_text(json.dumps({"tag_name": tag, "target_commitish": option("--target") if "--target" in args else "a" * 40, "draft": True}))
    elif verb == "upload":
        for value in args[3:]:
            if pathlib.Path(value).is_file(): shutil.copyfile(value, directory / pathlib.Path(value).name)
        if os.environ.get("FAKE_FAIL") == "upload": fail()
    elif verb == "edit":
        value = json.loads((directory / "release.json").read_text()); value["draft"] = False
        (directory / "release.json").write_text(json.dumps(value))
        (root.parent / ("gh-edited-" + str(os.getppid()))).touch()
        if "FAKE_MANIFEST_AFTER_EDIT" in os.environ:
            manifest = json.loads((directory / "manifest.json").read_text())
            manifest.update(json.loads(os.environ["FAKE_MANIFEST_AFTER_EDIT"]))
            (directory / "manifest.json").write_text(json.dumps(manifest))
        if os.environ.get("FAKE_DAMAGE_AFTER_EDIT") == "1":
            (directory / "lean-build.tgz").write_bytes(b"damaged after upload")
        if os.environ.get("FAKE_TRUNCATE_AFTER_EDIT") == "1":
            archive = directory / "lean-build.tgz"
            packed = archive.read_bytes()[:-8]; archive.write_bytes(packed)
            manifest = json.loads((directory / "manifest.json").read_text())
            digest = hashlib.sha256(packed).hexdigest()
            manifest.update(archive_bytes=len(packed), archive_sha256=digest,
                parts=[{"name": archive.name, "bytes": len(packed), "sha256": digest}])
            (directory / "manifest.json").write_text(json.dumps(manifest))
    elif verb == "download":
        destination = pathlib.Path(option("--dir")); destination.mkdir(exist_ok=True)
        if not directory.exists():
            sys.exit(0)
        patterns = [args[i + 1] for i, value in enumerate(args) if value == "--pattern" and i + 1 < len(args)]
        for path in directory.iterdir():
            if path.name != "release.json" and (not patterns or path.name in patterns):
                shutil.copyfile(path, destination / path.name)
    elif verb == "view":
        if not directory.exists(): sys.exit(1)
        print(json.dumps(metadata(directory)))
    elif verb == "delete": shutil.rmtree(directory)
    else: sys.exit(2)
'''
