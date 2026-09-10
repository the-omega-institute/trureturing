#!/usr/bin/env python3
"""Complete the run-local source sibling using consumer demand and current Lean.

Old package bytes are immutable source inputs. Only the current compiler and current
package artifacts execute; old declaration/expansion/initializer bodies never do.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request

SCHEMA = "lean-source-context/1"


class SourceAnalysisUnknown(RuntimeError):
    """Located source data could not establish the demanded registration fact."""


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


class Preparation:
    def __init__(self, repository, report, base, scratch, lake):
        self.repository, self.report, self.base = repository, report, base
        self.scratch, self.lake = scratch, lake
        self.producer = repository / "tools/lean-inspector/SourceContext.lean"
        self.cli = repository / "tools/StrataLint.Cli/StrataLint.Cli.csproj"
        self.queries = self.interfaces = self.external_bytes = self.external_queries = 0
        self.query_requests = self.consumer_requests = 0
        self.query_cache = {}
        self.source_cache = {}
        self.options_cache = {}
        self.option_queries = 0
        self.compiler_queries = {}
        self.started = time.monotonic()

    def demands(self, context):
        result = subprocess.run(["dotnet", "run", "--project", str(self.cli), "--configuration", "Release",
            "--no-build", "--no-restore", "--no-launch-profile", "--", "lean-source-input", "--base", self.base,
            "--report", str(self.report), "--context", str(context)], cwd=self.repository,
            text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return json.loads(result.stdout)["requests"]

    def query(self, request):
        encoded = json.dumps(request, sort_keys=True, separators=(",", ":")).encode()
        key = digest(encoded)
        if key in self.query_cache:
            return self.query_cache[key]
        request_file = self.scratch / (key + ".json")
        request_file.write_bytes(encoded)
        directory = self.scratch / key
        directory.mkdir()
        command, environment = self.compiler_query(self.producer)
        result = subprocess.run(command + [str(request_file), str(directory)],
            cwd=self.repository, env=environment, text=True, capture_output=True)
        self.queries += 1
        self.query_requests += len(request) if isinstance(request, list) else 1
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        value = json.loads(result.stdout)
        for row in value if isinstance(value, list) else [value]:
            self.interfaces += row.get("queryModules", 0)
        self.query_cache[key] = value
        return value

    def compiler_query(self, source):
        # Compile this run's current producer once. The driver only imports that
        # exact module; no old compiler or protected declaration is compiled.
        key = (str(source), digest(source.read_bytes()))
        if key not in self.compiler_queries:
            directory = self.scratch / (source.stem + "-compiler")
            directory.mkdir()
            compiled = subprocess.run([self.lake, "env", "lean", "-R", str(source.parent),
                "-o", str(directory / (source.stem + ".olean")), str(source)],
                cwd=self.repository, text=True, capture_output=True)
            if compiled.returncode:
                raise RuntimeError(compiled.stdout + compiled.stderr)
            driver = directory / "Run.lean"
            driver.write_text("import " + source.stem + "\n")
            environment = dict(os.environ)
            environment["LEAN_PATH"] = str(directory) + os.pathsep + environment.get("LEAN_PATH", "")
            command = [self.lake, "env", "lean"]
            if source.stem == "SourceOptions":
                # Lake owns its installation path. Load its native config helper
                # before importing Lake, as Lake's own setup-file does.
                plugin = subprocess.run(command + ["--run", str(driver), "--plugin-path"],
                    cwd=self.repository, env=environment, text=True, capture_output=True, check=True)
                command.append("--plugin=" + plugin.stdout.strip())
            self.compiler_queries[key] = (command + ["--run", str(driver)], environment)
        return self.compiler_queries[key]

    def current_options(self, module):
        if module not in self.options_cache:
            command, environment = self.compiler_query(self.repository / "tools/lean-inspector/SourceOptions.lean")
            result = subprocess.run(command + [str(self.repository), module],
                cwd=self.repository, env=environment, text=True, capture_output=True)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)
            value = json.loads(result.stdout)
            options = value["options"]
            flags = iter(value["flags"])
            for flag in flags:
                if flag == "-D":
                    flag += next(flags)
                if not flag.startswith("-D"):
                    continue
                name, raw = flag[2:].split("=", 1)
                # Lean's CLI option values have exactly these scalar forms.
                options[name] = (raw == "true") if raw in ("true", "false") else (
                    int(raw) if raw.isdecimal() else raw.strip('"'))
            self.options_cache[module] = [dict(name=name, value=value) for name, value in options.items()]
            self.option_queries += 1
        return self.options_cache[module]

    def headers(self, sources):
        result = self.query([dict(mode="header", source=source, path=path, options=[])
                             for path, source in sources])
        for row in result:
            if row["error"] is not None:
                raise SourceAnalysisUnknown("source header: " + json.dumps(row["error"]))
        return result

    def external_source(self, module, packages):
        relative = module.replace(".", "/") + ".lean"
        candidates = []
        errors, found = [], []
        for package in packages:
            if package.get("type") != "git":
                errors.append("unmodeled package source ownership: " + package["name"])
                continue
            name = package["name"]
            local = self.repository / ".lake/packages" / name
            candidates.append((name.lower() != module.split(".")[0].lower(), package, local))
        candidates.sort(key=lambda item: item[0])
        for _, package, local in candidates:
            revision, url = package["rev"], package.get("url", "")
            key = (url, revision, relative)
            if key in self.source_cache:
                found.append(self.source_cache[key])
                continue
            data = None
            if local.is_dir() and local.resolve().is_relative_to((self.repository / ".lake").resolve()):
                known = subprocess.run(["git", "-C", str(local), "cat-file", "-e", revision + "^{commit}"],
                                       capture_output=True).returncode == 0
                result = subprocess.run(["git", "-C", str(local), "show", revision + ":" + relative],
                                        capture_output=True)
                if result.returncode == 0:
                    data = result.stdout
                elif known:
                    # The immutable tree establishes that this package does not
                    # supply this module at the supported source address.
                    continue
            if data is None and url.startswith("https://github.com/"):
                remote = url[len("https://github.com/"):].removesuffix(".git")
                address = "https://raw.githubusercontent.com/" + remote + "/" + revision + "/" + relative
                try:
                    with urllib.request.urlopen(address, timeout=45) as response:
                        data = response.read()
                except (urllib.error.URLError, TimeoutError) as error:
                    errors.append(str(error))
            if data is None:
                errors.append("immutable module ownership unavailable: " + package["name"] + ":" + relative)
                continue
            try:
                source = data.decode("utf-8", errors="strict")
            except UnicodeError as error:
                raise SourceAnalysisUnknown(relative + ": " + str(error)) from error
            origin = dict(package=package["name"], url=url, revision=revision, path=relative,
                          module=module, source=source, sha256=digest(data), blob=git_blob(data))
            self.source_cache[key] = origin
            self.external_bytes += len(data)
            self.external_queries += 1
            found.append(origin)
        if len(found) > 1:
            raise SourceAnalysisUnknown("ambiguous immutable source ownership for " + module)
        if errors or not found:
            raise SourceAnalysisUnknown("immutable source unavailable for " + module + ": " + "; ".join(errors))
        return found[0]

    def core_source(self, module, pin):
        # Resolve the immutable release/commit selected by the snapshot. Only source
        # bytes are retrieved; the selected old compiler is never installed or run.
        key = ("lean4-pin", pin)
        if key not in self.source_cache:
            if not pin.startswith("leanprover/lean4:"):
                raise RuntimeError("unrecognized demanded Lean source pin: " + pin)
            ref = pin.split(":", 1)[1]
            if len(ref) == 40 and all(c in "0123456789abcdef" for c in ref):
                revision = ref
            else:
                resolved = subprocess.run(["git", "ls-remote", "https://github.com/leanprover/lean4",
                    "refs/tags/" + ref, "refs/tags/" + ref + "^{}"], text=True, capture_output=True, check=True)
                lines = resolved.stdout.splitlines()
                if not lines:
                    raise RuntimeError("immutable Lean source revision unavailable: " + pin)
                revision = lines[-1].split()[0]
            self.source_cache[key] = revision
        revision = self.source_cache[key]
        relative = "src/" + module.replace(".", "/") + ".lean"
        key = ("lean4", revision, relative)
        if key not in self.source_cache:
            address = "https://raw.githubusercontent.com/leanprover/lean4/" + revision + "/" + relative
            try:
                with urllib.request.urlopen(address, timeout=45) as response:
                    data = response.read()
                source = data.decode("utf-8", errors="strict")
            except (OSError, UnicodeError) as error:
                raise SourceAnalysisUnknown(relative + ": " + str(error)) from error
            self.source_cache[key] = dict(package="lean4", pin=pin, revision=revision,
                url="https://github.com/leanprover/lean4", path=relative, module=module,
                source=source, sha256=digest(data), blob=git_blob(data))
            self.external_bytes += len(data)
            self.external_queries += 1
        return self.source_cache[key]

    def source_modules(self, request):
        reference = json.loads(request["referenceManifest"]).get("packages", [])
        same_core = request["referenceToolchain"] == request["currentToolchain"]
        managed = {entry["module"]: entry for entry in request["managed"]}
        roots = [(request["path"], request["source"])] + [(e["path"], e["source"]) for e in managed.values()]
        pending = {i["module"] for row in self.headers(roots) for i in row["imports"]}
        seen, origins = set(managed), []
        while pending - seen:
            group = []
            for module in sorted(pending - seen):
                seen.add(module)
                if module.split(".")[0] in ("Init", "Lean", "Std"):
                    if same_core:
                        continue
                    origin = self.core_source(module, request["referenceToolchain"])
                else:
                    origin = self.external_source(module, reference)
                origins.append(origin)
                group.append(origin)
            pending = set()
            if group:
                for header in self.headers([(o["path"], o["source"]) for o in group]):
                    pending.update(i["module"] for i in header["imports"])
        return origins

    def produce(self, request):
        self.consumer_requests += 1
        origins = []
        try:
            if request["kind"] == "registration":
                origins = self.source_modules(request)
            selected_options = self.current_options(request["module"])
            managed = [dict(entry, options=self.current_options(entry["module"])) for entry in request["managed"]]
            result = self.query(dict(mode=request["mode"], source=request["source"], path=request["path"],
                module=request["module"], options=selected_options, managed=managed,
                sourceModules=[dict(module=o["module"], path=o["path"], source=o["source"]) for o in origins]))
        except SourceAnalysisUnknown as error:
            result = dict(error=dict(line=1, column=0, message=str(error)))
        binding = {key: request[key] for key in ("side", "path", "sourceSha256", "producerSha256",
                    "configurationSha256", "graphSha256", "referenceConfigurationSha256")}
        binding["interfaces"] = [{"path": e["path"], "sourceSha256": e["sourceSha256"]}
                                  for e in request["managed"]]
        return dict(binding, result=result, origins=origins)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--lake", default=os.environ.get("LAKE_BIN", "lake"))
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    repository, report = args.repository.resolve(), args.report.resolve()
    resolved = subprocess.run(["git", "rev-parse", "--verify", args.base + "^{commit}"],
                              cwd=repository, text=True, capture_output=True, check=True)
    args.base = resolved.stdout.strip()
    output = Path(str(report) + ".source-context.json")
    with tempfile.TemporaryDirectory(prefix="lean-source-context-") as temporary:
        scratch = Path(temporary)
        preparation = Preparation(repository, report, args.base, scratch, args.lake)
        context = scratch / "context.json"
        empty = dict(schema=SCHEMA, files=[], registrations=[])
        context.write_bytes(output.read_bytes() if output.exists() else json.dumps(empty).encode())
        try:
            bundle = json.loads(context.read_bytes())
        except ValueError:
            bundle = None

        def row_count(value):
            return sum(len(value.get(key, [])) for key in ("files", "registrations")
                       if isinstance(value.get(key, []), list)) if isinstance(value, dict) else 0

        initial = row_count(bundle)
        reset = False
        while True:
            try:
                requests = preparation.demands(context)
            except RuntimeError:
                if args.verify or reset:
                    raise
                bundle = dict(schema=SCHEMA, files=[], registrations=[])
                context.write_text(json.dumps(bundle, ensure_ascii=False, separators=(",", ":")) + "\n")
                reset = True
                continue
            if not requests:
                break
            if args.verify:
                raise RuntimeError("bundle lacks demanded context: " + json.dumps(requests))
            for request in requests:
                collection = "registrations" if request["kind"] == "registration" else "files"
                bundle[collection] = [row for row in bundle[collection]
                    if (row["side"], row["path"]) != (request["side"], request["path"])]
                bundle[collection].append(preparation.produce(request))
            context.write_text(json.dumps(bundle, ensure_ascii=False, separators=(",", ":")) + "\n")
        if not args.verify:
            # Unused malformed input has no authority. Publish the complete empty
            # sibling when no consumer needed any of its rows, without Lean.
            if not isinstance(bundle, dict) or bundle.get("schema") != SCHEMA:
                bundle = dict(schema=SCHEMA, files=[], registrations=[])
            for collection in ("files", "registrations"):
                if not isinstance(bundle.get(collection), list):
                    bundle[collection] = []
            context.write_text(json.dumps(bundle, ensure_ascii=False, separators=(",", ":")) + "\n")
            staged = Path(str(output) + ".tmp")
            staged.write_bytes(context.read_bytes())
            os.replace(staged, output)
        print("LEAN_SOURCE_CONTEXT " + json.dumps(dict(seconds=round(time.monotonic()-preparation.started, 3),
            queries=preparation.queries, option_queries=preparation.option_queries, interfaces=preparation.interfaces, external_queries=preparation.external_queries,
            query_requests=preparation.query_requests, consumer_requests=preparation.consumer_requests,
            compiler_modules=len(preparation.compiler_queries),
            external_bytes=preparation.external_bytes, sidecar_bytes=output.stat().st_size if output.exists() else 0,
            rebuilt_stale=reset, initial_rows=initial, final_rows=row_count(bundle)), sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print("LEAN_SOURCE_CONTEXT_FAILED " + str(error), file=sys.stderr)
        raise SystemExit(2)
