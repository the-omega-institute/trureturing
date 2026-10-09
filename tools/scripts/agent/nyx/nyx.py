#!/usr/bin/env python3
"""nyx: one oracle (ChatGPT Pro) call through the NyxID oracle broker.

usage: nyx.py ask <brief> <out>   one streamed chat completion; the answer text goes to <out>
       nyx.py pools               list broker pools and mark the one `ask` would use

The route and terminal decision are those of the sshx oracle runner: a non-mutating pool
listing, then one streamed `chat/completions` call that opens a fresh conversation. There is
no retry, pool failover, task polling or call to the `nyxid oracle` CLI; a caller that wants
another attempt runs `ask` again.

Environment: NYX_CLI names the nyxid executable (default `nyxid` on PATH); NYX_POOL selects
a pool explicitly, which must be listed active with an online worker. Without NYX_POOL the
active pool with the most online workers is used, and ties keep listing order.

`ask` replaces these artifacts on every run: <out> (the answer, written only on completion),
<out>.request.json, <out>.stream (the raw response stream), <out>.stderr and
<out>.status.json, which is written last. The final stdout line is `NYX_RESULT ...`.
Exit status: 0 complete, 1 not complete, 2 usage or local I/O error.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

USAGE = "usage: nyx.py ask <brief> <out> | nyx.py pools"
POOLS_ROUTE = ("proxy", "request", "oracle", "api/v1/oracle/pools", "--output", "json")
CHAT_ROUTE = ("proxy", "request", "oracle", "api/v1/oracle/openai/v1/chat/completions", "--method", "POST", "--data")
DONE_VALUE = "[DONE]"
MODEL_FIELDS = ("model_label", "observed_model_switcher", "observed_model_effort")
ARTIFACT_SUFFIXES = ("", ".request.json", ".stream", ".stderr", ".status.json")


class UsageError(Exception):
    pass


class Failure(Exception):
    def __init__(self, reason_code: str, detail: str) -> None:
        super().__init__(f"{reason_code}: {detail}")
        self.reason_code = reason_code


def log(message: str) -> None:
    print(f"nyx: {message}", file=sys.stderr, flush=True)


# ---- broker listing -------------------------------------------------------------------
def eligible(pool: object) -> bool:
    if not isinstance(pool, dict):
        return False
    slug, workers = pool.get("slug"), pool.get("online_workers")
    return (isinstance(slug, str) and bool(slug) and pool.get("is_active") is True
            and isinstance(workers, int) and not isinstance(workers, bool) and workers > 0)


def choose_pool(pools: list[object], explicit: str | None) -> str | None:
    candidates = [pool for pool in pools if eligible(pool)]
    if explicit:
        return explicit if any(pool["slug"] == explicit for pool in candidates) else None
    chosen = None
    for pool in candidates:
        if chosen is None or pool["online_workers"] > chosen["online_workers"]:
            chosen = pool
    return None if chosen is None else chosen["slug"]


def read_pools(cli: str, cwd: Path) -> list[object]:
    try:
        completed = subprocess.run([cli, *POOLS_ROUTE], cwd=cwd, stdin=subprocess.DEVNULL,
                                   capture_output=True, check=False)
    except OSError as error:
        raise Failure("BROKER_UNAVAILABLE", f"cannot run {cli}: {error}") from error
    if completed.returncode != 0:
        detail = completed.stderr.decode("utf-8", "backslashreplace").strip()
        raise Failure("BROKER_UNAVAILABLE", f"pool listing exited {completed.returncode}: {detail}")
    try:
        pools = json.loads(completed.stdout).get("pools")
    except (ValueError, AttributeError) as error:
        raise Failure("BROKER_UNAVAILABLE", f"pool listing is not a JSON object: {error}") from error
    if not isinstance(pools, list):
        raise Failure("BROKER_UNAVAILABLE", "pool listing has no `pools` list")
    return pools


def resolve_cli() -> str:
    cli = os.environ.get("NYX_CLI") or "nyxid"
    resolved = shutil.which(cli)
    if resolved is None:
        raise Failure("BROKER_UNAVAILABLE", f"nyxid executable not found: {cli}")
    return resolved


# ---- response stream ------------------------------------------------------------------
def parse_chunk(value: str) -> dict[str, object] | None:
    """One `data:` JSON chunk reduced to what the terminal decision reads, or None."""
    try:
        chunk = json.loads(value)
    except ValueError:
        return None
    if not isinstance(chunk, dict):
        return None
    choices, oracle = chunk.get("choices", []), chunk.get("oracle")
    if not isinstance(choices, list) or not (oracle is None or isinstance(oracle, dict)):
        return None
    contents, finishes = [], []
    for choice in choices:
        if not isinstance(choice, dict):
            return None
        delta = choice.get("delta")
        if not (delta is None or isinstance(delta, dict)):
            return None
        content, finish = (delta or {}).get("content"), choice.get("finish_reason")
        if not (content is None or isinstance(content, str)) or not (finish is None or isinstance(finish, str)):
            return None
        if content:
            contents.append(content)
        if finish is not None:
            finishes.append(finish)
    return {"error": chunk.get("error"), "has_error": "error" in chunk, "contents": contents,
            "finishes": finishes, "oracle": oracle}


def observe(raw: bytes) -> dict[str, object]:
    """Read a saved server-sent-event stream; only LF separates lines and a trailing CR is dropped."""
    seen = {"parses": True, "error": None, "has_error": False, "done": False, "finish": None,
            "oracle": None, "answer": ""}
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        seen["parses"] = False
        return seen
    parts = []
    for line in text.split("\n"):
        line = line.removesuffix("\r")
        if not line.startswith("data:"):
            continue
        value = line[len("data:"):].removeprefix(" ")
        if value == DONE_VALUE:
            seen["done"] = True
            continue
        chunk = parse_chunk(value)
        if chunk is None:
            seen["parses"] = False
            continue
        if chunk["has_error"]:
            seen["has_error"], seen["error"] = True, chunk["error"]
        parts.extend(chunk["contents"])
        if chunk["finishes"]:
            seen["finish"] = chunk["finishes"][-1]
        seen["oracle"] = chunk["oracle"]
    seen["answer"] = "".join(parts)
    return seen


def decide(carrier_exit: int, seen: dict[str, object]) -> str:
    """Completion is one conjunction; the first failed condition names the reason."""
    task_id = (seen["oracle"] or {}).get("task_id")
    if carrier_exit != 0:
        return "CARRIER_EXIT_NONZERO"
    if not seen["parses"]:
        return "STREAM_MALFORMED"
    if seen["has_error"]:
        return "BROKER_ERROR"
    if not seen["done"] or seen["finish"] != "stop":
        return "STREAM_NOT_TERMINAL"
    if not (isinstance(task_id, str) and task_id):
        return "TASK_ID_MISSING"
    return "COMPLETE"


# ---- ask --------------------------------------------------------------------------------
def artifact_paths(out: Path) -> dict[str, Path]:
    names = ("answer", "request", "stream", "stderr", "status")
    return {name: Path(str(out) + suffix) for name, suffix in zip(names, ARTIFACT_SUFFIXES)}


def same_file(left: Path, right: Path) -> bool:
    try:
        return left.exists() and right.exists() and os.path.samefile(left, right)
    except OSError:
        return False


def check_ask_paths(brief: Path, out: Path) -> dict[str, Path]:
    if not brief.is_file() or not os.access(brief, os.R_OK):
        raise UsageError(f"brief is not a readable file: {brief}")
    if not out.parent.is_dir():
        raise UsageError(f"output directory does not exist: {out.parent}")
    paths = artifact_paths(out)
    for path in paths.values():
        if path.resolve() == brief.resolve() or same_file(path, brief):
            raise UsageError(f"artifact would overwrite the brief: {path}")
        if path.exists() and not path.is_file():
            raise UsageError(f"artifact path is not a regular file: {path}")
    return paths


def write_atomically(path: Path, data: bytes) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def ask(brief: Path, out: Path) -> int:
    paths = check_ask_paths(brief, out)
    for path in paths.values():
        path.unlink(missing_ok=True)
    status = {"schema_version": 1, "status": "NOT_COMPLETE", "reason_code": "INTERNAL_ERROR", "pool": None,
              "carrier_exit": None, "task_id": None, "model": None, "broker_error": None,
              "brief_ref": str(brief), "request_ref": None, "stream_ref": None, "stderr_ref": None}
    try:
        try:
            text = brief.read_bytes().decode("utf-8")
        except UnicodeDecodeError as error:
            raise Failure("BRIEF_INVALID", f"the brief is not UTF-8: {error}") from error
        cli = resolve_cli()
        pool = choose_pool(read_pools(cli, out.parent), os.environ.get("NYX_POOL") or None)
        if pool is None:
            raise Failure("BROKER_UNAVAILABLE", "no eligible active pool with an online worker")
        status["pool"] = pool
        request = {"model": f"oracle/{pool}", "stream": True, "messages": [{"role": "user", "content": text}]}
        paths["request"].write_text(json.dumps(request, ensure_ascii=False), encoding="utf-8")
        status["request_ref"] = str(paths["request"])
        log(f"broker call starting: pool {pool}")
        with paths["stream"].open("wb") as stream, paths["stderr"].open("wb") as stderr:
            status["stream_ref"], status["stderr_ref"] = str(paths["stream"]), str(paths["stderr"])
            try:
                completed = subprocess.run([cli, *CHAT_ROUTE, "@" + paths["request"].name], cwd=out.parent,
                                           stdin=subprocess.DEVNULL, stdout=stream, stderr=stderr, check=False)
            except OSError as error:
                raise Failure("BROKER_UNAVAILABLE", f"cannot run {cli}: {error}") from error
        status["carrier_exit"] = completed.returncode
        seen = observe(paths["stream"].read_bytes())
        status["broker_error"] = seen["error"]
        status["reason_code"] = decide(completed.returncode, seen)
        if status["reason_code"] == "COMPLETE":
            oracle = seen["oracle"]
            write_atomically(paths["answer"], seen["answer"].encode("utf-8"))
            status.update({"status": "COMPLETE", "task_id": oracle["task_id"], "answer_ref": str(paths["answer"]),
                           "model": {field: oracle.get(field) for field in MODEL_FIELDS}})
    except Failure as failure:
        status["reason_code"] = failure.reason_code
        log(str(failure))
    write_atomically(paths["status"], (json.dumps(status, indent=2, ensure_ascii=False) + "\n").encode("utf-8"))
    model = (status["model"] or {}).get("model_label")
    error = status["broker_error"]
    error_text = error.get("code") if isinstance(error, dict) and "code" in error else error
    print(f"NYX_RESULT status={status['status']} reason={status['reason_code']} pool={status['pool'] or '-'}"
          f" task={status['task_id'] or '-'} model={model or '-'}"
          f" broker_error={'-' if error_text is None else json.dumps(error_text, ensure_ascii=False)}"
          f" status_file={paths['status']}")
    return 0 if status["status"] == "COMPLETE" else 1


# ---- pools ------------------------------------------------------------------------------
def pools() -> int:
    try:
        cli = resolve_cli()
        listed = read_pools(cli, Path.cwd())
    except Failure as failure:
        log(str(failure))
        print("NYX_POOLS chosen=<none>")
        return 1
    chosen = choose_pool(listed, os.environ.get("NYX_POOL") or None)
    print(f"{'pool':<32} {'active':<7} {'online':>6} chosen")
    for pool in listed:
        if isinstance(pool, dict):
            mark = "yes" if pool.get("slug") == chosen else "no"
            print(f"{str(pool.get('slug')):<32} {str(pool.get('is_active')):<7} {str(pool.get('online_workers')):>6} {mark}")
    print(f"NYX_POOLS chosen={chosen or '<none>'}")
    return 0 if chosen else 1


def main(argv: list[str]) -> int:
    try:
        if len(argv) == 3 and argv[0] == "ask":
            return ask(Path(argv[1]), Path(argv[2]))
        if argv == ["pools"]:
            return pools()
        raise UsageError("unrecognized arguments")
    except UsageError as error:
        print(f"nyx: {error}\n{USAGE}", file=sys.stderr)
        return 2
    except OSError as error:
        print(f"nyx: local I/O error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
