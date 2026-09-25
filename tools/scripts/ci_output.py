"""Present periodic CI progress and immediate diagnostics, retaining raw output."""
import argparse
import codecs
import json
import math
import os
import pathlib
import re
import selectors
import signal
import subprocess
import sys
import time


ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
INFO = re.compile(r"^(?:info(?:rmation)?:|\[info(?:rmation)?\]|debug:|trace:|ℹ|✔|✓|[\u2800-\u28ff]\s*\[)", re.I)
BUILD_INFO = re.compile(r"^(?:Build succeeded\.|Passed\s|Passed!|Test run|Starting test execution|A total of|Results File:|Determining projects to restore|Restored .*\.[a-z]*proj\b|All projects are up-to-date for restore\.|.* -> .*\.(?:dll|exe)$)")
ERROR = re.compile(r"(?:\b(?:error|fatal)(?:\s+[A-Z]+\d+)?\s*[:\[]|^(?:error|fatal)\b|::error\b|\[(?:ERROR|FAIL(?:ED)?)\]|^\s*Failed\s|^✖|^Traceback\b|^Unhandled exception|\b[A-Z_]+_(?:FAILED|FAILURE|EXHAUSTED|UNRESOLVED)\b)", re.I)
WARNING = re.compile(r"(?:\bwarn(?:ing)?(?:\s+[A-Z]+\d+)?\s*[:\[]|^warn(?:ing)?\b|::warning\b|\[WARN(?:ING)?\]|^⚠)", re.I)
PROGRESS = re.compile(r"\[\s*\d+\s*/\s*\d+\s*\]|\b\d+(?:\.\d+)?%")
EVENT = re.compile(r"^[A-Z][A-Z0-9_]+ (?:\{|[a-z_]+=)")


class Presenter:
    def __init__(self, stage, output, interval=30, clock=time.monotonic):
        self.stage, self.output, self.interval, self.clock = stage, output, interval, clock
        self.started = self.last = clock()
        self.counts = {"information": 0, "warning": 0, "error": 0}
        self.detail = {}
        self.step = "starting"
        self.latest = "waiting for output"
        self.previous_information = 0
        self.progress = "unreported"
        # Replayed blocks may contain nested stage/process events. Only their
        # matching end marker closes the block, independently of live operations.
        self.block_depth = {}
        self.failed_operation = set()

    def in_detail(self, stream):
        return self.detail.get(stream) or self.block_depth.get(stream, 0) > 0 or stream in self.failed_operation

    def information(self, text=None):
        self.counts["information"] += 1
        if text:
            self.latest = " ".join(text.split())[:200]
            progress = PROGRESS.search(text)
            if progress:
                self.progress = progress.group()

    def emit(self, text):
        self.output.write(text)
        self.output.flush()

    def diagnostic(self, text, severity):
        self.counts[severity] += 1
        self.emit(text if text.endswith("\n") else text + "\n")

    @staticmethod
    def severity(value):
        for key in ("DisplaySeverity", "severity", "level"):
            if key in value:
                level = value[key]
                return {0: "information", 1: "warning", 2: "error"}.get(level) if isinstance(level, int) else {
                    "info": "information", "information": "information", "warning": "warning", "warn": "warning",
                    "error": "error", "fatal": "error", "critical": "error"}.get(str(level).lower())
        if value.get("error") or value.get("status") in ("failed", "faulted", "cancelled") or value.get("outcome") in ("faulted", "cancelled"):
            return "error"
        return None

    def structured(self, value, original, activity=True):
        # The CLI's diagnostic severity is authoritative; do not infer it from
        # words such as "error" inside an informational message or file name.
        diagnostics = value.get("diagnostics")
        if isinstance(diagnostics, list):
            for diagnostic in diagnostics:
                severity = self.severity(diagnostic) if isinstance(diagnostic, dict) else None
                if severity == "information":
                    self.information()
                else:
                    self.diagnostic(json.dumps(diagnostic, ensure_ascii=False), severity or "warning")
            return
        severity = self.severity(value)
        child = value.get("child_exit")
        if isinstance(child, dict) and child.get("code") not in (None, 0):
            severity = "warning" if child["code"] == 3 else "error"
        if severity in ("warning", "error"):
            # Stage results already retain scope, paths and successful steps in
            # their artifact. Their failure message is the useful console detail.
            if "scope" in value and value.get("error"):
                self.diagnostic(f"error: stage={self.stage} {value['error']}", severity)
            else:
                self.diagnostic(original, severity)
        else:
            fields = ("stage", "name", "phase", "status", "selected", "reused", "executed", "completed", "total")
            self.information(" ".join(f"{key}={value[key]}" for key in fields if isinstance(value.get(key), (str, int))) if activity else None)

    def line(self, line, stream):
        plain = ANSI.sub("", line).strip()
        if plain.startswith("CI_DIAGNOSTIC_BEGIN "):
            self.block_depth[stream] = self.block_depth.get(stream, 0) + 1
            self.diagnostic(line, "error")
            return
        if plain == "CI_DIAGNOSTIC_END" and self.block_depth.get(stream, 0) > 0:
            self.emit(line)
            self.block_depth[stream] -= 1
            self.failed_operation.discard(stream)
            self.detail[stream] = False
            return
        event, _, payload = plain.partition(" ")
        activity = event not in ("RESOURCE_SAMPLE", "RESOURCE_OBSERVATION")
        # A textual diagnostic may itself contain JSON. Its outer label owns
        # severity; arbitrary fields in its payload must not turn it into info.
        if not plain.startswith("{") and (ERROR.search(event) or WARNING.search(event)):
            self.detail[stream] = True
            self.diagnostic(line, "error" if ERROR.search(event) else "warning")
            return
        candidate = plain if plain.startswith("{") else payload
        value = None
        if candidate.startswith("{"):
            try:
                value = json.loads(candidate)
            except ValueError:
                pass
        if isinstance(value, dict) and (not self.in_detail(stream) or EVENT.match(plain)
                                       or any(key in value for key in ("diagnostics", "DisplaySeverity", "severity", "level"))
                                       or "scope" in value and "stage" in value):
            if event == "STAGE_STEP" and isinstance(value.get("name"), str):
                self.failed_operation.discard(stream)
                self.detail[stream] = False
                self.step = value["name"]
                self.progress = "unreported"
            elif event == "STAGE_PROCESS":
                # Non-streaming operations emit their process result before
                # their text. Keep an unsuccessful operation's explanation.
                child = value.get("child_exit")
                failed = self.severity(value) == "error" or isinstance(child, dict) and child.get("code") not in (None, 0)
                self.detail[stream] = False
                if failed:
                    self.failed_operation.add(stream)
                else:
                    self.failed_operation.discard(stream)
            self.structured(value, line, activity=activity)
        elif INFO.match(plain) or BUILD_INFO.match(plain):
            self.detail[stream] = False
            self.information(plain)
        elif ERROR.search(plain) or WARNING.search(plain):
            severity = "error" if ERROR.search(plain) else "warning"
            self.detail[stream] = True
            self.diagnostic(line, severity)
        elif EVENT.match(plain):
            # Concurrent resource sampling is not a diagnostic boundary.
            self.information(plain if activity else None)
        elif self.in_detail(stream):
            self.emit(line)
        elif PROGRESS.search(plain):
            self.information(plain)
        elif plain:
            if stream == "stderr":
                # Unlabelled stderr may be a traceback or tool failure. Preserve
                # it conservatively instead of guessing that it is information.
                self.detail[stream] = True
                self.diagnostic(line, "error")
            else:
                self.information(plain)

    def summary(self, suffix):
        counts = " ".join(f"{key}={value}" for key, value in self.counts.items())
        added = self.counts["information"] - self.previous_information
        self.emit(f"CI_SUMMARY stage={self.stage} step={self.step} progress={self.progress} elapsed={self.clock() - self.started:.0f}s {counts} new_information={added} latest={json.dumps(self.latest, ensure_ascii=False)} {suffix}\n")
        self.previous_information = self.counts["information"]

    def tick(self):
        now = self.clock()
        if now - self.last >= self.interval:
            self.summary("status=running")
            self.last = now

    def finish(self, exit_code):
        self.summary(f"status={'completed' if exit_code == 0 else 'failed'} exit={exit_code}")


def run(command, stage, log, interval):
    presenter = Presenter(stage, sys.stdout, interval)
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("w+b") as raw, selectors.DefaultSelector() as selector:
        # Keep the caller's process group so CI group cancellation still reaches
        # the shell and all of its children. A direct signal is relayed to the
        # shell, preserving its existing traps and raw exit handling.
        child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        previous = {}
        def forward(signum, _frame):
            try:
                child.send_signal(signum)
            except ProcessLookupError:
                pass
        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            previous[signum] = signal.signal(signum, forward)
        try:
            for stream, name in ((child.stdout, "stdout"), (child.stderr, "stderr")):
                selector.register(stream, selectors.EVENT_READ, [name, codecs.getincrementaldecoder("utf-8")("replace"), ""])
            while selector.get_map() or child.poll() is None:
                for key, _ in selector.select(timeout=max(0, min(0.5, presenter.last + interval - time.monotonic()))):
                    name, decoder, pending = key.data
                    chunk = os.read(key.fd, 65536)
                    raw.write(chunk)
                    raw.flush()
                    pending += decoder.decode(chunk, final=not chunk)
                    lines = re.split(r"\r\n|\r|\n", pending)
                    for line in lines[:-1]:
                        presenter.line(line + "\n", name)
                    key.data[2] = lines[-1]
                    if not chunk:
                        if lines[-1]:
                            presenter.line(lines[-1], name)
                        selector.unregister(key.fileobj)
                        key.fileobj.close()
                presenter.tick()
            exit_code = child.wait()
            exit_code = exit_code if exit_code >= 0 else 128 - exit_code
            if exit_code and presenter.counts["error"] == 0:
                presenter.diagnostic(f"error: stage={stage} exit={exit_code}; command diagnostics follow", "error")
                raw.seek(0)
                # Unknown output may explain the failure. Explicit information
                # remains summarized even when the command fails.
                replay = Presenter(stage, sys.stdout, interval)
                replay.block_depth["stdout"] = 1
                for line in raw:
                    for part in re.split(r"\r\n|\r|\n", line.decode("utf-8", "replace").rstrip("\n")):
                        replay.line(part + "\n", "stdout")
            presenter.finish(exit_code)
            return exit_code
        finally:
            if child.poll() is None:
                child.kill()
                child.wait()
            for stream in (child.stdout, child.stderr):
                stream.close()
            for signum, handler in previous.items():
                signal.signal(signum, handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("build", "engineering", "current", "delta"), required=True)
    parser.add_argument("--log", type=pathlib.Path, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required")
    try:
        interval = float(os.environ.get("CI_LOG_INTERVAL_SECONDS", "30"))
        if not math.isfinite(interval) or interval <= 0:
            raise ValueError()
    except ValueError:
        parser.error("CI_LOG_INTERVAL_SECONDS must be a finite positive number")
    try:
        return run(command, args.stage, args.log, interval)
    except OSError as error:
        print(f"error: CI console failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
