"""Tail consumer probes for the worktree protocol fixture."""
import json
import os
from pathlib import Path
import select
import signal
import shutil
import subprocess
import sys
import time


class ProtocolTailCases:
    def runlocal_consumer(self):
        root = self.workspace("worktree-runlocal-", "/tmp")
        dirty, snapshot, unknown = root / "dirty", root / "snapshot", root / "unknown"
        self.g(self.main, "worktree", "add", "-b", "runlocal-recovery", dirty, self.base)
        (dirty / "owned").write_text("unpublished recovery\n")
        snapshot.mkdir()
        (snapshot / "owned").write_text("original\n")
        unknown.mkdir()
        (unknown / "private").write_text("private recovery\n")
        artifact = root / "artifact"
        artifact.write_text("unconfirmed file\n")
        container = root / "container"
        nested = container / "registered"
        self.g(self.main, "worktree", "add", "--detach", nested, self.base)
        self.g(self.main, "worktree", "lock", nested)
        targets = [dirty, snapshot, unknown, artifact]
        aged = time.time() - 3600
        for target in [*targets, container]:
            for path in ([*target.rglob("*"), target] if target.is_dir() else [target]):
                os.utime(path, (aged, aged))
        recent = root / "recent"
        recent.write_text("recent artifact\n")
        alias = root / "alias"
        alias.symlink_to(artifact)
        manifest = root / "manifest.json"
        manifest.write_text(json.dumps(dict(paths=list(map(str, [*targets, recent, alias, root, container])))))
        self.g(self.main, "remote", "remove", "origin")
        command = ["/bin/bash", str(self.source_root / "tools/scripts/agent/clean-runlocal.sh"), "--manifest", str(manifest),
            "--root", str(root), "--source", str(self.main), "--base", self.base, "--min-age-min", "15"]
        preview = self.run_owned_command(command, self.root, phase="runlocal-preview", timeout=30, check=False)
        self.assertEqual(0, preview.returncode, preview.stdout + preview.stderr)
        self.assertEqual(list(map(str, targets)), json.loads(preview.stdout)["would_remove"])
        self.assertTrue(all(path.exists() for path in targets))
        result = self.run_owned_command([*command, "--delete"], self.root, phase="runlocal", timeout=30, check=False)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(list(map(str, [dirty, snapshot, unknown, artifact])), json.loads(result.stdout)["removed"])
        self.assertFalse(snapshot.exists())
        self.assertFalse(dirty.exists())
        self.assertFalse(unknown.exists())
        self.assertFalse(artifact.exists())
        self.assertEqual("recent artifact\n", recent.read_text())
        self.assertTrue(alias.is_symlink())
        self.assertTrue(root.exists())
        self.assertTrue(nested.exists())
        self.assertEqual("nested_worktree", json.loads(result.stdout)["entries"][-1]["reason"])

    def initializer_lifetime(self, cli=None):
        cli = cli or self.initializer_cli
        # Exercise the production .NET launcher, not just Python fork/exec.
        (self.main / "lake-manifest.json").write_bytes((self.source_root / "lake-manifest.json").read_bytes())
        self.g(self.main, "add", "lake-manifest.json")
        self.g(self.main, "commit", "-m", "initializer pins")
        target = self.root / "initializing"
        binary = self.root / "bin"
        binary.mkdir()
        ready, release = self.root / "ready.fifo", self.root / "release.fifo"
        os.mkfifo(ready)
        os.mkfifo(release)
        real_git = shutil.which("git")
        shim = binary / "git"
        shim.write_text(f'''#!{sys.executable}
import os,sys
if "worktree" in sys.argv and "add" in sys.argv:
    open({str(self.root / 'native.pid')!r},"w").write(str(os.getpid()))
    with open({str(ready)!r},"w") as output: output.write("ready\\n")
    with open({str(release)!r}) as input: input.readline()
    output=os.open({str(self.root / 'native.output')!r},os.O_CREAT|os.O_WRONLY,0o600)
    os.dup2(output,1); os.dup2(output,2)
os.execv({real_git!r},[{real_git!r}]+sys.argv[1:])
''')
        shim.chmod(0o755)
        reader = os.open(ready, os.O_RDONLY | os.O_NONBLOCK)
        self.addCleanup(os.close, reader)
        job = subprocess.Popen(["dotnet", cli, "worktree", "--kind", "governance", "--name", "initializer-lifetime",
            "--path", str(target), "--source", str(self.main), "--base", "HEAD", "--skip-restore"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env=dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"]))
        self.jobs.append(job)
        self.jobs_settled = False
        self.assertTrue(select.select([reader], [], [], 20)[0], "native initializer readiness timeout")
        self.assertEqual(b"ready\n", os.read(reader, 100))
        native_pid = int((self.root / "native.pid").read_text())
        if hasattr(os, "pidfd_open"):
            handle = os.pidfd_open(native_pid)
            self.addCleanup(os.close, handle)
            wait_native = lambda: select.select([handle], [], [], 20)[0]
        else:
            handle = select.kqueue()
            self.addCleanup(handle.close)
            handle.control([select.kevent(native_pid, filter=select.KQ_FILTER_PROC,
                flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT, fflags=select.KQ_NOTE_EXIT)], 0, 0)
            wait_native = lambda: handle.control([], 1, 20)
        try:
            job.kill()
            job.wait(timeout=10)
            result = self.run_protocol("with", "--path", target, "--", "true", expect=73)
            self.assertIn("busy_scope", result.stderr)
            with release.open("w") as output:
                output.write("continue\n")
            self.assertTrue(wait_native(), "native initializer completion timeout")
            stdout, stderr = job.communicate(timeout=20)
            self.assertTrue(target.is_dir(), stdout + stderr + (self.root / "native.output").read_text())
            metadata = Path(self.g(target, "rev-parse", "--absolute-git-dir").strip())
            self.assertTrue((metadata / "locked").read_text().startswith("worktree-init:"))
            self.run_protocol("with", "--path", target, "--", "true")
        finally:
            try:
                os.kill(native_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
