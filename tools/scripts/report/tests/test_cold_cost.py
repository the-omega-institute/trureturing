"""Behavior tests for the temporary observer; no workflow assertions."""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

PROGRAM = Path(__file__).resolve().parents[1] / "cold_cost.py"
SPEC = importlib.util.spec_from_file_location("cold_cost", PROGRAM)
cost = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cost)


class ColdCostTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.output = self.root / "observations"
        self.output.mkdir()

    def compiler(self, body, arguments=None):
        fake = self.root / "fake-lean"
        fake.write_text("#!" + sys.executable + "\n" + body)
        fake.chmod(0o755)
        source = self.root / "Sample.lean"
        source.write_text("theorem sample : True := True.intro\n")
        setup = self.root / "setup.json"
        setup.write_text('{"name":"Sample","imports":[{"module":"Init"}]}')
        env = dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(fake))
        command = [sys.executable, str(PROGRAM), "compiler"] + (arguments or [str(source), "--setup", str(setup)])
        return subprocess.run(command, env=env, capture_output=True), source

    def test_compiler_preserves_outputs_status_arguments_and_setup(self):
        result, source = self.compiler('import sys\nprint("stdout")\nprint("checked fixture",file=sys.stderr)\nsys.exit(7)\n')
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout, b"stdout\n")
        self.assertEqual(result.stderr, b"checked fixture\n")
        folders = list((self.output / "compilers").iterdir())
        events = [json.loads(row) for row in (folders[0] / "events.jsonl").read_text().splitlines()]
        self.assertEqual(events[0]["actual_argv"][1], "--profile")
        self.assertEqual(events[0]["actual_argv"][2:], events[0]["original_argv"])
        self.assertEqual(events[0]["sources"][0]["sha256"], cost.sha(source))
        self.assertEqual(events[1]["returncode"], 7)
        self.assertGreater(events[1]["monotonic_ns"], events[0]["monotonic_ns"])
        self.assertGreater(events[1]["maxrss"], 0)
        self.assertEqual((folders[0] / "setup.json").read_text(), (self.root / "setup.json").read_text())
        self.assertEqual((folders[0] / "stdout.log").read_bytes(), result.stdout)
        self.assertEqual((folders[0] / "stderr.log").read_bytes(), result.stderr)

    def test_compiler_preserves_signal_failure(self):
        result, _ = self.compiler('import os,signal\nos.kill(os.getpid(),signal.SIGTERM)\n')
        self.assertEqual(result.returncode, -signal.SIGTERM)
        end = next((self.output / "compilers").glob("*/events.jsonl")).read_text().splitlines()[-1]
        self.assertEqual(json.loads(end)["returncode"], -signal.SIGTERM)

    def test_noncompile_query_executes_without_profiler(self):
        result, _ = self.compiler('import sys\nprint(sys.argv[1:])\n', ["--version"])
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"['--version']\n")
        self.assertFalse((self.output / "compilers").exists())

    def test_stage_failure_keeps_raw_logs_even_when_sampler_unavailable(self):
        with patch.object(cost, "sample", side_effect=OSError("sample unavailable")):
            rc = cost.observe_command([sys.executable, "-c", 'import sys,time; print("raw"); print("err",file=sys.stderr); time.sleep(.05); sys.exit(9)'],
                                      self.root, self.output, "fixture", dict(os.environ), interval=.01)
        self.assertEqual(rc, 9)
        self.assertEqual((self.output / "fixture.stdout.log").read_text(), "raw\n")
        self.assertEqual((self.output / "fixture.stderr.log").read_text(), "err\n")
        end = json.loads((self.output / "stages.jsonl").read_text().splitlines()[-1])
        self.assertEqual(end["returncode"], 9)
        self.assertTrue((self.output / "observer-errors.jsonl").is_file())

    def test_linux_sample_types_scopes_and_descendant_selection(self):
        proc = self.root / "proc"
        proc.mkdir()
        for pid, parent in ((10, 1), (11, 10), (12, 11), (13, 1)):
            folder = proc / str(pid)
            folder.mkdir()
            fields = ["S", str(parent)] + ["0"] * 22
            fields[11], fields[12], fields[19], fields[21] = "123", "456", "900", "42"
            (folder / "stat").write_text(f"{pid} (a tricky ) name) " + " ".join(fields))
            (folder / "cmdline").write_bytes(b"lean\0Sample.lean\0")
            (folder / "cgroup").write_text("0::/job\n")
        cg = self.root / "cgroup" / "job"
        cg.mkdir(parents=True)
        (cg / "cpu.stat").write_text("usage_usec 1234\n")
        (cg / "memory.events").write_text("oom_kill 2\n")
        row = cost.sample(10, proc, self.root / "cgroup")
        self.assertEqual([p["pid"] for p in row["processes"]], [10, 11, 12])
        self.assertEqual(row["processes"][0]["start_ticks"], 900)
        self.assertEqual(row["processes"][0]["user_ticks"], 123)
        self.assertEqual(row["cgroup"]["cpu.stat"], "usage_usec 1234\n")
        self.assertEqual(row["cgroup"]["memory.events"], "oom_kill 2\n")
        self.assertIsNone(row["kernel"]["pressure/cpu"])
        self.assertIn("sampled", row["scope"])

    def spawn_driver(self, linked=True):
        driver = self.root / "driver.c"
        driver.write_text('''#include <spawn.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
extern char **environ;
int main(int argc, char **argv) {
  if (argc < 2) return 2;
  char *kind = getenv("COLD_COST_TEST_SPAWN_KIND");
  if (kind && strcmp(kind,"execv")==0) { execv(argv[1],argv+1); return 2; }
  if (kind && strcmp(kind,"execvp")==0) { execvp(argv[1],argv+1); return 2; }
  if (kind && strcmp(kind,"execve")==0) { execve(argv[1],argv+1,environ); return 2; }
  pid_t pid; int status;
  int rc = kind && strcmp(kind,"posix_spawn")==0
    ? posix_spawn(&pid, argv[1], 0, 0, argv + 1, environ)
    : posix_spawnp(&pid, argv[1], 0, 0, argv + 1, environ);
  if (rc) return rc;
  if (waitpid(pid, &status, 0) < 0) return 2;
  return WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
}
''')
        executable = self.root / "driver"
        cmd = ["cc", "-Wall", "-Wextra", "-Werror", str(driver)]
        if linked:
            cmd += [str(PROGRAM.with_name("cold_cost_spawn.c"))]
        cmd += ["-o", str(executable)]
        if sys.platform == "linux":
            cmd += ["-ldl"]
        subprocess.run(cmd, check=True, capture_output=True)
        return executable

    def test_compiled_spawn_observer_forwards_and_does_not_recurse(self):
        driver = self.spawn_driver()
        lean = self.root / "lean"
        lean.write_text("#!" + sys.executable + '\nimport sys\nprint(sys.argv[1:])\nsys.exit(6)\n')
        lean.chmod(0o755)
        source = self.root / "Source.lean"
        source.write_text("example : True := True.intro\n")
        env = dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(lean),
                   COLD_COST_PROGRAM=str(PROGRAM), COLD_COST_PYTHON=sys.executable)
        for kind in ("posix_spawn", "posix_spawnp", "execv", "execvp", "execve"):
            with self.subTest(kind=kind):
                result = subprocess.run([str(driver), str(lean), str(source)],
                                        env=dict(env, COLD_COST_TEST_SPAWN_KIND=kind), capture_output=True)
                self.assertEqual(result.returncode, 6)
                self.assertIn(b"--profile", result.stdout)
        self.assertEqual(len(list((self.output / "compilers").iterdir())), 5)
        query = subprocess.run([str(driver), str(lean), "--version"], env=env, capture_output=True)
        self.assertEqual(query.returncode, 6)
        self.assertNotIn(b"--profile", query.stdout)

    def test_native_entry_rejects_local_identity_before_any_execution(self):
        with patch.object(cost, "git", return_value=b"0" * 40), patch.dict(os.environ, {"GITHUB_EVENT_PATH": str(self.root / "event.json")}):
            (self.root / "event.json").write_text('{}')
            with self.assertRaisesRegex(ValueError, "genuine labeled"):
                cost.native_binding(self.root, dict(os.environ))

    @unittest.skipUnless(os.environ.get("COLD_COST_TEST_LEAN"), "requires explicitly supplied pinned test compiler")
    def test_actual_pinned_compiler_spawn_keeps_toolchain_and_olean_bytes(self):
        # Independent core fixture, not a repository build or report acceptance.
        real = Path(os.environ["COLD_COST_TEST_LEAN"]).resolve()
        source = self.root / "Fixture.lean"
        source.write_text("def diagnostic_fixture : Nat := 3\ntheorem diagnostic_fixture_ok : diagnostic_fixture = 3 := rfl\n")
        original = source.read_bytes()
        baseline = self.root / "control.olean"
        control = subprocess.run([str(real), "-Dprofiler.threshold=0", "-o", str(baseline), str(source)],
                                 cwd=self.root, capture_output=True)
        self.assertEqual(control.returncode, 0, control.stderr.decode())
        driver = self.spawn_driver()
        env = dict(os.environ, COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(real),
                   COLD_COST_PROGRAM=str(PROGRAM), COLD_COST_PYTHON=sys.executable)
        observed = self.root / "observed.olean"
        result = subprocess.run([str(driver), str(real), "-Dprofiler.threshold=0", "-o", str(observed), str(source)],
                                cwd=self.root, env=env, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertIn(b"type checking", result.stderr)
        self.assertEqual(source.read_bytes(), original)
        self.assertEqual(cost.sha(baseline), cost.sha(observed))
        events = next((self.output / "compilers").glob("*/events.jsonl"))
        self.assertEqual(json.loads(events.read_text().splitlines()[0])["actual_argv"][0], str(real))
        self.assertEqual(cost.sha(real), cost.sha(Path(os.environ["COLD_COST_TEST_LEAN"])))

    @unittest.skipUnless(sys.platform == "linux", "actual LD_PRELOAD requires Linux")
    def test_linux_dynamic_spawn_observer(self):
        library = cost.build_spawn_observer(self.output)
        driver = self.spawn_driver(linked=False)
        lean = self.root / "lean"
        lean.write_text("#!" + sys.executable + '\nimport sys\nprint(sys.argv[1:])\nsys.exit(4)\n')
        lean.chmod(0o755)
        source = self.root / "Source.lean"
        source.write_text("example : True := True.intro\n")
        env = dict(os.environ, LD_PRELOAD=str(library), COLD_COST_OUTPUT=str(self.output), COLD_COST_REAL_LEAN=str(lean),
                   COLD_COST_PROGRAM=str(PROGRAM), COLD_COST_PYTHON=sys.executable)
        result = subprocess.run([str(driver), str(lean), str(source)], env=env, capture_output=True)
        self.assertEqual(result.returncode, 4)
        self.assertIn(b"--profile", result.stdout)
        self.assertEqual(len(list((self.output / "compilers").iterdir())), 1)


if __name__ == "__main__":
    unittest.main()
