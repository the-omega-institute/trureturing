import contextlib
import hashlib
import importlib.util
import io
import json
import subprocess
import unittest
from pathlib import Path
from unittest.mock import Mock, patch
import zipfile


spec = importlib.util.spec_from_file_location("coordinator", Path(__file__).with_name("compiler-release-coordinator.py"))
controller = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controller)


def key(n):
    return f"{n:064x}"


def example(dependencies, lanes):
    units = {}
    for n, deps in enumerate(dependencies):
        name = f"compiler-unit-{key(n)}.tar.gz"
        units[key(n)] = dict(key=name, asset=name, fingerprint=key(n), members=[f"M{n}"], artifact_kind="compiler",
                             rank=len(deps), deps=[key(d) for d in deps])
    return (dict(lanes=list(lanes), compiler_dag={"units": units}),
            dict(units=list(units), lanes=list(range(len(lanes))),
                 lane_units={str(i): [key(n) for n in deps] for i, deps in enumerate(lanes)}))


def receipt(plan, k):
    row = plan["compiler_dag"]["units"][k]
    return {**row, "bytes": 16, "version": "test", "sha256": key(42)}


class Actions:
    def __init__(self, plan, latency=0):
        self.plan = plan
        self.latency = latency
        self.jobs = {}
        self.submitted = []
        self.tick = 0
        self.peak = 0

    def title(self, batch, phase):
        return f"{batch}/{phase}"

    def dispatch(self, batch, phase, assignment):
        run = 1000 + batch
        self.jobs[run] = (batch, phase, assignment, self.tick + self.latency)
        self.submitted.append((phase, assignment))
        self.peak = max(self.peak, len(self.jobs))
        return run

    def runs(self, *args, **options):
        self.tick += 1
        return [dict(id=run, display_title=self.title(batch, phase),
                     status="completed" if self.tick >= due else "in_progress", conclusion="success")
                for run, (batch, phase, _, due) in self.jobs.items()]

    def matches(self, row, title):
        return row["display_title"] == title

    def result(self, run, batch):
        assert self.jobs[run][0] == batch
        _, phase, assignment, _ = self.jobs.pop(run)
        if phase == "shards":
            return {"lanes": assignment}
        return {k: receipt(self.plan, k) for k in assignment}


class ScheduleTests(unittest.TestCase):
    def test_receipts_release_only_ready_dependents_and_physical_shards(self):
        plan, pending = example([[], [0], [], [1, 2]], [[0], [0, 1, 2, 3]])
        schedule = controller.Schedule(plan, pending, {key(0): receipt(plan, key(0))})
        self.assertEqual(schedule.take(2, 1), ("shards", [0]))
        phase, assignment = schedule.take(2, 1)
        self.assertEqual(assignment, [key(1), key(2)])
        self.assertIsNone(schedule.take(2, 1))
        schedule.accept(phase, assignment, {k: receipt(plan, k) for k in assignment})
        self.assertEqual(schedule.take(2, 1), ("units", [key(3)]))
        schedule.accept("units", [key(3)], {key(3): receipt(plan, key(3))})
        self.assertEqual(schedule.take(2, 1), ("shards", [1]))

    def test_more_than_64_concurrent_children_and_optional_active_bound(self):
        plan, pending = example([[] for _ in range(140)], [[n] for n in range(140)])
        for limit in (None, 7):
            github = Actions(plan, latency=9)
            with patch.object(controller.time, "sleep"), contextlib.redirect_stdout(io.StringIO()):
                controller.coordinate(github, controller.Schedule(plan, pending, {}), limit, 1, 3)
            if limit is None:
                self.assertGreater(github.peak, 64)
            else:
                self.assertEqual(github.peak, limit)
            units = [k for phase, rows in github.submitted if phase == "units" for k in rows]
            lanes = [n for phase, rows in github.submitted if phase == "shards" for n in rows]
            self.assertCountEqual(units, list(plan["compiler_dag"]["units"]))
            self.assertCountEqual(lanes, list(range(140)))

    def test_bounded_retries_and_partial_checkpoint_recovery(self):
        plan, pending = example([[], [], [0, 1]], [[0, 1, 2]])
        github = Actions(plan)
        original = github.runs
        def interrupted(*args, **kwargs):
            rows = original(*args, **kwargs)
            for row in rows:
                if row["id"] == 1001:
                    row["conclusion"] = "cancelled"
            return rows
        github.runs = interrupted
        refresh = Mock(return_value=({key(0): receipt(plan, key(0))}, None))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            controller.coordinate(github, controller.Schedule(plan, pending, {}), None, 8, 1, refresh)
        refresh.assert_called_once_with("units")
        self.assertEqual(github.submitted, [("units", [key(0), key(1)]), ("units", [key(1)]),
                                            ("units", [key(2)]), ("shards", [0])])

    def test_failed_physical_worker_can_have_completed_the_release_artifact(self):
        plan, pending = example([], [[]])
        github = Actions(plan)
        github.runs = Mock(return_value=[dict(id=1001, display_title="1/shards", status="completed",
                                              conclusion="cancelled")])
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            controller.coordinate(github, controller.Schedule(plan, pending, {}), None, 1, 1,
                                  lambda phase: (None, {"lanes":[]}))
        self.assertEqual(github.submitted, [("shards", [0])])

    def test_persistent_failure_lists_exact_runs_and_blocks_downstream(self):
        plan, pending = example([[], [0]], [[0, 1]])
        github = Actions(plan)
        original = github.runs
        github.runs = lambda *a, **kw: [dict(row, conclusion="failure") for row in original(*a, **kw)]
        with self.assertRaisesRegex(RuntimeError, r"1001, 1002, 1003"), contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            controller.coordinate(github, controller.Schedule(plan, pending, {}), None, 1, 1)
        self.assertEqual(github.submitted, [("units", [key(0)])] * 3)

    def test_rejects_omitted_dependencies_duplicate_keys_and_mismatched_receipts(self):
        plan, pending = example([[], [0]], [[0, 1]])
        with self.assertRaises(ValueError):
            controller.Schedule(plan, dict(pending, units=[key(1)]), {})
        with self.assertRaises(ValueError):
            controller.Schedule(plan, dict(pending, units=[key(0)] * 2), {})
        schedule = controller.Schedule(plan, pending, {})
        for rows in [{}, {key(0): receipt(plan, key(1))}, {key(0): dict(receipt(plan, key(0)), sha256="bad")}]:
            with self.assertRaises(ValueError):
                schedule.accept("units", [key(0)], rows)
        with self.assertRaises(ValueError):
            schedule.accept("shards", [0], {"lanes": [False]})

    def test_cycle_fails_without_dispatch(self):
        plan, pending = example([[1], [0]], [[0, 1]])
        with self.assertRaisesRegex(ValueError, "do not admit"):
            controller.coordinate(Actions(plan), controller.Schedule(plan, pending, {}), None, 1, 1)

    def test_pending_run_metadata_can_arrive_after_dispatch(self):
        plan, pending = example([[]], [])
        github = Actions(plan, latency=2)
        listing = github.runs

        def runs(*args, **options):
            return [dict(row, display_title=None) if row["status"] != "completed" else row
                    for row in listing(*args, **options)]

        github.runs = runs
        with patch.object(controller.time, "sleep"), contextlib.redirect_stdout(io.StringIO()):
            controller.coordinate(github, controller.Schedule(plan, pending, {}), None, 1, 1)
        self.assertEqual(github.submitted, [("units", [key(0)])])

    def test_completed_run_identity_is_checked_against_exact_run(self):
        plan, pending = example([[]], [])
        for exact_title in ("1/units", "unrelated"):
            with self.subTest(exact_title=exact_title), contextlib.redirect_stdout(io.StringIO()):
                github = Actions(plan)
                github.runs = Mock(return_value=[dict(id=1001, status="completed", display_title=None)])
                github.json = Mock(return_value=dict(id=1001, status="completed", conclusion="success",
                                                     display_title=exact_title))
                schedule = controller.Schedule(plan, pending, {})
                if exact_title == "1/units":
                    controller.coordinate(github, schedule, None, 1, 1)
                    self.assertEqual(schedule.done, {key(0)})
                else:
                    with self.assertRaisesRegex(ValueError, "untrusted compiler workflow run 1001"):
                        controller.coordinate(github, schedule, None, 1, 1)
                    self.assertEqual(schedule.done, set())
                github.json.assert_called_once_with("actions/runs/1001")


class ApiTests(unittest.TestCase):
    def setUp(self):
        self.github = object.__new__(controller.GitHub)
        self.github.repo = "owner/repo"
        self.github.workflow_id = 74
        self.github.parent = "700"
        self.github.attempt = "2"
        self.github.source = "a" * 40
        self.github.path = "actions/workflows/" + controller.WORKFLOW
        self.github.last_dispatch = 0
        self.row = dict(id=91, workflow_id=74, event="workflow_dispatch", display_title=self.github.title(1, "units"),
                        actor={"login":"github-actions[bot]"}, head_branch="dev",
                        repository={"full_name":"owner/repo"}, head_repository={"full_name":"owner/repo"})

    def test_lost_dispatch_response_recovers_only_matching_bot_run_and_never_reposts(self):
        self.github.json = Mock(side_effect=RuntimeError("connection reset"))
        self.github.runs = Mock(return_value=[dict(self.row, actor={"login":"someone"}), self.row])
        with patch.object(controller.time, "sleep"), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(self.github.dispatch(1, "units", [key(1)]), 91)
        self.assertEqual(self.github.json.call_count, 1)
        self.github.runs.return_value = [self.row, dict(self.row, id=92)]
        with patch.object(controller.time, "sleep"), contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaisesRegex(ValueError, "multiple"):
                self.github.dispatch(1, "units", [key(1)])

    def test_dispatch_return_run_details_variants(self):
        for response in ({"workflow_run_id":91,"run_url":"example"}, {"run_id":91}, {"id":91}):
            self.github.json = Mock(return_value=response)
            with patch.object(controller.time, "sleep"):
                self.assertEqual(self.github.dispatch(1, "units", [key(1)]), 91)
            payload = self.github.json.call_args.kwargs["payload"]
            self.assertEqual(payload["inputs"]["assignment"], json.dumps([key(1)]))
            self.assertTrue(payload["return_run_details"])
            self.assertEqual(payload["ref"], "dev")

    def test_artifact_is_bound_to_exact_child_digest_and_result_member(self):
        archive = io.BytesIO()
        with zipfile.ZipFile(archive, "w") as z:
            z.writestr("result.json", json.dumps({"lanes":[0]}))
        raw = archive.getvalue()
        row = dict(id=133, name="compiler-result-2-1", expired=False, workflow_run={"id":91},
                   digest="sha256:" + hashlib.sha256(raw).hexdigest())
        self.github.api = Mock(return_value=raw)
        self.github.json = Mock(return_value={"artifacts":[row]})
        self.assertEqual(self.github.result(91, 1), {"lanes":[0]})
        self.assertIn("actions/runs/91/artifacts?", self.github.json.call_args.args[0])
        self.github.json = Mock(side_effect=[{"artifacts":[]}, {"artifacts":[row]}])
        with patch.object(controller.time, "sleep"):
            self.assertEqual(self.github.result(91, 1), {"lanes":[0]})
        self.github.json = Mock()
        # Older run-scoped responses can omit the redundant workflow_run field.
        self.github.json.return_value = {"artifacts":[{k:v for k,v in row.items() if k != "workflow_run"}]}
        self.assertEqual(self.github.result(91, 1), {"lanes":[0]})
        for invalid in (dict(row, expired=True), dict(row, workflow_run={"id":92}), dict(row, digest=key(0))):
            self.github.json.return_value = {"artifacts":[invalid]}
            with self.assertRaises(ValueError):
                self.github.result(91, 1)

    def test_reads_recover_from_timeout_and_recent_404_without_dispatch(self):
        args = ["gh", "api"]
        events = [subprocess.TimeoutExpired(args, 120),
                  subprocess.CompletedProcess(args, 1, b"", b"gh: Not Found (HTTP 404)"),
                  subprocess.CompletedProcess(args, 0, b'{"id":91}', b"")]
        with patch.object(controller.subprocess, "run", side_effect=events) as call, patch.object(controller.time, "sleep"):
            self.assertEqual(self.github.json("actions/runs/91"), {"id":91})
        self.assertEqual(call.call_count, 3)
        self.assertTrue(all("POST" not in c.args[0] for c in call.call_args_list))

    def test_wrong_repository_event_or_workflow_rejected(self):
        for field, value in (("workflow_id",75), ("event","push"), ("head_branch","feature"),
                             ("actor", None), ("head_repository", {"full_name":"other/repo"}),
                             ("head_repository", None), ("display_title","other")):
            with self.subTest(field=field):
                self.assertFalse(self.github.matches(dict(self.row, **{field:value}), self.row["display_title"]))


if __name__ == "__main__":
    unittest.main()
