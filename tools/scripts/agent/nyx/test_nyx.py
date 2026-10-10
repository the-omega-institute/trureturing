"""Behavioral contracts for nyx.py, the oracle broker client, driven through a fake nyxid."""
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import textwrap
import unittest

NYX = Path(__file__).resolve().with_name("nyx.py")
POOLS_ROUTE = ["proxy", "request", "oracle", "api/v1/oracle/pools", "--output", "json"]
CHAT_ROUTE = ["proxy", "request", "oracle", "api/v1/oracle/openai/v1/chat/completions", "--method", "POST", "--data"]

FAKE_NYXID = textwrap.dedent('''\
    #!/usr/bin/env python3
    import json, os, sys
    from pathlib import Path
    fake = Path(os.environ["FAKE_DIR"])
    argv = sys.argv[1:]
    with (fake / "calls.jsonl").open("a", encoding="utf-8") as calls:
        calls.write(json.dumps({"argv": argv, "cwd": os.getcwd()}) + "\\n")
    def emit(name):
        path = fake / name
        if path.exists():
            sys.stdout.buffer.write(path.read_bytes())
    def code(name):
        path = fake / name
        return int(path.read_text()) if path.exists() else 0
    if argv == %(pools)r:
        emit("listing.json")
        sys.exit(code("listing.rc"))
    if argv[:-1] == %(chat)r and argv[-1].startswith("@"):
        (fake / "request.seen").write_bytes(Path(argv[-1][1:]).read_bytes())
        emit("stream.sse")
        if (fake / "chat.stderr").exists():
            sys.stderr.write((fake / "chat.stderr").read_text())
        sys.exit(code("chat.rc"))
    sys.stderr.write("fake nyxid: unexpected argv %%r\\n" %% (argv,))
    sys.exit(99)
    ''') % {"pools": POOLS_ROUTE, "chat": CHAT_ROUTE}


def listing(*pools):
    return json.dumps({"pools": [
        {"slug": slug, "is_active": active, "online_workers": workers} for slug, active, workers in pools
    ]})


def sse(*values, newline="\n"):
    lines = []
    for value in values:
        lines.append("data: " + (value if isinstance(value, str) else json.dumps(value, ensure_ascii=False)))
        lines.append("")
    return newline.join(lines) + newline


def chunk(content=None, finish=None, oracle=None, **extra):
    document = {"choices": [{"delta": {} if content is None else {"content": content}, "finish_reason": finish}]}
    if oracle is not None:
        document["oracle"] = oracle
    document.update(extra)
    return document


ORACLE = {"task_id": "task-0001", "model_label": "chatgpt-pro", "observed_model_switcher": "gpt", "observed_model_effort": "pro"}
GOOD_STREAM = sse(chunk("Hello, ")) + ": keep-alive\n\n" + sse(chunk("world."), chunk(finish="stop", oracle=ORACLE), "[DONE]")


class NyxContracts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="nyx contract ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.fake = self.root / "fake dir"
        self.fake.mkdir()
        self.cli = self.fake / "nyxid"
        self.cli.write_text(FAKE_NYXID, encoding="utf-8")
        self.cli.chmod(self.cli.stat().st_mode | stat.S_IXUSR)
        self.work = self.root / "work dir"
        self.work.mkdir()
        self.brief = self.work / "brief.md"
        self.brief.write_text("Prove the lemma.\nUse ∑ and   safely.\n", encoding="utf-8")
        self.out = self.work / "answer.txt"
        self.set_listing(listing(("small-pool", True, 2), ("big-pool", True, 9), ("idle-pool", False, 50)))
        self.set_stream(GOOD_STREAM)

    def set_listing(self, text, rc=0):
        (self.fake / "listing.json").write_text(text, encoding="utf-8")
        (self.fake / "listing.rc").write_text(str(rc))

    def set_stream(self, text, rc=0, stderr=None):
        (self.fake / "stream.sse").write_bytes(text.encode("utf-8") if isinstance(text, str) else text)
        (self.fake / "chat.rc").write_text(str(rc))
        if stderr is not None:
            (self.fake / "chat.stderr").write_text(stderr)

    def run_nyx(self, *args, env=None, cwd=None):
        environment = {key: value for key, value in os.environ.items() if not key.startswith("NYX_")}
        environment.update({"NYX_CLI": str(self.cli), "FAKE_DIR": str(self.fake)})
        environment.update(env or {})
        return subprocess.run([sys.executable, str(NYX), *map(str, args)], cwd=cwd or self.root,
                              env=environment, capture_output=True, text=True, check=False)

    def calls(self):
        path = self.fake / "calls.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def chat_calls(self):
        return [call for call in self.calls() if call["argv"][:len(CHAT_ROUTE)] == CHAT_ROUTE]

    def status(self):
        return json.loads(Path(str(self.out) + ".status.json").read_text(encoding="utf-8"))

    # ---- usage and input boundaries -----------------------------------------------------
    def test_usage_errors_exit_two_without_any_call(self):
        cases = [(), ("bogus",), ("ask",), ("ask", self.brief), ("ask", self.brief, self.out, "extra"),
                 ("ask", self.work / "missing.md", self.out), ("ask", self.brief, self.brief),
                 ("ask", self.brief, self.work), ("pools", "extra")]
        for args in cases:
            with self.subTest(args=args):
                completed = self.run_nyx(*args)
                self.assertEqual(completed.returncode, 2, completed.stderr)
                self.assertIn("usage", completed.stderr.lower())
        self.assertEqual(self.calls(), [])

    def test_artifact_name_colliding_with_brief_is_rejected(self):
        colliding = self.work / "x"
        Path(str(colliding) + ".stream").write_text("brief\n")
        completed = self.run_nyx("ask", Path(str(colliding) + ".stream"), colliding)
        self.assertEqual(completed.returncode, 2)
        self.assertEqual(Path(str(colliding) + ".stream").read_text(), "brief\n")
        self.assertEqual(self.calls(), [])

    def test_non_utf8_brief_is_not_sent(self):
        self.brief.write_bytes(b"\xff\xfe broken")
        completed = self.run_nyx("ask", self.brief, self.out)
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(self.status()["reason_code"], "BRIEF_INVALID")
        self.assertEqual(self.calls(), [])
        self.assertFalse(self.out.exists())

    # ---- capability check and pool choice ----------------------------------------------
    def test_no_active_pool_with_workers_is_broker_unavailable(self):
        for text, rc in [(listing(("a", False, 9), ("b", True, 0)), 0), ("not json", 0),
                         (json.dumps({"pools": "x"}), 0), (listing(("a", True, 3)), 1)]:
            with self.subTest(listing=text, rc=rc):
                self.set_listing(text, rc)
                completed = self.run_nyx("ask", self.brief, self.out)
                self.assertEqual(completed.returncode, 1)
                self.assertEqual(self.status()["reason_code"], "BROKER_UNAVAILABLE")
                self.assertIn("NYX_RESULT status=NOT_COMPLETE reason=BROKER_UNAVAILABLE", completed.stdout)
        self.assertEqual(self.chat_calls(), [])

    def test_missing_cli_is_broker_unavailable(self):
        completed = self.run_nyx("ask", self.brief, self.out, env={"NYX_CLI": str(self.root / "absent-nyxid")})
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(self.status()["reason_code"], "BROKER_UNAVAILABLE")

    def test_pool_with_most_online_workers_wins_and_ties_keep_listing_order(self):
        self.set_listing(listing(("first", True, 4), ("second", True, 4), ("third", True, 3)))
        completed = self.run_nyx("ask", self.brief, self.out)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(self.status()["pool"], "first")

    def test_explicit_pool_must_be_listed_active_with_workers(self):
        completed = self.run_nyx("ask", self.brief, self.out, env={"NYX_POOL": "small-pool"})
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(self.status()["pool"], "small-pool")
        for pool in ("idle-pool", "unknown-pool"):
            with self.subTest(pool=pool):
                completed = self.run_nyx("ask", self.brief, self.out, env={"NYX_POOL": pool})
                self.assertEqual(completed.returncode, 1)
                self.assertEqual(self.status()["reason_code"], "BROKER_UNAVAILABLE")
        self.assertEqual(len(self.chat_calls()), 1)

    def test_pools_verb_lists_pools_and_marks_the_chosen_one(self):
        completed = self.run_nyx("pools")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        rows = {line.split()[0]: line for line in completed.stdout.splitlines() if line and not line.startswith(("pool", "NYX_"))}
        self.assertEqual(set(rows), {"small-pool", "big-pool", "idle-pool"})
        self.assertIn("NYX_POOLS chosen=big-pool", completed.stdout)
        self.set_listing("not json")
        self.assertEqual(self.run_nyx("pools").returncode, 1)
        self.set_listing(listing(("a", False, 1)))
        completed = self.run_nyx("pools")
        self.assertEqual(completed.returncode, 1)
        self.assertIn("NYX_POOLS chosen=<none>", completed.stdout)

    # ---- request and completion --------------------------------------------------------
    def test_complete_answer_request_and_status(self):
        completed = self.run_nyx("ask", self.brief, self.out, cwd=self.fake)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(self.out.read_text(encoding="utf-8"), "Hello, world.")
        request = json.loads((self.fake / "request.seen").read_text(encoding="utf-8"))
        self.assertEqual(request, {"model": "oracle/big-pool", "stream": True,
                                   "messages": [{"role": "user", "content": self.brief.read_text(encoding="utf-8")}]})
        status = self.status()
        self.assertEqual((status["status"], status["reason_code"], status["carrier_exit"]), ("COMPLETE", "COMPLETE", 0))
        self.assertEqual(status["task_id"], "task-0001")
        self.assertEqual(status["model"], {k: ORACLE[k] for k in ("model_label", "observed_model_switcher", "observed_model_effort")})
        self.assertEqual(status["answer_ref"], str(self.out))
        self.assertEqual(Path(status["stream_ref"]).read_text(encoding="utf-8"), GOOD_STREAM)
        self.assertIn("NYX_RESULT status=COMPLETE reason=COMPLETE pool=big-pool task=task-0001", completed.stdout)
        self.assertEqual(len(self.chat_calls()), 1)

    def test_crlf_lines_and_unicode_separators_are_preserved(self):
        self.set_stream(sse(chunk("a b ∑"), chunk(finish="stop", oracle=ORACLE), "[DONE]", newline="\r\n"))
        completed = self.run_nyx("ask", self.brief, self.out)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(self.out.read_text(encoding="utf-8"), "a b ∑")

    def test_every_incomplete_shape_is_not_complete_and_leaves_no_answer(self):
        cases = {
            "CARRIER_EXIT_NONZERO": (GOOD_STREAM, 1),
            "STREAM_MALFORMED": (sse(chunk("x"), "{not json", chunk(finish="stop", oracle=ORACLE), "[DONE]"), 0),
            "BROKER_ERROR": (sse(chunk("x"), {"error": {"code": "model_unavailable"}}, "[DONE]"), 0),
            "STREAM_NOT_TERMINAL": (sse(chunk("x"), chunk(finish="stop", oracle=ORACLE)), 0),
            "TASK_ID_MISSING": (sse(chunk("x"), chunk(finish="stop", oracle={"task_id": ""}), "[DONE]"), 0),
        }
        for reason, (stream, rc) in cases.items():
            with self.subTest(reason=reason):
                self.out.write_text("stale answer from an earlier run")
                self.set_stream(stream, rc)
                completed = self.run_nyx("ask", self.brief, self.out)
                self.assertEqual(completed.returncode, 1, completed.stdout)
                self.assertEqual(self.status()["status"], "NOT_COMPLETE")
                self.assertEqual(self.status()["reason_code"], reason)
                self.assertFalse(self.out.exists(), "a failed run must not leave an answer behind")

    def test_finish_reason_other_than_stop_and_quoted_done_are_not_terminal(self):
        for stream in (sse(chunk("x"), chunk(finish="length", oracle=ORACLE), "[DONE]"),
                       sse(chunk("data: [DONE]\n[DONE]"), chunk(finish="stop", oracle=ORACLE)),):
            with self.subTest(stream=stream):
                self.set_stream(stream)
                completed = self.run_nyx("ask", self.brief, self.out)
                self.assertEqual(completed.returncode, 1)
                self.assertEqual(self.status()["reason_code"], "STREAM_NOT_TERMINAL")

    def test_broker_error_detail_is_reported(self):
        self.set_stream(sse({"error": {"code": "prompt_delivery_uncertain", "message": "unknown"}}, "[DONE]"))
        completed = self.run_nyx("ask", self.brief, self.out)
        self.assertEqual(completed.returncode, 1)
        self.assertEqual(self.status()["broker_error"], {"code": "prompt_delivery_uncertain", "message": "unknown"})
        self.assertIn("prompt_delivery_uncertain", completed.stdout)

    def test_carrier_stderr_is_kept(self):
        self.set_stream("", rc=1, stderr='{"status": 429, "error": "queue full"}\n')
        completed = self.run_nyx("ask", self.brief, self.out)
        self.assertEqual(completed.returncode, 1)
        self.assertIn("queue full", Path(self.status()["stderr_ref"]).read_text())

    def test_rerun_replaces_previous_artifacts(self):
        self.assertEqual(self.run_nyx("ask", self.brief, self.out).returncode, 0)
        self.set_stream(sse(chunk("second"), chunk(finish="stop", oracle=ORACLE), "[DONE]"))
        self.assertEqual(self.run_nyx("ask", self.brief, self.out).returncode, 0)
        self.assertEqual(self.out.read_text(encoding="utf-8"), "second")
        leftovers = sorted(p.name for p in self.work.iterdir())
        self.assertEqual(leftovers, sorted(["brief.md", "answer.txt", "answer.txt.status.json", "answer.txt.stream",
                                            "answer.txt.stderr", "answer.txt.request.json"]))


    # ---- terminal decision: reference conditions and reason precedence --------------------
    def assert_reason(self, stream, reason, rc=0):
        self.set_stream(stream, rc)
        completed = self.run_nyx("ask", self.brief, self.out)
        self.assertEqual(completed.returncode, 0 if reason == "COMPLETE" else 1, completed.stdout)
        self.assertEqual(self.status()["reason_code"], reason)
        self.assertEqual(self.out.exists(), reason == "COMPLETE")

    def test_the_last_reported_finish_reason_decides(self):
        cases = {
            "STREAM_NOT_TERMINAL": sse(chunk("x", finish="stop"), chunk(finish="length", oracle=ORACLE), "[DONE]"),
            "COMPLETE": sse(chunk("x", finish="length"), chunk(finish="stop", oracle=ORACLE), "[DONE]"),
        }
        for reason, stream in cases.items():
            with self.subTest(reason=reason):
                self.assert_reason(stream, reason)

    def test_only_the_final_chunk_oracle_carries_the_task_id(self):
        for final in (chunk(finish="stop"), chunk(finish="stop", oracle={"task_id": 123}),
                      chunk(finish="stop", oracle={"task_id": None})):
            with self.subTest(final=final):
                self.assert_reason(sse(chunk("x", oracle=ORACLE), final, "[DONE]"), "TASK_ID_MISSING")

    def test_an_error_key_fails_even_when_its_value_is_null(self):
        for value in (None, "", {}, False):
            with self.subTest(value=value):
                self.assert_reason(sse(chunk("x"), chunk(finish="stop", oracle=ORACLE, error=value), "[DONE]"),
                                   "BROKER_ERROR")

    def test_non_object_and_mistyped_chunks_are_malformed(self):
        bad_values = ["[1, 2]", '"text"', "7", "null",
                      json.dumps({"choices": {"delta": {}}}),
                      json.dumps({"choices": ["x"]}),
                      json.dumps({"choices": [{"delta": "x"}]}),
                      json.dumps({"choices": [{"delta": {"content": 5}}]}),
                      json.dumps({"choices": [{"delta": {}, "finish_reason": 1}]}),
                      json.dumps({"choices": [], "oracle": "task"})]
        for value in bad_values:
            with self.subTest(value=value):
                self.assert_reason(sse(chunk("x"), value, chunk(finish="stop", oracle=ORACLE), "[DONE]"),
                                   "STREAM_MALFORMED")

    def test_reason_precedence_follows_the_condition_order(self):
        malformed, error = "{not json", {"error": {"code": "model_unavailable"}}
        no_task = chunk(finish="stop")
        cases = [
            ("CARRIER_EXIT_NONZERO", sse(malformed, error), 1),
            ("STREAM_MALFORMED", sse(malformed, error, no_task), 0),
            ("BROKER_ERROR", sse(error, no_task), 0),
            ("STREAM_NOT_TERMINAL", sse(chunk("x"), no_task), 0),
            ("TASK_ID_MISSING", sse(chunk("x"), no_task, "[DONE]"), 0),
        ]
        for reason, stream, rc in cases:
            with self.subTest(reason=reason):
                self.assert_reason(stream, reason, rc)

    # ---- artifacts and inputs ------------------------------------------------------------
    def test_a_pre_dispatch_failure_removes_every_earlier_artifact(self):
        failures = {"BRIEF_INVALID": ({}, lambda: self.brief.write_bytes(b"\xff")),
                    "BROKER_UNAVAILABLE": ({"NYX_CLI": str(self.root / "absent-nyxid")}, lambda: None)}
        for reason, (env, prepare) in failures.items():
            with self.subTest(reason=reason):
                self.brief.write_text("Prove the lemma.\n", encoding="utf-8")
                self.assertEqual(self.run_nyx("ask", self.brief, self.out).returncode, 0)
                prepare()
                completed = self.run_nyx("ask", self.brief, self.out, env=env)
                self.assertEqual(completed.returncode, 1)
                self.assertEqual(self.status()["reason_code"], reason)
                self.assertEqual(sorted(p.name for p in self.work.iterdir()), ["answer.txt.status.json", "brief.md"])

    def test_relative_cli_path_is_anchored_at_the_invocation_directory(self):
        completed = self.run_nyx("ask", self.brief, self.out, cwd=self.root, env={"NYX_CLI": "fake dir/nyxid"})
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        self.assertEqual(self.out.read_text(encoding="utf-8"), "Hello, world.")

    def test_brief_named_like_a_temporary_file_survives(self):
        for name in ("answer.txt.tmp", "answer.txt.status.json.tmp"):
            with self.subTest(name=name):
                brief = self.work / name
                brief.write_text("Prove the lemma.\n", encoding="utf-8")
                self.assertEqual(self.run_nyx("ask", brief, self.out).returncode, 0)
                self.assertEqual(brief.read_text(encoding="utf-8"), "Prove the lemma.\n")
                brief.unlink()


if __name__ == "__main__":
    unittest.main()
