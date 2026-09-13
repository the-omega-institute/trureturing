namespace StrataLint.Tests;

public sealed partial class InspectorSourceModeTests
{
    // Only the downstream mutating commands are adapters. Public Make/script
    // routing, source identity, report capture and demanded-context validation
    // execute the candidate programs, with no source environment patched in.
    private const string LocalConsumers = """
        public_results = scratch / "public-results.jsonl"
        env.update(FIXTURE_PUBLIC_CONSUMERS="1", FIXTURE_PUBLIC_RESULTS=str(public_results))
        canonical = root / ".lake/build/stratalint/raw-lean-report.json"
        canonical.parent.mkdir(parents=True, exist_ok=True)
        for suffix in ("", ".input.attestation", ".provenance.json", ".materials.zip", ".source-context.json"):
            shutil.copyfile(str(output) + suffix, str(canonical) + suffix)
        Path(str(canonical) + ".sha256").write_text(hashlib.sha256(canonical.read_bytes()).hexdigest()
            + "  " + canonical.name + "\n")
        consumer = str(root / "tools/scripts/report/report-consumer.sh")
        reached = [sys.executable, "-c", 'import os; print("CONSUMER_REACHED " + os.environ["STRATALINT_SOURCE_BASE"])']
        public = [consumer, "--role", "public-fixture", "--report", str(canonical)]
        base_env = env.copy()
        observations = []
        def public_run(label, argv, expected=0, updates=None):
            environment = base_env.copy()
            environment.pop("BASE", None)
            environment.update(updates or {})
            result = subprocess.run(argv, cwd=root, env=environment, text=True, capture_output=True)
            observations.append(dict(label=label, argv=argv, cwd=str(root),
                source_environment={name:environment.get(name) for name in
                    ("BASE", "STRATALINT_SOURCE_BASE", "STRATALINT_PUSH_BEFORE", "STRATALINT_PUSH_HEAD")},
                exit_code=result.returncode, stdout=result.stdout, stderr=result.stderr))
            assert result.returncode == expected, (label, result.returncode, result.stdout, result.stderr)
            return result
        # Missing and conflicting modes cannot be repaired by peeking past --.
        for label, args, updates in (
            ("missing", [], {}),
            ("empty", ["--base", ""], {}),
            ("empty-BASE-environment", [], {"BASE":""}),
            ("zero", ["--base", "0" * 40], {}),
            ("conflicting", ["--base", before], {"STRATALINT_SOURCE_BASE":head}),
            ("partial-push", ["--push-before", before], {}),
            ("both-modes", ["--base", before, "--push-before", before, "--push-head", head], {}),
        ):
            rejected = public_run(label, [*public, *args, "--", *reached], 2, updates)
            assert "CONSUMER_REACHED" not in rejected.stdout
        rejected = public_run("base-after-separator", [*public, "--", *reached, "--base", before], 2)
        assert "CONSUMER_REACHED" not in rejected.stdout
        public_run("make-emit-missing-source", ["make", "emit"], 2)
        public_run("make-emit-empty-base", ["make", "emit", "BASE="], 2)
        public_run("make-emit-zero-base", ["make", "emit", "BASE=" + "0" * 40], 2)
        for label, args, updates in (
            ("consumer-base-argument", ["--base", before], {}),
            ("consumer-normalizes-explicit-base", ["--base", "HEAD~2"], {}),
            ("consumer-BASE-environment", [], {"BASE":before}),
            ("consumer-source-environment", [], {"STRATALINT_SOURCE_BASE":before}),
        ):
            accepted = public_run(label, [*public, *args, "--", *reached], updates=updates)
            assert "CONSUMER_REACHED " + before in accepted.stdout
        public_run("make-emit-source-environment", ["make", "emit"], updates={"STRATALINT_SOURCE_BASE":before})
        push_reached = [sys.executable, "-c", 'import os; print("PUSH_REACHED " + os.environ["STRATALINT_PUSH_BEFORE"] + " " + os.environ["STRATALINT_PUSH_HEAD"])']
        accepted = public_run("consumer-push-arguments", [*public, "--push-before", before, "--push-head", head,
            "--", *push_reached])
        assert "PUSH_REACHED " + before + " " + head in accepted.stdout
        public_run("make-emit-push-environment", ["make", "emit"], updates={"STRATALINT_PUSH_BEFORE":before,
            "STRATALINT_PUSH_HEAD":head})
        for label, argv in (
            ("make-emit", ["make", "emit", "BASE=" + before]),
            ("script-emit", ["bash", "tools/scripts/scribe.sh", "emit", before]),
            ("make-align", ["make", "align-digestion-status", "BASE=" + before]),
            ("script-align", ["bash", "tools/scripts/ingest.sh", "align-digestion-status", before]),
            ("make-ingest", ["make", "ingest", "BASE=" + before]),
            ("script-ingest", ["bash", "tools/scripts/ingest.sh", "ingest", before]),
            ("make-reanchor", ["make", "mathlib-reanchor", "BASE=" + before]),
            ("make-test", ["make", "test", "BASE=" + before]),
            ("make-residual", ["make", "echo-residual-summary", "BASE=" + before]),
        ):
            public_run(label, argv)
        # Direct playbook entry has no inherited make command-line BASE.
        write("Blueprint/D5/Probe.md", "fixture mirror\n")
        write("Meta/Digestion/atoms/sha256/fixture-atom", "fixture\n")
        write("Generated/truth-graph.v1.json", '{"truth":{"nodes":[]}}\n')
        public_run("make-deliver-check", ["make", "deliver-check", "BASE=" + before, "PREFLIGHT=0"])
        for label, argv in (
            ("make-deposit", ["make", "deposit", "BASE=" + before, "ATOM_ID=fixture-atom", "GID=D5/Probe.probe"]),
            ("script-deposit", ["bash", "tools/scripts/workflow/playbook-workflows.sh", "deposit", before,
                "fixture-atom", "D5/Probe.probe"]),
            ("script-deposit-uncovered", ["bash", "tools/scripts/workflow/playbook-workflows.sh", "deposit-uncovered",
                before, "D5/Probe.probe"]),
            ("script-cover", ["bash", "tools/scripts/workflow/playbook-workflows.sh", "cover", before,
                "fixture-atom", "D5/Probe.probe"]),
        ):
            public_run(label, argv)
        for row in map(json.loads, public_results.read_text().splitlines()):
            command = row["command"]
            for flag in ("--base", "--protected-base"):
                if flag in command: assert command[command.index(flag) + 1] == before, row
            if command[0] in ("emit", "align-digestion-status"):
                assert (row["source_base"], row["push_before"], row["push_head"]) in (
                    (before, "", ""), ("", before, head)), row
        # A valid report hash does not exempt missing demanded context.
        context_file = Path(str(canonical) + ".source-context.json")
        saved_context = context_file.read_bytes()
        archive = Path(str(canonical) + ".materials.zip")
        saved_archive = archive.read_bytes()
        context_file.unlink()
        with zipfile.ZipFile(archive) as z:
            entries = [(info, z.read(info)) for info in z.infolist() if info.filename != "source-context.json"]
        with zipfile.ZipFile(archive, "w") as z:
            for info, data in entries: z.writestr(info, data)
        rejected = public_run("public-missing-context", ["make", "emit", "BASE=" + before], 2)
        assert "bundle lacks demanded context" in rejected.stderr, rejected.stderr
        archive.write_bytes(saved_archive)
        context_file.write_bytes(saved_context)
        (scratch / "public-command-results.json").write_text(json.dumps(observations, indent=2))
        """;
}
