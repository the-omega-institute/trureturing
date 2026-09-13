namespace StrataLint.Tests;

public sealed partial class InspectorSourceModeTests
{
    private const string Selection = """
        previous = json.loads(Path(str(output) + ".provenance.json").read_text())
        previous_entry = Path(env["STRATALINT_REPORT_CACHE_ROOT"]) / previous["input_address"][7:]
        assert previous_entry.is_dir()
        expected = ["D5.Dependent", "D5.Probe", "D5.Unrelated", "Trureturing"]
        def inspector_calls():
            return [row for row in map(json.loads, calls.read_text().splitlines())
                if any(a.endswith("/Inspector.lean") for a in row)]
        assert len(inspector_calls()) == 1
        write("D5/Probe.lean", source + "-- changed declared input\n")
        changed = run(command)
        rows = inspector_calls()
        assert len(rows) == 2, (changed.stdout, changed.stderr, rows)
        args = rows[-1]
        selected = args[args.index("--utility-input") + 2::3]
        # Observe actual Inspector argv. Cached imports and the claim edge would
        # select only Probe, Dependent and Trureturing on the replaced path.
        assert sorted(selected) == expected, ("DECLARED_INSPECTION_NARROWED", selected, expected,
            changed.stdout, changed.stderr)
        assert changed.returncode == 0, (changed.stdout, changed.stderr)
        current = json.loads(Path(str(output) + ".provenance.json").read_text())
        assert current["input_address"] != previous["input_address"]
        for key in ("producer_sha256", "repository_inspector_sha256", "lean_config_sha256"):
            assert current[key] == previous[key], (key, previous, current)
        assert previous_entry.is_dir(), "the compatible prior entry must remain available to the producer"
        assert [m["module"] for m in json.loads(output.read_text())["modules"]] == expected
        refreshed_context = Path(str(output) + ".source-context.json").read_bytes()
        with zipfile.ZipFile(str(output) + ".materials.zip") as z:
            assert z.read("source-context.json") == refreshed_context
        exact = run(command)
        assert exact.returncode == 0 and "mode=cached" in exact.stdout, (exact.stdout, exact.stderr)
        assert len(inspector_calls()) == 2
        (scratch / "selection-result.json").write_text(json.dumps(dict(
            argv=command, cwd=str(root), cache_root=env["STRATALINT_REPORT_CACHE_ROOT"],
            previous_provenance=previous, current_provenance=current, selected=selected,
            changed_exit=changed.returncode, changed_stdout=changed.stdout, changed_stderr=changed.stderr,
            exact_exit=exact.returncode, declaration_inspector_executions=2), indent=2))
        """;
}
