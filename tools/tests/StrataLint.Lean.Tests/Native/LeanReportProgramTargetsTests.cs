using System.Text;
using System.Text.Json;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanReportProgramTargetsTests
{
    [Theory]
    [InlineData("valid", "both", 0, 0,
        "ensure|build leanInspector/LeanInformationAudit leanInspector/reportInspector", true, true, null)]
    [InlineData("valid", "audit", 42, 42,
        "ensure|build leanInspector/LeanInformationAudit", false, false, null)]
    [InlineData("missing", "both", 42, 42,
        "ensure|build :report leanInspector/LeanInformationAudit leanInspector/reportInspector", false, false, null)]
    [InlineData("valid", "none", 0, 0, "", true, true, null)]
    [InlineData("corrupt", "audit", 42, 42,
        "ensure|build :report leanInspector/LeanInformationAudit", false, false, null)]
    [InlineData("valid", "invalid", 0, 2, "", false, true, "lean_targets requires", true)]
    [InlineData("valid", "invalid", 0, 2, "", false, false, "lean_targets requires")]
    [InlineData("valid", "malformed", 0, 2, "", false, true, "JSONDecodeError", true)]
    [InlineData("valid", "non-list", 0, 2, "", false, true, "lean_targets requires", true)]
    [InlineData("valid", "invalid-registered", 0, 2, "", false, true, "lean_targets requires", true)]
    [InlineData("valid", "registered", 0, 0, "ensure|build FixtureAudit", true, true, null)]
    [InlineData("valid", "both", 0, 0,
        "ensure|build leanInspector/LeanInformationAudit leanInspector/reportInspector", true, true, null, true)]
    [InlineData("valid", "none", 0, 0, "", true, true, null, true)]
    [InlineData("valid", "audit", 42, 42, "ensure|build leanInspector/LeanInformationAudit", false, true, null, true)]
    [InlineData("corrupt", "audit", 42, 42,
        "ensure|build :report leanInspector/LeanInformationAudit", false, true, null, true)]
    public void ReportEntryHonorsRegisteredProgramObligations(
        string seed, string selection, int buildExit, int expectedExit,
        string expectedCalls, bool receiptExists, bool identicalReports, string? error,
        bool existingOutput = false)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import json, pathlib, sys
            repository, seed, selection, build_exit, existing_output = sys.argv[1:]
            sys.path.insert(0, str(pathlib.Path(repository) / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            import publication
            fixture = ReuseTests()
            fixture.setUp()
            try:
                targets = {
                    'both': ['leanInspector/LeanInformationAudit', 'leanInspector/reportInspector'],
                    'audit': ['leanInspector/LeanInformationAudit'], 'none': [],
                    'invalid': ['--invalid-build-option'], 'registered': None,
                    'malformed': '[', 'non-list': '{}', 'invalid-registered': None,
                }[selection]
                process, calls = fixture.entry_with_program_build(targets,
                    seed=False if seed == 'missing' else seed, build_exit=int(build_exit),
                    existing_output=existing_output == 'True',
                    registered_targets=['--invalid-build-option'] if selection == 'invalid-registered'
                        else ['FixtureAudit'])
                print(json.dumps(dict(exit=process.returncode, stdout=process.stdout,
                    stderr=process.stderr, calls=calls, lake=str(fixture.lake),
                    workspace=str((fixture.root / 'Reg').resolve()),
                    receipt_exists=publication.member(fixture.output, '.reuse.json').is_file(),
                    seed_unchanged=all(path.read_bytes() == before
                        for path, before in fixture.seed_before.items()),
                    identical_reports=fixture.output.is_file() and
                        fixture.output.read_bytes() == fixture.report.read_bytes())))
            finally:
                fixture.doCleanups()
            """, root, seed, selection, buildExit.ToString(System.Globalization.CultureInfo.InvariantCulture),
                existingOutput.ToString()],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.True(result.ExitCode == 0, text + Encoding.UTF8.GetString(result.StandardError));
        using var outcome = JsonDocument.Parse(text);
        var value = outcome.RootElement;
        Assert.True(expectedExit == value.GetProperty("exit").GetInt32(),
            value.GetProperty("stdout").GetString() + value.GetProperty("stderr").GetString());
        var lake = value.GetProperty("lake").GetString();
        var workspace = value.GetProperty("workspace").GetString();
        var calls = expectedCalls.Length == 0 ? [] : expectedCalls.Split('|')
            .Select(call => call == "ensure" ? call : lake + " -d " + workspace + " " + call).ToArray();
        Assert.Equal(calls, value.GetProperty("calls").EnumerateArray().Select(call => call.GetString()));
        Assert.True(value.GetProperty("seed_unchanged").GetBoolean(), text);
        Assert.True(receiptExists == value.GetProperty("receipt_exists").GetBoolean(),
            "[FAIL] canonical_receipt_state: " + text);
        if (identicalReports) Assert.True(value.GetProperty("identical_reports").GetBoolean());
        if (error is not null)
            Assert.Contains(error, value.GetProperty("stderr").GetString(), StringComparison.Ordinal);
    }
}
