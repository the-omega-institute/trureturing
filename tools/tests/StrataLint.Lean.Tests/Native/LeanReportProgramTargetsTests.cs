using System.Text;
using System.Text.Json;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanReportProgramTargetsTests
{
    [Theory]
    [InlineData("valid", "both", 0, 0,
        "ensure|build LeanInformationAudit leanInspector/reportInspector", true, true, null)]
    [InlineData("valid", "audit", 42, 42,
        "ensure|build LeanInformationAudit", false, false, null)]
    [InlineData("missing", "both", 42, 42,
        "ensure|build :report LeanInformationAudit leanInspector/reportInspector", null, false, null)]
    [InlineData("valid", "none", 0, 0, "", null, false, null)]
    [InlineData("corrupt", "audit", 42, 42,
        "ensure|build :report LeanInformationAudit", false, false, null)]
    [InlineData("valid", "invalid", 0, 2, "", null, false, "lean_targets requires")]
    [InlineData("valid", "registered", 0, 0, "ensure|build FixtureAudit", null, false, null)]
    public void ReportEntryHonorsRegisteredProgramObligations(
        string seed, string selection, int buildExit, int expectedExit,
        string expectedCalls, bool? receiptExists, bool identicalReports, string? error)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import json, pathlib, sys
            repository, seed, selection, build_exit = sys.argv[1:]
            sys.path.insert(0, str(pathlib.Path(repository) / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            import publication
            fixture = ReuseTests()
            fixture.setUp()
            try:
                targets = {
                    'both': ['LeanInformationAudit', 'leanInspector/reportInspector'],
                    'audit': ['LeanInformationAudit'], 'none': [],
                    'invalid': ['--invalid-build-option'], 'registered': None,
                }[selection]
                process, calls = fixture.entry_with_program_build(targets,
                    seed=False if seed == 'missing' else seed, build_exit=int(build_exit))
                print(json.dumps(dict(exit=process.returncode, stdout=process.stdout,
                    stderr=process.stderr, calls=calls, lake=str(fixture.lake),
                    receipt_exists=publication.member(fixture.output, '.reuse.json').is_file(),
                    identical_reports=fixture.output.is_file() and
                        fixture.output.read_bytes() == fixture.report.read_bytes())))
            finally:
                fixture.doCleanups()
            """, root, seed, selection, buildExit.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.True(result.ExitCode == 0, text + Encoding.UTF8.GetString(result.StandardError));
        using var outcome = JsonDocument.Parse(text);
        var value = outcome.RootElement;
        Assert.True(expectedExit == value.GetProperty("exit").GetInt32(),
            value.GetProperty("stdout").GetString() + value.GetProperty("stderr").GetString());
        var lake = value.GetProperty("lake").GetString();
        var calls = expectedCalls.Length == 0 ? [] : expectedCalls.Split('|')
            .Select(call => call == "ensure" ? call : lake + " " + call).ToArray();
        Assert.Equal(calls, value.GetProperty("calls").EnumerateArray().Select(call => call.GetString()));
        if (receiptExists is { } expectedReceipt)
            Assert.Equal(expectedReceipt, value.GetProperty("receipt_exists").GetBoolean());
        if (identicalReports) Assert.True(value.GetProperty("identical_reports").GetBoolean());
        if (error is not null)
            Assert.Contains(error, value.GetProperty("stderr").GetString(), StringComparison.Ordinal);
    }
}
