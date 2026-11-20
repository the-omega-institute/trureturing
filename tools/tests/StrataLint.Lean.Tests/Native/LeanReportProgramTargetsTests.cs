using System.Text;
using System.Text.Json;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanReportProgramTargetsTests
{
    [Theory]
    [InlineData("valid", 0, true, false)]
    [InlineData("valid", 0, true, true)]
    [InlineData("missing", 42, false, false)]
    [InlineData("corrupt", 42, false, true)]
    public void FullReportOnlyRequestsReportExtractionOnMiss(
        string seed, int expectedExit, bool receiptExists, bool existingOutput)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import json, pathlib, sys
            repository, seed, existing_output = sys.argv[1:]
            sys.path.insert(0, str(pathlib.Path(repository) / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            import publication
            fixture = ReuseTests()
            fixture.setUp()
            try:
                process, calls = fixture.entry_with_program_build(
                    ['leanInspector/reportInspector'], seed=False if seed == 'missing' else seed,
                    build_exit=42, existing_output=existing_output == 'True')
                print(json.dumps(dict(exit=process.returncode, stdout=process.stdout,
                    stderr=process.stderr, calls=calls, lake=str(fixture.lake),
                    workspace=str((fixture.root / 'tools/lean-inspector-reg').resolve()),
                    receipt_exists=publication.member(fixture.output, '.reuse.json').is_file(),
                    seed_unchanged=all(path.read_bytes() == before
                        for path, before in fixture.seed_before.items()),
                    identical_reports=fixture.output.is_file() and
                        fixture.output.read_bytes() == fixture.report.read_bytes())))
            finally:
                fixture.doCleanups()
            """, root, seed, existingOutput.ToString()],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.True(result.ExitCode == 0, text + Encoding.UTF8.GetString(result.StandardError));
        using var outcome = JsonDocument.Parse(text);
        var value = outcome.RootElement;
        Assert.True(expectedExit == value.GetProperty("exit").GetInt32(),
            value.GetProperty("stdout").GetString() + value.GetProperty("stderr").GetString());
        var lake = value.GetProperty("lake").GetString();
        var workspace = value.GetProperty("workspace").GetString();
        string[] calls = seed == "valid" ? [] : ["--prebuilt " + lake + " --log-level=error -d " + workspace + " build :report"];
        Assert.Equal(calls, value.GetProperty("calls").EnumerateArray().Select(call => call.GetString()));
        Assert.True(value.GetProperty("seed_unchanged").GetBoolean(), text);
        Assert.True(receiptExists == value.GetProperty("receipt_exists").GetBoolean(),
            "[FAIL] canonical_receipt_state: " + text);
        if (seed == "valid") Assert.True(value.GetProperty("identical_reports").GetBoolean());
    }
}
