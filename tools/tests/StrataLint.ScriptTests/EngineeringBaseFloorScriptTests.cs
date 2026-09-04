using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EngineeringBaseFloorScriptTests
{
    private static readonly UTF8Encoding Utf8 = new(false);

    [Fact]
    public void RejectsMissingRequiredAssembly()
    {
        using var run = RunVerifier("[\"Missing.Tests\"]");

        Assert.Equal(2, run.Process.ExitCode);
        Assert.Contains(
            "ENGINEERING_BASE_FLOOR_FAILED TRX has no executed identity from required assembly Missing.Tests",
            run.StandardError,
            StringComparison.Ordinal);
    }

    [Fact]
    public void AcceptsExecutedRequiredAssembly()
    {
        using var run = RunVerifier("[\"Present.Tests\"]");

        Assert.Equal(0, run.Process.ExitCode);
        Assert.Contains(
            "ENGINEERING_BASE_FLOOR_EXECUTED assembly=Present.Tests evidence=trx executed=1",
            run.StandardOutput,
            StringComparison.Ordinal);
    }

    private static VerifierRun RunVerifier(string requiredAssemblies)
    {
        var temporary = new TemporaryDirectory();
        var results = Path.Combine(temporary.Path, "results");
        ScriptHarnessScratch.EnsureDirectory(results);
        ScriptHarnessScratch.WriteScratchText(
            Path.Combine(results, "evidence.trx"),
            """
            <TestRun>
              <ResultSummary><Counters executed="1" /></ResultSummary>
              <TestDefinitions>
                <UnitTest id="one" storage="Present.Tests.dll">
                  <TestMethod className="Fixture.Tests" name="Runs" />
                </UnitTest>
              </TestDefinitions>
              <Results><UnitTestResult testId="one" outcome="Passed" /></Results>
            </TestRun>
            """);
        var process = TestProcessRunner.Run(
            "python3",
            [
                Path.Combine(AppContext.BaseDirectory, "engineering-base-floor.py"),
                "verify",
                "--required-assemblies-json", requiredAssemblies,
                "--results-directory", results,
            ],
            temporary.Path,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        return new VerifierRun(temporary, process);
    }

    private sealed record VerifierRun(TemporaryDirectory Temporary, ProcessOutput Process)
        : IDisposable
    {
        internal string StandardOutput => Utf8.GetString(Process.StandardOutput);

        internal string StandardError => Utf8.GetString(Process.StandardError);

        public void Dispose() => Temporary.Dispose();
    }
}
