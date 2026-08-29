using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class BannedApiCoverageTests
{
    [Fact]
    public void CompileFailProofMarksEveryExpectedDiagnosticLine()
    {
        var existingProof = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"));

        Assert.Equal(31, existingProof.Split('\n')
            .Count(static line => line.Contains("// banned-api-proof", StringComparison.Ordinal)));
    }

    [Fact]
    public void ProcessCapabilityBanNamesOnlyTheUnitProcessSurface()
    {
        var source = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "tools/Architecture/BannedSymbols.ProcessCapability.txt"));
        var symbols = source.Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(static line => line.Split(';', 2)[0])
            .ToHashSet(StringComparer.Ordinal);

        Assert.True(symbols.SetEquals(new[]
        {
            "T:System.Diagnostics.Process",
            "T:System.Diagnostics.ProcessStartInfo",
            "T:StrataLint.Engine.BoundedProcessRunner",
            "T:StrataLint.Tests.TestProcessRunner",
        }));
        Assert.DoesNotContain(symbols, static symbol => symbol.StartsWith("M:System.IO.", StringComparison.Ordinal));
    }

    [Fact]
    public void DeterminismBanNamesEveryWallClockAndDelaySymbol()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools", "Architecture", "BannedSymbols.Determinism.txt");
        var entries = File.ReadAllLines(path).ToHashSet(StringComparer.Ordinal);

        Assert.All(new[]
        {
            "M:System.Threading.Thread.Sleep(System.Int32);Use an injected synchronization primitive outside deterministic tests.",
            "M:System.Threading.Thread.Sleep(System.TimeSpan);Use an injected synchronization primitive outside deterministic tests.",
            "M:System.Threading.Tasks.Task.Delay(System.Int32);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.Int32,System.Threading.CancellationToken);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.Threading.CancellationToken);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.TimeProvider);Use virtual time or an injected synchronization primitive.",
            "M:System.Threading.Tasks.Task.Delay(System.TimeSpan,System.TimeProvider,System.Threading.CancellationToken);Use virtual time or an injected synchronization primitive.",
        }, entry => Assert.Contains(entry, entries));
        Assert.Contains(
            "T:System.Diagnostics.Stopwatch;Do not make test verdicts or diagnostics depend on machine speed.",
            entries);
    }

    [Fact]
    public void PreflightComparesEveryMarkedLineWithAnRs0030Diagnostic()
    {
        var preflight = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/preflight.sh"));

        Assert.Contains("expected_lines+=(\"$line\")", preflight, StringComparison.Ordinal);
        Assert.Contains("actual_lines+=(\"$line\")", preflight, StringComparison.Ordinal);
        Assert.Contains("error RS0030", preflight, StringComparison.Ordinal);
        Assert.Contains(
            "test \"${#actual_lines[@]}\" -eq \"${#expected_lines[@]}\"",
            preflight,
            StringComparison.Ordinal);
    }
}
