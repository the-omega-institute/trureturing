using StrataLint.Tests;
using StrataLint.EngineeringScope;

namespace StrataLint.ArchitectureTests;

public sealed class BannedApiCoverageTests
{
    [Fact]
    public void CompileFailProofMarksEveryExpectedDiagnosticLine()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools", "tests", "BannedApiCompileFailProof",
            "BannedApiViolations.cs");

        Assert.Equal(27, File.ReadLines(path).Count(static line =>
            line.Contains("// banned-api-proof", StringComparison.Ordinal)));
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
        var source = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs"));
        var diagnostics = source.Split('\n').Select((line, index) => (line, index))
            .Where(item => item.line.Contains("// banned-api-proof", StringComparison.Ordinal))
            .Select(item => $"BannedApiViolations.cs({item.index + 1},1): error RS0030: forbidden symbol").ToArray();
        var output = string.Join('\n', diagnostics);
        Assert.True(CompilationProof.ValidateBannedApi(1, output, source));
        Assert.False(CompilationProof.ValidateBannedApi(0, output, source));
        Assert.False(CompilationProof.ValidateBannedApi(1, string.Join('\n', diagnostics.Skip(1)), source));
        Assert.False(CompilationProof.ValidateBannedApi(1, output + "\nproject: error MSB1009: missing project", source));
    }
}
