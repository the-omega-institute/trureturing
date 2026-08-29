using StrataLint.Engine;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class ProcessCapabilityDebtPolicyTests
{
    private const string OldPath = "tools/tests/StrataLint.Tests/OldDebtTests.cs";
    private const string NewPath = "tools/tests/StrataLint.Tests/NewTests.cs";

    [Fact]
    public void ByteIdenticalBaselineBlobMayCarryInheritedDebt()
    {
        var baseline = Snapshot((OldPath, "class OldDebt { void Run() { Legacy(); } }"));
        var diagnostic = Diagnostic(OldPath, 1, 36, "T:StrataLint.Tests.TestProcessRunner");

        Assert.Empty(ProcessCapabilityDebtPolicy.EvaluateDebt(
            baseline,
            baseline,
            [diagnostic],
            [diagnostic],
            wiringChanged: false));
    }

    [Fact]
    public void EqualSwapRejectsTheCandidateNewIdentity()
    {
        var baseline = Snapshot((OldPath, "class OldDebt { void Run() { Legacy(); } }"));
        var current = Snapshot(
            (OldPath, "class OldDebt { void Run() { } }"),
            (NewPath, "class NewTests { void Run() { Added(); } }"));
        var oldDiagnostic = Diagnostic(OldPath, 1, 36, "T:StrataLint.Tests.TestProcessRunner");
        var newDiagnostic = Diagnostic(NewPath, 1, 35, "T:System.Diagnostics.Process");

        var finding = Assert.Single(ProcessCapabilityDebtPolicy.EvaluateDebt(
            current,
            baseline,
            [newDiagnostic],
            [oldDiagnostic],
            wiringChanged: false));

        Assert.Equal(NewPath, finding.Path);
        Assert.Contains("candidate-new", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ChangedDebtBlobMustClearEveryDiagnostic()
    {
        var baseline = Snapshot((OldPath, "class OldDebt { void Run() { Legacy(); } }"));
        var current = Snapshot((OldPath, "class OldDebt { void Run() { Legacy(); More(); } }"));
        var diagnostic = Diagnostic(OldPath, 1, 36, "T:StrataLint.Tests.TestProcessRunner");

        var finding = Assert.Single(ProcessCapabilityDebtPolicy.EvaluateDebt(
            current,
            baseline,
            [diagnostic],
            [diagnostic],
            wiringChanged: false));

        Assert.Equal(OldPath, finding.Path);
        Assert.Contains("byte-identical", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ClearingATouchedDebtBlobStrictlyDescends()
    {
        var baseline = Snapshot((OldPath, "class OldDebt { void Run() { Legacy(); } }"));
        var current = Snapshot((OldPath, "class OldDebt { void Run() { } }"));

        Assert.Empty(ProcessCapabilityDebtPolicy.EvaluateDebt(
            current,
            baseline,
            [],
            [Diagnostic(OldPath, 1, 36, "T:StrataLint.Tests.TestProcessRunner")],
            wiringChanged: false));
    }

    [Fact]
    public void EmptyBaselineAutomaticallyAppliesTheBanToTheWholeTree()
    {
        var baseline = Snapshot((NewPath, "class NewTests { void Run() { } }"));
        var current = Snapshot((NewPath, "class NewTests { void Run() { Added(); } }"));

        var finding = Assert.Single(ProcessCapabilityDebtPolicy.EvaluateDebt(
            current,
            baseline,
            [Diagnostic(NewPath, 1, 35, "T:System.Diagnostics.Process")],
            [],
            wiringChanged: false));

        Assert.Equal(NewPath, finding.Path);
        Assert.Contains("candidate-new", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DuplicateCompilerLinesAreGroupedWithoutCrashing()
    {
        var snapshot = Snapshot((OldPath, "class OldDebt { void Run() { Legacy(); } }"));
        var diagnostic = Diagnostic(OldPath, 1, 36, "T:StrataLint.Tests.TestProcessRunner");

        Assert.Empty(ProcessCapabilityDebtPolicy.EvaluateDebt(
            snapshot,
            snapshot,
            [diagnostic, diagnostic],
            [diagnostic, diagnostic],
            wiringChanged: false));
    }

    [Fact]
    public void WiringChangesFailClosedWhileBaselineDebtRemains()
    {
        var snapshot = Snapshot((OldPath, "class OldDebt { void Run() { Legacy(); } }"));
        var diagnostic = Diagnostic(OldPath, 1, 36, "T:StrataLint.Tests.TestProcessRunner");

        var finding = Assert.Single(ProcessCapabilityDebtPolicy.EvaluateDebt(
            snapshot,
            snapshot,
            [diagnostic],
            [diagnostic],
            wiringChanged: true));

        Assert.Equal(ProcessCapabilityDebtPolicy.WiringPath, finding.Path);
        Assert.Contains("wiring changed", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WiringMayChangeAfterBaselineDebtReachesZero()
    {
        var snapshot = Snapshot((NewPath, "class NewTests { void Run() { } }"));

        Assert.Empty(ProcessCapabilityDebtPolicy.EvaluateDebt(
            snapshot,
            snapshot,
            [],
            [],
            wiringChanged: true));
    }

    [Fact]
    public void Sl003CallsTheProcessCapabilityRatchet()
    {
        var source = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
            "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs"));

        Assert.Contains("ProcessCapabilityDebtPolicy.Evaluate", source, StringComparison.Ordinal);
    }

    private static ProcessCapabilityDiagnostic Diagnostic(
        string path,
        int line,
        int column,
        string symbol) => new(path, line, column, symbol, $"The symbol '{symbol}' is banned");

    private static RepositorySnapshot Snapshot(params (string Path, string Content)[] files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static file =>
            RawRepositoryEntry.FromText(file.Path, file.Content)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }
}
