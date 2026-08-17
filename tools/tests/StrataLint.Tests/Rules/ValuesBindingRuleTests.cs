using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ValuesBindingRuleTests
{
    private static readonly ImmutableArray<string> StandardAxioms =
        ["Classical.choice", "Quot.sound", "propext"];

    [Fact]
    public void TamperedStatementSha256IsRejectedBySl018()
    {
        var fixture = Fixture();
        fixture.Changes.Clear();
        fixture.Changes.Add(ValuesKernelBindingValidator.RelativePath);
        var text = fixture.Files[ValuesKernelBindingValidator.RelativePath];
        var valueStart = text.IndexOf("lean_statement_sha256 = \"", StringComparison.Ordinal)
            + "lean_statement_sha256 = \"".Length;
        fixture.Files[ValuesKernelBindingValidator.RelativePath] = string.Concat(
            text.AsSpan(0, valueStart),
            text[valueStart] == '0' ? "1" : "0",
            text.AsSpan(valueStart + 1));

        var diagnostics = Evaluate(fixture);

        Assert.Contains(diagnostics, static diagnostic =>
            diagnostic.Path == ValuesKernelBindingValidator.RelativePath
            && diagnostic.Message.Contains("D5/S0/Carrier/ValuesBinding.fixtureValue", StringComparison.Ordinal)
            && diagnostic.Message.Contains("statement SHA-256 mismatch", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl018DoesNotReplayCommittedStatementIdsForAnUnrelatedCandidateDelta()
    {
        var fixture = Fixture();
        var text = fixture.Files[ValuesKernelBindingValidator.RelativePath];
        var valueStart = text.IndexOf("lean_statement_sha256 = \"", StringComparison.Ordinal)
            + "lean_statement_sha256 = \"".Length;
        fixture.Files[ValuesKernelBindingValidator.RelativePath] = string.Concat(
            text.AsSpan(0, valueStart),
            text[valueStart] == '0' ? "1" : "0",
            text.AsSpan(valueStart + 1));
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create(["notes/unrelated.txt"]))));

        Assert.DoesNotContain(
            completed.Capability.Diagnostics,
            static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(18));
    }

    [Fact]
    public void ChangedLeanInputStillRevalidatesItsStoredSl018Binding()
    {
        var fixture = Fixture();
        fixture.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport(
            [],
            [Declaration(kind: "theorem")]);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(
                RawChangeSet.Create([RuleFixture.ValuesBindingPath]))));

        Assert.Contains(
            completed.Capability.Diagnostics,
            static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(18)
                && diagnostic.Message.Contains("expected kind=def, found theorem", StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedLeanToolchainWakesSl018ForItsStoredBinding()
    {
        var fixture = Fixture();
        fixture.Files["lean-toolchain"] = "leanprover/lean4:v4.25.0\n";
        fixture.Baseline["lean-toolchain"] = "leanprover/lean4:v4.24.0\n";
        fixture.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport(
            [],
            [Declaration(kind: "theorem")]);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(
                RawChangeSet.Create(["lean-toolchain"]))));

        Assert.Contains(
            completed.Capability.Diagnostics,
            static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(18)
                && diagnostic.Message.Contains("expected kind=def, found theorem", StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedLeanReportDefinitionWakesAndRevalidatesItsStoredSl018Binding()
    {
        var fixture = Fixture();
        fixture.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport(
            [],
            [Declaration(kind: "theorem")]);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(
                RawChangeSet.Create(["Directory.Build.props"]))));

        Assert.Contains(
            completed.Capability.Diagnostics,
            static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(18)
                && diagnostic.Message.Contains("expected kind=def, found theorem", StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedTransitiveLeanImportWakesAndRevalidatesItsStoredSl018Binding()
    {
        var fixture = Fixture();
        fixture.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport(
            ["D5.S0.Carrier.Ring"],
            [Declaration(kind: "theorem")]);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(
                RawChangeSet.Create([RuleFixture.RingPath]))));

        Assert.Contains(
            completed.Capability.Diagnostics,
            static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(18)
                && diagnostic.Message.Contains("expected kind=def, found theorem", StringComparison.Ordinal));
    }

    [Fact]
    public void MissingOrAmbiguousGidIsRejectedBySl018()
    {
        var missing = Fixture();
        missing.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport([], []);
        Assert.Contains(Evaluate(missing), static diagnostic =>
            diagnostic.Message.Contains("GID matched 0 declarations", StringComparison.Ordinal));

        var ambiguous = Fixture();
        ambiguous.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport(
            [],
            [Declaration(), Declaration()]);
        Assert.Contains(Evaluate(ambiguous), static diagnostic =>
            diagnostic.Message.Contains("GID matched 2 declarations", StringComparison.Ordinal));
    }

    [Fact]
    public void NonDefinitionOrNonExactStandardAxiomClosureIsRejectedBySl018()
    {
        var wrongKind = Fixture();
        wrongKind.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport(
            [],
            [Declaration(kind: "theorem")]);
        Assert.Contains(Evaluate(wrongKind), static diagnostic =>
            diagnostic.Message.Contains("expected kind=def, found theorem", StringComparison.Ordinal));

        var wrongAxioms = Fixture();
        wrongAxioms.Reports[RuleFixture.ValuesBindingPath] = new LeanFileReport(
            [],
            [Declaration(axioms: ["Classical.choice", "Quot.sound"])]);
        Assert.Contains(Evaluate(wrongAxioms), static diagnostic =>
            diagnostic.Message.Contains("axiom closure mismatch", StringComparison.Ordinal));
    }

    private static RuleFixture Fixture()
    {
        var fixture = new RuleFixture();
        fixture.Changes.Clear();
        fixture.Changes.Add(ValuesKernelBindingValidator.RelativePath);
        return fixture;
    }

    private static ImmutableArray<Diagnostic> Evaluate(RuleFixture fixture)
    {
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build()));
        return completed.Capability.Diagnostics
            .Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(18))
            .ToImmutableArray();
    }

    private static LeanDeclaration Declaration(
        string kind = "def",
        ImmutableArray<string>? axioms = null) =>
        new("fixtureValue", kind, "Nat", axioms ?? StandardAxioms);

}
