using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FaultInjectionTests
{
    [Fact]
    public void MissingCatalogEntryCannotProduceCompletedRuleSet()
    {
        var catalog = RuleCatalog.CreateForTesting(
            RuleCatalog.Default.Descriptors[..^1]
                .Select(static descriptor => new RuleRegistration(descriptor, new NoOpRule()))
                .ToImmutableArray());

        var outcome = catalog.Execute(new RuleFixture().Build());

        Assert.IsType<RuleExecutionOutcome.InfrastructureFailure>(outcome);
    }

    [Fact]
    public void ThrowingRuleCannotProduceCompletedRuleSet()
    {
        var registrations = RuleCatalog.Default.Descriptors
            .Select(descriptor => new RuleRegistration(
                descriptor,
                descriptor.Id == RuleId.CreateKnown(6)
                    ? new ThrowingRule()
                    : new NoOpRule()))
            .ToImmutableArray();
        var catalog = RuleCatalog.CreateForTesting(registrations);

        var outcome = catalog.Execute(new RuleFixture().Build());

        var failure = Assert.IsType<RuleExecutionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("injected", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingLeanReportIsInfrastructureWhileInspectionFailureReachesRules()
    {
        var fixture = new RuleFixture();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(fixture.Files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value))))).Snapshot;
        var missing = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>());

        // Both cases below must reach the malformed/unknown-axiom branches, so every other managed
        // Lean file still needs a well-formed entry — a report missing any of them short-circuits
        // to InfrastructureFailure first. Deriving the base from fixture.Reports keeps that true as
        // the fixture grows; naming one path here is what silently disabled this assertion when
        // ValuesBinding.lean was added.
        var malformed = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(fixture.Reports, StringComparer.Ordinal)
            {
                [RuleFixture.RingPath] = new(
                    ImmutableArray<string>.Empty,
                    ImmutableArray<LeanDeclaration>.Empty,
                    "malformed trusted report"),
            });
        var unknownAxiom = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(fixture.Reports, StringComparer.Ordinal)
            {
                [RuleFixture.RingPath] = new(
                    ImmutableArray<string>.Empty,
                    ImmutableArray.Create(new LeanDeclaration(
                        "invented",
                        "axiom",
                        "False",
                        ImmutableArray.Create("invented")))),
            });

        Assert.IsType<LeanValidationOutcome.InfrastructureFailure>(LeanClosureValidator.Validate(snapshot, missing));
        Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(snapshot, malformed));
        Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(snapshot, unknownAxiom));
    }

    [Fact]
    public void RegisteredAxiomDebtClosureIsAccepted()
    {
        const string debtPath = "D5/X_Assumptions/AxiomDebt.lean";
        const string consumerPath = "D5/X_Certificates/ConditionalResult.lean";
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(new[]
            {
                RawRepositoryEntry.FromText(debtPath, "axiom registeredDebt : False\n"),
                RawRepositoryEntry.FromText(
                    consumerPath,
                    "import D5.X_Assumptions.AxiomDebt\n\ntheorem conditionalResult : False := registeredDebt\n"),
            }))).Snapshot;
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            [debtPath] = new(
                ImmutableArray<string>.Empty,
                ImmutableArray.Create(new LeanDeclaration(
                    "registeredDebt",
                    "axiom",
                    "False",
                    ImmutableArray.Create("registeredDebt")))),
            [consumerPath] = new(
                ImmutableArray.Create("D5.X_Assumptions.AxiomDebt"),
                ImmutableArray.Create(new LeanDeclaration(
                    "conditionalResult",
                    "theorem",
                    "False",
                    ImmutableArray.Create("registeredDebt")))),
        });

        Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(snapshot, report));
    }

    [Fact]
    public void BoundedProcessSurfacesNonzeroAndTimeout()
    {
        var nonzero = TestProcessRunner.Run(
            "/usr/bin/false",
            Array.Empty<string>(),
            "/tmp",
            TestBudgets.LocalProcessHangGuard,
            1024);

        Assert.NotEqual(0, nonzero.ExitCode);
        Assert.Throws<TimeoutException>(() => BoundedProcessRunner.Run(
            "/bin/sleep",
            new[] { "2" },
            "/tmp",
            TestBudgets.ZeroDuration,
            1024));
    }

    [Fact]
    public void BoundedProcessFeedsExactStandardInputBytes()
    {
        var expected = Encoding.UTF8.GetBytes("base-owned replay envelope\n");

        var output = TestProcessRunner.Run(
            "/bin/cat",
            Array.Empty<string>(),
            "/tmp",
            TestBudgets.LocalProcessHangGuard,
            1024,
            expected);

        Assert.Equal(0, output.ExitCode);
        Assert.Equal(expected, output.StandardOutput);
        Assert.Empty(output.StandardError);
    }

    [Fact]
    public void OutputFailureCannotReturnSuccess()
    {
        var admitted = CreateAdmission();
        var exit = CliApplication.Run(
            new[] { "check" },
            new StubCliEnvironment(admitted),
            new ThrowingConsole());

        Assert.NotEqual(0, exit);
    }

    private static AdmissionOutcome CreateAdmission()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context));
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));
        return AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed.Capability,
            context.MetaEvaluation);
    }
}

internal sealed class NoOpRule : IRepositoryRule
{
    public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => true;

    public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
        ImmutableArray<RuleFinding>.Empty;
}

internal sealed class ThrowingRule : IRepositoryRule
{
    public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) => true;

    public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
        throw new InvalidOperationException("injected rule failure");
}

internal sealed class ThrowingConsole : ICliConsole
{
    public void WriteOutput(string value) => throw new IOException("injected output failure");

    public void WriteError(string value) => throw new IOException("injected output failure");
}
