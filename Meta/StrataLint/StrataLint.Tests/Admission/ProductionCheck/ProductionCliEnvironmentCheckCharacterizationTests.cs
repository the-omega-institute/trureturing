using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string CheckUsage =
        "USAGE: StrataLint check [--protected-base REV] "
        + "--candidate-lean-report FILE --baseline-lean-report FILE "
        + "[--frozen-evidence-root DIR]";

    [Theory]
    [InlineData("--protected-base")]
    [InlineData("--merge-base")]
    public void CheckCharacterizesProtectedBaseOptionForms(string option)
    {
        using var temporary = new TemporaryDirectory();
        var fixture = ValidFixtureWithFrozenLedger();
        var reports = WriteCheckReports(temporary.Path, fixture);
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            option, "base-revision",
            "--candidate-lean-report", reports.Candidate,
            "--baseline-lean-report", reports.Baseline,
        ]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(["base-revision"], gateway.PreparedProtectedBases);
        Assert.Equal(["Prepare(base-revision)", "ReadCurrent", "ReadRevision(baseline)"], gateway.Events[..3]);
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Theory]
    [MemberData(nameof(InvalidCheckArguments))]
    public void CheckCharacterizesParserFailuresBeforeRepositoryAccess(string[] arguments)
    {
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            null,
            null);
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(arguments);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal(CheckUsage, failure.Message);
        Assert.Empty(gateway.Events);
        Assert.Equal(0, gateway.ReadCount);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Theory]
    [MemberData(nameof(MissingReportArguments))]
    public void CheckCharacterizesMissingLeanReportArgumentsAfterPrepareBeforeSnapshots(
        string[] arguments,
        string? expectedProtectedBase)
    {
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            null,
            null);
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(arguments);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal(
            "check requires --candidate-lean-report FILE and --baseline-lean-report FILE",
            failure.Message);
        Assert.Equal([expectedProtectedBase], gateway.PreparedProtectedBases);
        Assert.Equal([$"Prepare({expectedProtectedBase ?? "<null>"})"], gateway.Events);
        Assert.Equal(0, gateway.ReadCount);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckCharacterizesPreparationExceptionsAsInfrastructureFailures()
    {
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            null,
            null)
        {
            PrepareException = new InvalidOperationException("prepare exploded"),
        };
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check([]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal("prepare exploded", failure.Message);
        Assert.Equal(["Prepare(<null>)"], gateway.Events);
        Assert.Equal(0, gateway.ReadCount);
    }

    [Fact]
    public void CheckCharacterizesSnapshotExceptionsAsInfrastructureFailures()
    {
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            null,
            null)
        {
            ReadCurrentException = new IOException("current snapshot exploded"),
        };
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--candidate-lean-report", "candidate.json",
            "--baseline-lean-report", "baseline.json",
        ]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal("current snapshot exploded", failure.Message);
        Assert.Equal(["Prepare(<null>)", "ReadCurrent"], gateway.Events);
    }

    [Fact]
    public void CheckCharacterizesReportLoadingExceptionsAsInfrastructureFailures()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = ValidFixtureWithFrozenLedger();
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));
        var missingReport = Path.Combine(temporary.Path, "missing-candidate.json");

        var outcome = environment.Check(
        [
            "--candidate-lean-report", missingReport,
            "--baseline-lean-report", Path.Combine(temporary.Path, "unused-baseline.json"),
        ]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("missing-candidate.json", failure.Message, StringComparison.Ordinal);
        Assert.Equal(["Prepare(<null>)", "ReadCurrent", "ReadRevision(baseline)"], gateway.Events);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckCharacterizesScribeExceptionsAsInfrastructureFailures()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = ValidFixtureWithFrozenLedger();
        var reports = WriteCheckReports(temporary.Path, fixture);
        var verifier = new ThrowingScribeVerifier("scribe exploded");
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            gateway,
            new FakeLeanReportSource(null),
            verifier);

        var outcome = environment.Check(
        [
            "--candidate-lean-report", reports.Candidate,
            "--baseline-lean-report", reports.Baseline,
        ]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal("scribe exploded", failure.Message);
        Assert.Equal(1, verifier.CallCount);
        Assert.Equal(["Prepare(<null>)", "ReadCurrent", "ReadRevision(baseline)"], gateway.Events);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckCharacterizesFrozenLedgerExceptionsAsInfrastructureFailures()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = ValidFixtureWithFrozenLedger();
        var reports = WriteCheckReports(temporary.Path, fixture);
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline))
        {
            ValidateFrozenReferencesException = new IOException("frozen validation exploded"),
        };
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--candidate-lean-report", reports.Candidate,
            "--baseline-lean-report", reports.Baseline,
        ]);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal("frozen validation exploded", failure.Message);
        Assert.Equal(1, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckCharacterizesSnapshotRejectionShortCircuitingFrozenLedgerValidation()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = ValidFixtureWithFrozenLedger();
        fixture.Apply("badge");
        var reports = WriteCheckReports(temporary.Path, fixture);
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline))
        {
            ValidateFrozenReferencesException = new IOException("frozen ledger should not be reached"),
        };
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--candidate-lean-report", reports.Candidate,
            "--baseline-lean-report", reports.Baseline,
        ]);

        Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckCharacterizesAdmittedOutcomeProceedingThroughFrozenLedgerValidation()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = ValidFixtureWithFrozenLedger();
        var reports = WriteCheckReports(temporary.Path, fixture);
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--candidate-lean-report", reports.Candidate,
            "--baseline-lean-report", reports.Baseline,
        ]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckCharacterizesProtectedSurfaceOutcomeProceedingThroughFrozenLedgerValidation()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = ValidFixtureWithFrozenLedger();
        var reports = WriteCheckReports(temporary.Path, fixture);
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.SyntheticProtectedPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--candidate-lean-report", reports.Candidate,
            "--baseline-lean-report", reports.Baseline,
        ]);

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
        Assert.Equal(2, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckCharacterizesFrozenLedgerReplacementPreservingSl022Diagnostics()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var reports = WriteCheckReports(temporary.Path, fixture);
        var gateway = new RecordingRepositoryGateway(
            RawChangeSet.Create([RuleFixture.SyntheticProtectedPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
        [
            "--candidate-lean-report", reports.Candidate,
            "--baseline-lean-report", reports.Baseline,
        ]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var sl008 = Assert.Single(rejected.Diagnostics.Where(static diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(
            "frozen ledger is missing from current or protected baseline",
            sl008.Message);
        var protectedPath = RepoPath.TryCreate(RuleFixture.SyntheticProtectedPath, out var parsed)
            ? parsed
            : throw new InvalidOperationException("synthetic protected path is invalid");
        var expectedSl022 = BootstrapGate.CreateSl022Diagnostics(new MetaChangeSet(
            ImmutableArray.Create(protectedPath)));
        var actualSl022 = rejected.Diagnostics
            .Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(22))
            .OrderBy(static diagnostic => diagnostic.Path, StringComparer.Ordinal)
            .ToImmutableArray();
        Assert.Equal(
            expectedSl022.Select(static diagnostic => diagnostic.Render()),
            actualSl022.Select(static diagnostic => diagnostic.Render()));
    }

    [Fact]
    public void CheckCharacterizesOmittedFrozenEvidenceRootUsingRepositoryGatewayPath()
    {
        using var candidate = new TemporaryDirectory();
        using var evidence = new TemporaryDirectory();
        using var reports = new TemporaryDirectory();
        var invocation = CreateRealFrozenEvidenceInvocation(
            candidate.Path,
            evidence.Path,
            reports.Path,
            useMissingCommit: false);
        var environment = new ProductionCliEnvironment(
            candidate.Path,
            new GitRepositoryGateway(candidate.Path),
            new FakeLeanReportSource(null));
        var withoutEvidenceRoot = invocation.Arguments[..^2];

        var outcome = environment.Check(withoutEvidenceRoot);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(rejected.Diagnostics);
        Assert.Equal(RuleId.CreateKnown(8), diagnostic.RuleId);
        Assert.Contains("is not a reachable commit", diagnostic.Message, StringComparison.Ordinal);
    }

    public static IEnumerable<object[]> InvalidCheckArguments()
    {
        yield return [new[] { "--candidate-lean-report" }];
        yield return [new[] { "--unknown", "value" }];
        yield return [new[] { "candidate.json", "baseline.json" }];
        yield return [new[]
        {
            "--candidate-lean-report", "first.json",
            "--candidate-lean-report", "second.json",
        }];
        yield return [new[]
        {
            "--protected-base", "base-a",
            "--merge-base", "base-b",
        }];
    }

    public static IEnumerable<object?[]> MissingReportArguments()
    {
        yield return [Array.Empty<string>(), null];
        yield return [new[] { "--protected-base", "base-revision" }, "base-revision"];
        yield return [new[] { "--candidate-lean-report", "candidate.json" }, null];
        yield return [new[] { "--baseline-lean-report", "baseline.json" }, null];
    }

    private static RuleFixture ValidFixtureWithFrozenLedger()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        return fixture;
    }

    private static CheckReportPaths WriteCheckReports(string directory, RuleFixture fixture)
    {
        var candidateReport = Path.Combine(directory, "candidate.json");
        var baselineReport = Path.Combine(directory, "baseline.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());
        File.WriteAllBytes(
            baselineReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Baseline)),
                LeanAxiomReport.Create(fixture.BaselineReports)).AsSpan());
        return new CheckReportPaths(candidateReport, baselineReport);
    }

    private sealed record CheckReportPaths(string Candidate, string Baseline);

    private sealed class RecordingRepositoryGateway(
        RawChangeSet changes,
        RawRepositorySnapshot? current,
        RawRepositorySnapshot? baseline)
        : IRepositoryGateway
    {
        public Exception? PrepareException { get; init; }

        public Exception? ReadCurrentException { get; init; }

        public Exception? ReadRevisionException { get; init; }

        public Exception? ValidateFrozenReferencesException { get; init; }

        internal List<string> Events { get; } = [];

        internal List<string?> PreparedProtectedBases { get; } = [];

        internal List<FrozenLedgerReferenceSet> FrozenReferenceValidations { get; } = [];

        internal int ReadCount { get; private set; }

        internal int FrozenReferenceValidationCount => FrozenReferenceValidations.Count;

        public AdmissionTopologyOutcome InspectAdmissionTopology() =>
            throw new InvalidOperationException("topology should not be inspected");

        public PreparedRepository Prepare(string? protectedBase)
        {
            Events.Add($"Prepare({protectedBase ?? "<null>"})");
            PreparedProtectedBases.Add(protectedBase);
            if (PrepareException is not null) throw PrepareException;
            return new PreparedRepository("baseline", changes);
        }

        public FrozenRevisionIdentity ResolveFrozenRevision(string revision)
        {
            var value = revision.StartsWith("git-sha1:", StringComparison.Ordinal)
                ? revision["git-sha1:".Length..]
                : revision;
            var algorithm = value.Length == 40 ? "git-sha1:" : "git-sha256:";
            return new FrozenRevisionIdentity(
                value,
                algorithm + value,
                algorithm + new string('b', value.Length));
        }

        public FrozenRevisionIdentity ResolveCurrentRevision() =>
            ResolveFrozenRevision(new string('a', 40));

        public RawRepositorySnapshot ReadCurrent()
        {
            Events.Add("ReadCurrent");
            ReadCount++;
            if (ReadCurrentException is not null) throw ReadCurrentException;
            return current ?? throw new InvalidOperationException("current snapshot should not be read");
        }

        public RawRepositorySnapshot ReadRevision(string revision)
        {
            Events.Add($"ReadRevision({revision})");
            ReadCount++;
            if (ReadRevisionException is not null) throw ReadRevisionException;
            return baseline ?? throw new InvalidOperationException("baseline snapshot should not be read");
        }

        public RawRepositorySnapshot ReadFrozenRevision(string revision)
        {
            Events.Add($"ReadFrozenRevision({revision})");
            ReadCount++;
            return baseline ?? throw new InvalidOperationException("frozen revision snapshot should not be read");
        }

        public TrustedFrozenGitReferences ValidateFrozenReferences(FrozenLedgerReferenceSet references)
        {
            Events.Add("ValidateFrozenReferences");
            FrozenReferenceValidations.Add(references);
            if (ValidateFrozenReferencesException is not null)
            {
                throw ValidateFrozenReferencesException;
            }

            return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
        }
    }

    private sealed class ThrowingScribeVerifier(string message) : IScribeEmissionVerifier
    {
        internal int CallCount { get; private set; }

        public VerifiedScribeEmissions Verify(LeanAxiomReport report)
        {
            CallCount++;
            throw new InvalidOperationException(message);
        }
    }
}
