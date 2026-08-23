using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void WriterSemanticPinComparisonDoesNotReplayEntryEnvironmentBinding()
    {
        var fixture = CreatePinBumpFixture([], []);
        AddSupersedeEvents(fixture);
        var baseView = FrozenLedgerBaseViewReader.Read(Decode(Snapshot(fixture.Baseline)));
        var entry = baseView.ActiveByPath[RepoPath.CreateKnown(RuleFixture.RingPath)];
        var protectedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(
                SnapshotWithBaseOid(
                    fixture.Baseline,
                    "lean-toolchain",
                    FrozenLedgerTestData.GitOid('f')))).Snapshot;
        var candidateSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(SnapshotWithoutGitBlobOids(fixture.Files))).Snapshot;
        var report = LeanAxiomReport.Create(fixture.Reports);

        Assert.True(
            LeanImportClosure.RelevantSemanticPinsChanged(
                report,
                RepoPath.CreateKnown(RuleFixture.RingPath),
                protectedSnapshot,
                candidateSnapshot));
    }

    [Fact]
    public void SemanticPinEdgeIsOwnedByAdmissionAndNotWriter()
    {
        var closure = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/StrataLint.Engine/Anchors/LeanImportClosure.cs"));
        var admission = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/StrataLint.Engine/Ledger/Admission/FrozenLedgerAdmission.cs"));
        var writer = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/StrataLint.Cli/Commands/Ledger/DagLedgerSupersedeWriter.cs"));

        Assert.Contains("ProtectedEnvironmentMatchesEntry(", admission, StringComparison.Ordinal);
        Assert.DoesNotContain("ProtectedEnvironmentMatchesEntry(", writer, StringComparison.Ordinal);
        var predicateStart = closure.IndexOf(
            "internal static bool RelevantSemanticPinsChanged(",
            StringComparison.Ordinal);
        var predicateEnd = closure.IndexOf(
            "    internal static bool CandidateStatementsAvoidTrivialTruth(",
            predicateStart,
            StringComparison.Ordinal);
        Assert.True(predicateStart >= 0 && predicateEnd > predicateStart);
        Assert.DoesNotContain(
            "ProtectedEnvironmentMatchesEntry(",
            closure[predicateStart..predicateEnd],
            StringComparison.Ordinal);
    }

    [Fact]
    public void RelevantSemanticPinsGuardTrueAcceptsStatementDriftWithTrustedBaseOids()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        fixture.Reports[RuleFixture.RingPath] = RingReport([], "Int");
        AddSupersedeEvents(fixture);
        var candidate = SnapshotWithoutGitBlobOids(fixture.Files);
        Assert.All(candidate.Entries, static entry => Assert.Null(entry.GitBlobOid));
        var gateway = PinBumpGatewayWithSnapshots(
            fixture,
            candidate,
            Snapshot(fixture.Baseline));

        var outcome = CheckPinBump(temporary, fixture, gateway);

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
    }

    [Fact]
    public void RelevantSemanticPinsGuardFalseRejectsStatementDriftWithMismatchedBaseOid()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        fixture.Reports[RuleFixture.RingPath] = RingReport([], "Int");
        AddSupersedeEvents(fixture);
        var protectedBase = SnapshotWithBaseOid(
            fixture.Baseline,
            "lean-toolchain",
            FrozenLedgerTestData.GitOid('f'));
        var gateway = PinBumpGatewayWithSnapshots(
            fixture,
            SnapshotWithoutGitBlobOids(fixture.Files),
            protectedBase);

        var outcome = CheckPinBump(temporary, fixture, gateway);

        AssertSupersedeRejection(outcome, "no relevant imported semantic pin changed");
    }

    [Fact]
    public void ProtectedEnvironmentGuardFailsClosedWhenBaseGitBlobOidIsMissing()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = CreatePinBumpFixture([], []);
        fixture.Reports[RuleFixture.RingPath] = RingReport([], "Int");
        AddSupersedeEvents(fixture);
        var protectedBase = SnapshotWithBaseOid(fixture.Baseline, "lean-toolchain", null);
        var gateway = PinBumpGatewayWithSnapshots(
            fixture,
            SnapshotWithoutGitBlobOids(fixture.Files),
            protectedBase);

        var outcome = CheckPinBump(temporary, fixture, gateway);

        AssertSupersedeRejection(outcome, "no relevant imported semantic pin changed");
    }

    private static FakeRepositoryGateway PinBumpGatewayWithSnapshots(
        RuleFixture fixture,
        RawRepositorySnapshot candidate,
        RawRepositorySnapshot protectedBase)
    {
        var eventChanges = AddedLedgerPaths(fixture)
            .Select(static path => (path, RawChangeKind.Added));
        return new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds(
                new[] { ("lean-toolchain", RawChangeKind.Modified) }.Concat(eventChanges)),
            candidate,
            protectedBase);
    }

    private static RawRepositorySnapshot SnapshotWithoutGitBlobOids(
        IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    private static RawRepositorySnapshot SnapshotWithBaseOid(
        IReadOnlyDictionary<string, string> files,
        string selectedPath,
        string? selectedOid) =>
        RawRepositorySnapshot.Create(files.Select(pair => new RawRepositoryEntry(
            pair.Key,
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(pair.Value)),
            pair.Key == selectedPath ? selectedOid : FrozenLedgerTestData.GitBlobOid(pair.Value))));
}
