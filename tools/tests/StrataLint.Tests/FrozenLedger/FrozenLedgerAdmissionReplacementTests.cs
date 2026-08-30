using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    /// A plain deposit appends one Freeze and deletes no accepted shard. Replacement recognition
    /// must stay null there: with no deletion both sides of its SetEquals conjunct are empty, so
    /// without an explicit non-empty guard the whole predicate degenerates to true and every
    /// ordinary deposit is mistaken for a wholesale ledger replacement -- which pulls the entire
    /// Closed corpus into the admission scope (issue #4083).
    [Fact]
    public void FreezeAppendWithoutLedgerDeletionIsNotRecognizedAsReplacement()
    {
        var appended = AppendOnlyDeposit();

        var services = new ProductionFrozenLedgerAdmissionServices(
            repositoryRoot: ".",
            ImmutableHashSet<string>.Empty);
        var prepared = services.Prepare(appended.Current, appended.ProtectedBase, appended.Changes);

        Assert.Null(prepared.Replacement);
    }

    /// The behaviour the conjunct above protects: an append-only deposit must wake only its own
    /// dependency closure, never the whole frozen corpus.
    [Fact]
    public void FreezeAppendWithoutLedgerDeletionScopesOnlyTheAppendedModule()
    {
        var appended = AppendOnlyDeposit();
        var services = new ProductionFrozenLedgerAdmissionServices(
            repositoryRoot: ".",
            ImmutableHashSet<string>.Empty);
        var prepared = services.Prepare(appended.Current, appended.ProtectedBase, appended.Changes);
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(appended.Current, appended.Report)).Capability;

        var scope = FrozenLedgerAdmissionScope.Create(
            appended.Changes,
            prepared,
            LeanTruthStates.Resolve(appended.Current, lean),
            LeanImportAdjacency.Build(appended.Current, lean));

        Assert.Equal([RepoPathFor("C")], scope.Paths.OrderBy(static path => path.Value, StringComparer.Ordinal));
    }

    private static AppendOnlyDepositFixture AppendOnlyDeposit()
    {
        ModuleSpec[] baseModules = [Module("A"), Module("B")];
        ModuleSpec[] candidateModules = [Module("A"), Module("B"), Module("C")];
        var baseEvents = EventFiles(BuildCatalog(baseModules));
        var appendedEvent = LedgerFileForModule(EventFiles(BuildCatalog(candidateModules)), "C");

        // Both sides carry byte-identical environment inputs: the only delta is module C's source
        // and its own accepted shard, so nothing else may legitimately widen the scope.
        var baseFiles = baseEvents.AddRange(
            ReanchorInputFiles(baseModules, ReanchorEnvironment.PinUpgrade, candidate: false));
        var currentFiles = baseEvents.Add(appendedEvent).AddRange(
            ReanchorInputFiles(candidateModules, ReanchorEnvironment.PinUpgrade, candidate: false));
        var changes = RawChangeSet.CreateWithKinds(
        [
            (appendedEvent.Path.Value, RawChangeKind.Added),
            (PathFor("C"), RawChangeKind.Added),
        ]);

        return new AppendOnlyDepositFixture(
            Snapshot(currentFiles),
            Snapshot(baseFiles),
            changes,
            ReanchorReport(candidateModules));
    }

    private sealed record AppendOnlyDepositFixture(
        RepositorySnapshot Current,
        RepositorySnapshot ProtectedBase,
        RawChangeSet Changes,
        LeanAxiomReport Report);

    private static RepositorySnapshot Snapshot(IEnumerable<RepositoryFile> files) =>
        RepositorySnapshot.Create(files.ToImmutableDictionary(static file => file.Path));

    private static void AssertReuseRejected(FrozenLedgerAdmissionFailure? failure)
    {
        var rejected = Assert.IsType<FrozenLedgerAdmissionFailure>(failure);
        Assert.Contains(
            "Freeze reused an active case ID or module path",
            rejected.Message,
            StringComparison.Ordinal);
    }

    private sealed class RejectAllReplacementAuthorization : IFrozenLedgerReplacementAuthorization
    {
        internal static RejectAllReplacementAuthorization Instance { get; } = new();

        public bool IsAuthorized(FrozenLedgerReplacementAuthorizationContext context) => false;
    }
}
