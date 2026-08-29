using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenLedgerAdmissionSchemaMonotonicityTests
{
    [Fact]
    public void AdmissionRejectsV4DeltaWhenProtectedBaseEventsAreAllV5BecauseSchemaWouldDowngrade()
    {
        var failure = ValidateSchemaTransition([5], deltaSchemaVersion: 4);

        var rejected = Assert.IsType<FrozenLedgerAdmissionFailure>(failure);
        Assert.Contains("schema downgrade", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionAllowsV5DeltaWhenProtectedBaseEventsAreAllV5()
    {
        var failure = ValidateSchemaTransition([5], deltaSchemaVersion: 5);

        Assert.Null(failure);
    }

    [Fact]
    public void AdmissionAllowsV5DeltaWhenProtectedBaseContainsV4History()
    {
        var failure = ValidateSchemaTransition([4, 5], deltaSchemaVersion: 5);

        Assert.Null(failure);
    }

    [Fact]
    public void AdmissionAllowsV5DeltaWhenProtectedBaseIsEmpty()
    {
        var failure = ValidateSchemaTransition([], deltaSchemaVersion: 5);

        Assert.Null(failure);
    }

    private static FrozenLedgerAdmissionFailure? ValidateSchemaTransition(
        IReadOnlyList<int> baseSchemaVersions,
        int deltaSchemaVersion)
    {
        var baseModules = baseSchemaVersions
            .Select((_, index) => Module($"Base{index}"))
            .ToArray();
        var deltaModule = Module("Delta");
        var baseCatalog = BuildCatalog(baseModules);
        var candidateCatalog = BuildCatalog(baseModules.Append(deltaModule).ToArray());
        var canonicalBaseView = BaseView(baseCatalog);
        Assert.Equal(baseSchemaVersions.Count, canonicalBaseView.Events.Length);
        var baseEvents = canonicalBaseView.Events
            .Select((item, index) => item with { SchemaVersion = baseSchemaVersions[index] })
            .ToImmutableArray();
        var baseView = new FrozenLedgerBaseView(
            baseEvents,
            canonicalBaseView.ActiveByCase,
            canonicalBaseView.EventHashes,
            canonicalBaseView.EventIdentities);
        var canonicalDeltaEvent = Assert.Single(LoadEvents(EventFiles(BuildCatalog(deltaModule))));
        var deltaEvent = canonicalDeltaEvent with { SchemaVersion = deltaSchemaVersion };
        var preparation = new FrozenLedgerAdmissionPreparation(
            baseView,
            [deltaEvent],
            ImmutableHashSet<string>.Empty);
        var changes = RawChangeSet.CreateWithKinds(
            [(deltaEvent.SourcePath.Value, RawChangeKind.Added)]);
        var scope = FrozenLedgerAdmissionScope.Create(
            changes,
            preparation,
            candidateCatalog.States,
            candidateCatalog.Adjacency);

        return FrozenLedger.ValidateAdmissionDelta(
            preparation,
            scope,
            candidateCatalog,
            RejectAllReplacementAuthorization.Instance);
    }

    private sealed class RejectAllReplacementAuthorization : IFrozenLedgerReplacementAuthorization
    {
        internal static RejectAllReplacementAuthorization Instance { get; } = new();

        public bool IsAuthorized(FrozenLedgerReplacementAuthorizationContext context) => false;
    }
}
