using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void OrdinaryDepositIsNotAFullReplacement()
    {
        var baseCatalog = BuildCatalog(Module("A"));
        var baseEvents = EventFiles(baseCatalog);
        var deltaFiles = EventFiles(BuildCatalog(Module("B")));
        var deltaEvents = LoadEvents(deltaFiles);
        var current = Snapshot(baseEvents.AddRange(deltaFiles));
        var changes = RawChangeSet.CreateWithKinds(
            deltaFiles.Select(static file => (file.Path.Value, RawChangeKind.Added)));

        var recognition = FrozenLedgerReplacementRecognition.Recognize(
            BaseView(baseCatalog),
            current,
            changes,
            deltaEvents);

        Assert.Null(recognition);
    }

    [Fact]
    public void ActualFullReplacementStillRecognizes()
    {
        var baseCatalog = BuildCatalog(Module("A"));
        var baseEvents = EventFiles(baseCatalog);
        var deltaFiles = EventFiles(BuildCatalog(Module("B")));
        var deltaEvents = LoadEvents(deltaFiles);
        var current = Snapshot(deltaFiles);
        var changes = RawChangeSet.CreateWithKinds(
            baseEvents.Select(static file => (file.Path.Value, RawChangeKind.Deleted))
                .Concat(deltaFiles.Select(static file =>
                    (file.Path.Value, RawChangeKind.Added))));

        var recognition = FrozenLedgerReplacementRecognition.Recognize(
            BaseView(baseCatalog),
            current,
            changes,
            deltaEvents);

        Assert.NotNull(recognition);
    }

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
