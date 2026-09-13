using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class AtomSourceStreamTests
{
    [Fact]
    public void MaterializeSourceRejectsUnregisteredSource()
    {
        var fixture = Create();
        AssertError(DigestionAtomContextError.SOURCE_MISSING, "source_id=unregistered",
            () => DigestionAtomContextProjection.MaterializeSource(fixture.Snapshot(), fixture.Ledger, "unregistered"));
    }

    [Fact]
    public void MaterializeSourceRejectsMissingSourceFile()
    {
        var fixture = Create();
        AssertError(DigestionAtomContextError.SOURCE_MISSING, "source_id=source source_path=docs/source.md",
            () => DigestionAtomContextProjection.MaterializeSource(
                fixture.Snapshot(includeSource: false), fixture.Ledger, "source"));
    }

    [Fact]
    public void MaterializeSourceRejectsDuplicateSourceRegistration()
    {
        var fixture = Create();
        var source = fixture.Ledger.RequireDigestionSources().Single();
        var ledger = fixture.Ledger.WithDigestionSources([source, source with { Entries = [] }]);
        AssertError(DigestionAtomContextError.SOURCE_MISSING, "source_id=source",
            () => DigestionAtomContextProjection.MaterializeSource(fixture.Snapshot(), ledger, "source"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MaterializeSourcePreservesOrderedAtomsAndData(bool expand)
    {
        var fixture = Create(ListClaims, expand);
        var claims = fixture.Atomized.Claims;
        var expected = expand
            ? new[] { claims[0] }.Concat(fixture.Atomized.ClausePlans.Single().Children).Append(claims[^1]).ToArray()
            : claims.ToArray();
        var stream = DigestionAtomContextProjection.MaterializeSource(fixture.Snapshot(), fixture.Ledger, "source");
        Assert.Equal(("source", SourcePath, "generic-v1"), (stream.SourceId, stream.SourcePath, stream.Atomizer));
        Assert.Equal(expected.Select(Id), stream.AtomIds);
        Assert.Equal(expected.Length, stream.Atoms.Length);
        for (var index = 0; index < expected.Length; index++)
        {
            var atom = stream.Atoms[index];
            Assert.Equal((expected[index].StartByte, expected[index].EndByte), (atom.StartByte, atom.EndByte));
            Assert.Equal(expected[index].RawBytes.ToArray(), atom.RawBytes.ToArray());
            Assert.Equal(expected[index].Fingerprints, atom.Fingerprints);
            Assert.Equal(expected[index].Context.ToArray(), atom.Context.ToArray());
            Assert.Equal(expected[index].StatusMarker, atom.StatusMarker);
        }
    }

    [Fact]
    public void MaterializeSourceKeepsUnregisteredAtomsAndRepeatedOccurrences()
    {
        var fixture = Create();
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries()
            .Where(entry => entry.AtomId == Id(fixture.Atomized.Claims[1]))) with
        {
            SourceBytes = Encoding.UTF8.GetBytes(ThreeClaims + ThreeClaims),
        };
        var stream = DigestionAtomContextProjection.MaterializeSource(fixture.Snapshot(), fixture.Ledger, "source");
        Assert.Equal(fixture.Atomized.Claims.Concat(fixture.Atomized.Claims).Select(Id), stream.AtomIds);
        var occurrences = stream.ResolveOccurrences(Id(fixture.Atomized.Claims[1]));
        Assert.Equal(new[] { 2, 5 }, occurrences.Select(context => context.Index));
        Assert.All(occurrences, context => Assert.Null(context.Previous!.Value.LedgerState));
    }

    [Fact]
    public void OneMaterializedSourceResolvesTwoAtomsLikeLegacyEntrypoints()
    {
        var fixture = Create(ListClaims, expand: true);
        var snapshot = fixture.Snapshot();
        var stream = DigestionAtomContextProjection.MaterializeSource(snapshot, fixture.Ledger, "source");
        var children = fixture.Atomized.ClausePlans.Single().Children;
        foreach (var id in new[] { Id(children[0]), Id(children[^1]) })
        {
            var actual = Assert.Single(stream.ResolveOccurrences(id));
            AssertContextEqual(DigestionAtomContextProjection.Resolve(snapshot, fixture.Ledger, id), actual);
            AssertContextEqual(Assert.Single(DigestionAtomContextProjection.ResolveOccurrences(
                snapshot, fixture.Ledger, id)), actual);
        }
    }

    [Fact]
    public void MaterializedAtomIdsDoNotReadUnrelatedLedgerStatus()
    {
        var fixture = Create();
        var snapshot = fixture.Snapshot();
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry =>
            entry.AtomId != Id(fixture.Atomized.Claims[^1]) ? entry : entry with
            {
                ProjectedStatus = new((DigestionMigrationState)(-1), DigestionTruthState.Open),
            }));
        var stream = DigestionAtomContextProjection.MaterializeSource(snapshot, fixture.Ledger, "source");
        Assert.Equal(fixture.Atomized.Claims.Select(Id), stream.AtomIds);
        var first = DigestionAtomContextProjection.Resolve(snapshot, fixture.Ledger, Id(fixture.Atomized.Claims[0]));
        AssertContextEqual(first, Assert.Single(stream.ResolveOccurrences(first.Target.AtomId)));
        Assert.Equal((1, 3), (first.Index, first.Count));
    }

    [Fact]
    public void LegacyNeighborStatusFailureKeepsTypedError()
    {
        var fixture = Create();
        var snapshot = fixture.Snapshot();
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry => entry with
        {
            ProjectedStatus = new((DigestionMigrationState)(-1), DigestionTruthState.Open),
        }));
        AssertError(DigestionAtomContextError.OCCURRENCE_MISSING, new ArgumentOutOfRangeException("value").Message,
            () => DigestionAtomContextProjection.Resolve(snapshot, fixture.Ledger, Id(fixture.Atomized.Claims[0])));
    }

    [Fact]
    public void LegacySourceErrorsKeepTargetPathAndValidationPrecedence()
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry => entry with
        {
            SourcePath = "docs/ledger-path.md",
        }));
        var missing = fixture.Snapshot(includeSource: false);
        AssertError(DigestionAtomContextError.SOURCE_MISSING, "source_id=source source_path=docs/ledger-path.md",
            () => DigestionAtomContextProjection.ResolveOccurrences(missing, fixture.Ledger, target));
        AssertError(DigestionAtomContextError.ARGUMENTS_INVALID, "atom_id must be 64 lowercase hexadecimal characters",
            () => DigestionAtomContextProjection.ResolveOccurrences(missing, fixture.Ledger, "bad"));
        AssertError(DigestionAtomContextError.ATOM_ABSENT, $"atom_id={new string('0', 64)}",
            () => DigestionAtomContextProjection.ResolveOccurrences(missing, fixture.Ledger, new string('0', 64)));
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry => entry with
        {
            SourceId = "unregistered",
        }));
        AssertError(DigestionAtomContextError.SOURCE_MISSING, "source_id=unregistered source_path=docs/ledger-path.md",
            () => DigestionAtomContextProjection.ResolveOccurrences(missing, fixture.Ledger, target));
    }

    private static void AssertContextEqual(DigestionAtomContext expected, DigestionAtomContext actual)
    {
        Assert.Equal(expected.Target, actual.Target);
        Assert.Equal((expected.Index, expected.Count, expected.SourceId, expected.SourcePath, expected.Atomizer),
            (actual.Index, actual.Count, actual.SourceId, actual.SourcePath, actual.Atomizer));
        Assert.Equal((expected.PreviousBoundaryReason, expected.NextBoundaryReason),
            (actual.PreviousBoundaryReason, actual.NextBoundaryReason));
        AssertNeighborEqual(expected.Previous, actual.Previous);
        AssertNeighborEqual(expected.Current, actual.Current);
        AssertNeighborEqual(expected.Next, actual.Next);
    }

    private static void AssertNeighborEqual(
        (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? expected,
        (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? actual)
    {
        Assert.Equal(expected.HasValue, actual.HasValue);
        if (expected is not { } value) return;
        Assert.Equal((value.AtomId, value.LedgerState), (actual!.Value.AtomId, actual.Value.LedgerState));
        Assert.Equal(value.RawBytes.ToArray(), actual.Value.RawBytes.ToArray());
    }

    private static void AssertError(DigestionAtomContextError code, string message, Action action)
    {
        var error = Assert.Throws<DigestionAtomContextException>(action);
        Assert.Equal(code, error.Code);
        Assert.Equal(message, error.Message);
    }
}
