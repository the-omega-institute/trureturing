using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenLedgerDeltaPredicateTests
{
    public static TheoryData<string> DirectLedgerInputs => new()
    {
        FrozenLedgerChangeClassifier.AcceptedRoot + "/event.json",
        "lean-toolchain",
        "lakefile.toml",
        "lakefile.lean",
        "lake-manifest.json",
        "Trureturing.lean",
        "D5/S0/Carrier/Ring.lean",
        ".github/workflows/ci.yml",
        "tools/scripts/report/lean-report-input.sh",
        "Directory.Build.props",
        "Directory.Build.targets",
        "Directory.Packages.props",
        "global.json",
        "tools/StrataLint.Cli/StrataLint.Cli.csproj",
        "tools/StrataLint.Engine/StrataLint.Engine.csproj",
        "tools/StrataLint.Cli/Admission/ProductionCliEnvironment.cs",
        "tools/StrataLint.Engine/Ledger/Admission/FrozenLedgerDeltaPredicate.cs",
    };

    [Theory]
    [MemberData(nameof(DirectLedgerInputs))]
    public void EveryDirectLedgerInputKindAuthorizesIncrementalWork(string path)
    {
        foreach (var kind in Enum.GetValues<RawChangeKind>())
        {
            var changes = RawChangeSet.CreateWithKinds([(path, kind)]);

            Assert.True(FrozenLedgerDeltaPredicate.HasLedgerDelta(
                changes,
                ImmutableHashSet<string>.Empty));
        }
    }

    [Fact]
    public void CanonicalProducerClosureAuthorizesIncrementalWorkWithoutACopiedPathTable()
    {
        const string producerPath = "tools/StrataLint.Engine/Ledger/FrozenLedger.cs";
        var changes = RawChangeSet.Create([producerPath]);
        var producerClosure = ImmutableHashSet.Create(StringComparer.Ordinal, producerPath);

        Assert.True(FrozenLedgerDeltaPredicate.HasLedgerDelta(changes, producerClosure));
    }

    [Theory]
    [InlineData("lean-toolchain")]
    [InlineData("lakefile.toml")]
    [InlineData("lakefile.lean")]
    [InlineData("lake-manifest.json")]
    public void EnvironmentInputChangeExpandsAdmissionScopeToEveryFrozenModule(string path)
    {
        var catalog = FrozenLedgerTestData.BuildCatalog(
            FrozenLedgerTestData.Module("A"),
            FrozenLedgerTestData.Module("B"));
        var baseView = FrozenLedgerTestData.BaseView(catalog);
        var preparation = new FrozenLedgerAdmissionPreparation(
            baseView,
            [],
            ImmutableHashSet<string>.Empty);

        var scope = FrozenLedgerAdmissionScope.Create(
            RawChangeSet.CreateWithKinds([(path, RawChangeKind.Modified)]),
            preparation,
            catalog.States,
            catalog.Adjacency);

        Assert.Equal(
            catalog.ClosedNodes.Select(static node => node.RepoPath).OrderBy(static item => item.Value),
            scope.Paths.OrderBy(static item => item.Value));
    }

    [Fact]
    public void UnrelatedCandidateBytesDoNotAuthorizeLedgerWork()
    {
        var changes = RawChangeSet.Create(["Blueprint/Papers/Example.scribe.cs"]);
        var producerClosure = ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "tools/StrataLint.Engine/Ledger/FrozenLedger.cs");

        Assert.False(FrozenLedgerDeltaPredicate.HasLedgerDelta(changes, producerClosure));
    }
}
