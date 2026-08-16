using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeDeltaScopeTests
{
    private static readonly ScribeDeltaDocument Source = new(
        "D5/S0/Carrier/Source",
        "Blueprint/D5/S0/Carrier/Source.scribe.cs",
        "Blueprint/D5/S0/Carrier/Source.md");

    private static readonly ScribeDeltaDocument OldTarget = new(
        "D5/S0/Carrier/OldTarget",
        "Blueprint/D5/S0/Carrier/OldTarget.scribe.cs",
        "Blueprint/D5/S0/Carrier/OldTarget.md");

    private static readonly ScribeDeltaDocument NewTarget = new(
        "D5/S0/Carrier/NewTarget",
        "Blueprint/D5/S0/Carrier/NewTarget.scribe.cs",
        "Blueprint/D5/S0/Carrier/NewTarget.md");

    [Fact]
    public void UnrelatedDeltaDoesNotReplayCommittedProjections()
    {
        var scope = ScribeDeltaScope.Create(
            RawChangeSet.Create(["docs/develop/notes.md"]),
            ImmutableHashSet<string>.Empty,
            [Source, OldTarget, NewTarget],
            ImmutableDictionary<string, ImmutableHashSet<string>>.Empty,
            ImmutableDictionary<string, ImmutableHashSet<string>>.Empty);

        Assert.False(scope.IsFull);
        Assert.Empty(scope.EmissionPaths);
        Assert.False(ScribeDeltaScope.RequiresBlueprintEmission(
            RawChangeSet.Create(["docs/develop/notes.md"]),
            ImmutableHashSet<string>.Empty));
    }

    [Fact]
    public void ChangedDocumentScopesOldAndNewDescribeAnchorTargets()
    {
        var candidateTargets = ImmutableDictionary<string, ImmutableHashSet<string>>.Empty
            .Add(Source.DefinitionPath, [NewTarget.Gid]);
        var baseTargets = ImmutableDictionary<string, ImmutableHashSet<string>>.Empty
            .Add(Source.DefinitionPath, [OldTarget.Gid]);

        var scope = ScribeDeltaScope.Create(
            RawChangeSet.Create([Source.DefinitionPath]),
            ImmutableHashSet.Create(StringComparer.Ordinal, Source.DefinitionPath),
            [Source, OldTarget, NewTarget],
            candidateTargets,
            baseTargets);

        Assert.False(scope.IsFull);
        Assert.Equal(
            [NewTarget.EmissionPath, OldTarget.EmissionPath, Source.EmissionPath],
            scope.EmissionPaths.Order(StringComparer.Ordinal));
    }

    [Theory]
    [InlineData("D5/S0/Source.lean")]
    [InlineData("tools/StrataLint.Scribe/Writers/CanonicalMarkdownWriter.cs")]
    [InlineData("Library/notes/source.md")]
    [InlineData("Golden/Projection/statement-projection-pilot-v1.json")]
    [InlineData("Meta/Digestion/backfill/source/residual-closed/probe.yaml")]
    public void SharedOrLeanReportInputWidensToEveryDocument(string changedPath)
    {
        var producers = changedPath.StartsWith("tools/", StringComparison.Ordinal)
            ? ImmutableHashSet.Create(StringComparer.Ordinal, changedPath)
            : ImmutableHashSet<string>.Empty;

        var scope = ScribeDeltaScope.Create(
            RawChangeSet.Create([changedPath]),
            producers,
            [Source, OldTarget, NewTarget],
            ImmutableDictionary<string, ImmutableHashSet<string>>.Empty,
            ImmutableDictionary<string, ImmutableHashSet<string>>.Empty);

        Assert.True(scope.IsFull);
        Assert.Equal(3, scope.EmissionPaths.Count);
    }

    [Fact]
    public void ValuesProjectionUsesOnlyItsMinimalClosure()
    {
        var sharedProducer = "tools/StrataLint.Scribe/Values/ValuesEvaluator.cs";
        var producers = ImmutableHashSet.Create(StringComparer.Ordinal, sharedProducer);

        Assert.False(ScribeDeltaScope.RequiresValuesProjection(
            RawChangeSet.Create([Source.DefinitionPath]),
            producers));
        Assert.False(ScribeDeltaScope.RequiresValuesProjection(
            RawChangeSet.Create(["D5/S0/Unrelated.lean"]),
            producers));
        Assert.True(ScribeDeltaScope.RequiresValuesProjection(
            RawChangeSet.Create([CanonicalValuesWriter.RelativePath]),
            producers));
        Assert.True(ScribeDeltaScope.RequiresValuesProjection(
            RawChangeSet.Create(["Golden/values-kernels.toml"]),
            producers));
        Assert.True(ScribeDeltaScope.RequiresValuesProjection(
            RawChangeSet.Create([sharedProducer]),
            producers));
    }

    [Fact]
    public void DeltaInputsFailClosedOnMalformedTrustedBaseReferenceAndForgedChangeManifest()
    {
        var valid = """
            # Source

            ## References

            - Narrative reference: [D5/S0/Carrier/OldTarget#describe/old](OldTarget.md#describe-old)
            """;

        Assert.Equal(
            [OldTarget.Gid],
            ScribeBaseDocumentReferences.ParseDescribeTargetGids(valid));
        Assert.Throws<FormatException>(() =>
            ScribeBaseDocumentReferences.ParseDescribeTargetGids(
                "- Narrative reference: [D5/S0/Carrier/OldTarget#describe/old](broken)\n"));

        var temporary = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-delta-input-" + Guid.NewGuid().ToString("N"));
        var repository = Path.Combine(temporary, "repository");
        TemporaryFileSystem.Directory.CreateDirectory(repository);
        try
        {
            RunGit(repository, ["init", "--quiet"]);
            TemporaryFileSystem.File.WriteAllText(
                Path.Combine(repository, "tracked.txt"),
                "base\n");
            RunGit(repository, ["add", "tracked.txt"]);
            RunGit(
                repository,
                ["-c", "user.name=Scribe Test", "-c", "user.email=scribe@example.invalid",
                    "commit", "--quiet", "-m", "base"]);
            var baseRevision = RunGit(repository, ["rev-parse", "HEAD"]);
            TemporaryFileSystem.File.WriteAllText(
                Path.Combine(repository, "tracked.txt"),
                "candidate\n");
            var exact = RawChangeSet.Create(["tracked.txt"]);
            ScribeDeltaInputLoader.ValidateChangeManifest(
                repository,
                baseRevision,
                exact);
            Assert.Throws<FormatException>(() => ScribeDeltaInputLoader.ValidateChangeManifest(
                repository,
                baseRevision,
                RawChangeSet.Create([])));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(temporary, recursive: true);
        }
    }

    private static string RunGit(string workingDirectory, IReadOnlyList<string> arguments)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            arguments,
            workingDirectory,
            TimeSpan.FromSeconds(30),
            64 * 1024);
        Assert.Equal(0, result.ExitCode);
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }
}
