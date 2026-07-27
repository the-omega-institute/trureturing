using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class SplitCommandTests
{
    private const string SourceDirectory = "D5/S1/Digit";
    private const string DestinationDirectory = "D5/S1/Phase";
    private const string SplitDate = "2026-07-27";

    [Fact]
    public void FormalPlanMovesOnlyPressureAdditionsAndRewritesExactReferences()
    {
        var baseline = FormalBaseline();
        var current = new Dictionary<string, string>(baseline, StringComparer.Ordinal)
        {
            ["D5/S1/Digit/NewResult.lean"] = FormalFile(
                "D5/S1/Digit/NewResult",
                "D5.S1.Digit.NewResult"),
            ["Blueprint/D5/S1/Digit/NewResult.scribe.cs"] =
                "namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;\n"
                + "// D5/S1/Digit/NewResult\n",
            ["Blueprint/D5/S1/Digit/NewResult.md"] =
                "<!-- GID: D5/B/S1/Digit/NewResult -->\n",
            ["Blueprint/D5/S1/Digit/NewResultExtra.md"] =
                "<!-- GID: D5/B/S1/Digit/NewResultExtra -->\n",
            ["D5/S1/Scale/Consumer.lean"] =
                "import D5.S1.Digit.NewResult\n\nnamespace D5.S1.Scale.Consumer\n\n"
                + "#check D5.S1.Digit.NewResult.result\n\nend D5.S1.Scale.Consumer\n",
        };

        var first = SplitPlanner.Plan(
            Decode(current),
            Decode(baseline),
            Policy(),
            new SplitRequest(SourceDirectory, "Phase", SplitDate, new string('a', 40)));
        var second = SplitPlanner.Plan(
            Decode(current),
            Decode(baseline),
            Policy(),
            new SplitRequest(SourceDirectory, "Phase", SplitDate, new string('a', 40)));

        Assert.Equal(SplitPlanStatus.Pending, first.Status);
        Assert.Equal(SplitReceiptWriter.Write(first), SplitReceiptWriter.Write(second));
        Assert.Equal(
            new[]
            {
                "Blueprint/D5/S1/Digit/NewResult.md",
                "Blueprint/D5/S1/Digit/NewResult.scribe.cs",
                "D5/S1/Digit/NewResult.lean",
            },
            first.Moves.Select(static move => move.Source));
        Assert.Equal(
            new[]
            {
                "Blueprint/D5/S1/Phase/NewResult.md",
                "Blueprint/D5/S1/Phase/NewResult.scribe.cs",
                "D5/S1/Phase/NewResult.lean",
            },
            first.Moves.Select(static move => move.Target));
        Assert.All(
            baseline.Keys,
            path => Assert.DoesNotContain(first.Moves, move => move.Source == path));
        var consumer = Assert.Single(
            first.Writes,
            write => write.Path == "D5/S1/Scale/Consumer.lean");
        Assert.Contains("import D5.S1.Phase.NewResult", consumer.Text, StringComparison.Ordinal);
        Assert.Contains("D5.S1.Phase.NewResult.result", consumer.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("D5.S1.Digit.NewResult", consumer.Text, StringComparison.Ordinal);
        Assert.DoesNotContain(
            first.Writes,
            write => write.Path.Contains("NewResultExtra", StringComparison.Ordinal));
        Assert.Equal(12, first.PreservedBaseMappings.Length);
        Assert.Contains(
            "all 12 base paths remain in place",
            Assert.Single(first.Writes, write => write.Path == "D5/S1/MAP.md").Text,
            StringComparison.Ordinal);
    }

    [Fact]
    public void LibraryPlanUsesRegisteredDomainRoutingWithoutMovingExistingNotes()
    {
        var baseline = Enumerable.Range(1, 12).ToDictionary(
            index => $"Library/notes/source{index:00}.md",
            index => $"<!-- GID: D5/L/source{index:00} -->\n",
            StringComparer.Ordinal);
        var current = new Dictionary<string, string>(baseline, StringComparer.Ordinal)
        {
            ["Library/notes/newsource.md"] = "<!-- GID: D5/L/newsource -->\n",
            ["Blueprint/D5/S1/Phase/Consumer.scribe.cs"] =
                "// literature: D5/L/newsource\n",
        };

        var plan = SplitPlanner.Plan(
            Decode(current),
            Decode(baseline),
            Policy(),
            new SplitRequest("Library/notes", "Phase", SplitDate, new string('b', 40)));

        var move = Assert.Single(plan.Moves);
        Assert.Equal("Library/notes/newsource.md", move.Source);
        Assert.Equal("Library/Phase/newsource.md", move.Target);
        Assert.All(
            baseline.Keys,
            path => Assert.DoesNotContain(plan.Moves, candidate => candidate.Source == path));
        Assert.Contains(
            "D5/L/Phase/newsource",
            Assert.Single(
                plan.Writes,
                write => write.Path == "Blueprint/D5/S1/Phase/Consumer.scribe.cs").Text,
            StringComparison.Ordinal);
    }

    [Fact]
    public void PlannerRejectsAnOverflowThatWouldRequireMovingBaseFiles()
    {
        var baseline = FormalBaseline();
        baseline["D5/S1/Digit/ExistingThirteenth.lean"] = FormalFile(
            "D5/S1/Digit/ExistingThirteenth",
            "D5.S1.Digit.ExistingThirteenth");

        var exception = Assert.Throws<SplitPlanException>(() => SplitPlanner.Plan(
            Decode(baseline),
            Decode(baseline),
            Policy(),
            new SplitRequest(SourceDirectory, "Phase", SplitDate, new string('c', 40))));

        Assert.Contains("explicit migration", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ApplyIsIdempotentAndRunsCanonicalDerivationsOnce()
    {
        using var repository = CreateRepository();
        AddPressureFile(repository.Path);
        var runner = new RecordingSplitDerivationRunner(success: true);

        var first = SplitCommand.Run(
            repository.Path,
            new GitRepositoryGateway(repository.Path),
            runner,
            [SourceDirectory, "--domain", "Phase", "--date", SplitDate, "--apply"]);
        var second = SplitCommand.Run(
            repository.Path,
            new GitRepositoryGateway(repository.Path),
            runner,
            [SourceDirectory, "--domain", "Phase", "--date", SplitDate, "--apply"]);

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        Assert.Contains("\"status\": \"applied\"", first.Output, StringComparison.Ordinal);
        Assert.Contains("\"status\": \"already_applied\"", second.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(repository.Path, "D5/S1/Digit/NewResult.lean")));
        Assert.True(File.Exists(Path.Combine(repository.Path, "D5/S1/Phase/NewResult.lean")));
        Assert.Equal(1, runner.CallCount);
        Assert.Equal(
            FormalBaseline().Keys.Order(StringComparer.Ordinal),
            FormalBaseline().Keys
                .Where(path => File.Exists(Path.Combine(repository.Path, path)))
                .Order(StringComparer.Ordinal));
    }

    [Fact]
    public void DerivationFailureRestoresExactPreCommandWorktree()
    {
        using var repository = CreateRepository();
        AddPressureFile(repository.Path);
        var existing = Path.Combine(repository.Path, "D5/S1/Digit/Item01.lean");
        File.AppendAllText(existing, "-- pre-existing dirty edit\n");
        var before = SnapshotBytes(repository.Path);
        var runner = new RecordingSplitDerivationRunner(success: false);

        var result = SplitCommand.Run(
            repository.Path,
            new GitRepositoryGateway(repository.Path),
            runner,
            [SourceDirectory, "--domain", "Phase", "--date", SplitDate, "--apply"]);

        Assert.False(result.Success);
        Assert.Contains("rolled back", result.Error, StringComparison.OrdinalIgnoreCase);
        var after = SnapshotBytes(repository.Path);
        Assert.Equal(before.Keys, after.Keys);
        foreach (var (path, bytes) in before)
        {
            Assert.True(
                bytes.AsSpan().SequenceEqual(after[path].AsSpan()),
                $"rollback changed bytes for {path}");
        }
        Assert.False(File.Exists(Path.Combine(repository.Path, "Generated/split-probe.txt")));
    }

    private static Dictionary<string, string> FormalBaseline() => Enumerable.Range(1, 12).ToDictionary(
        index => $"D5/S1/Digit/Item{index:00}.lean",
        index => FormalFile($"D5/S1/Digit/Item{index:00}", $"D5.S1.Digit.Item{index:00}"),
        StringComparer.Ordinal);

    private static string FormalFile(string gid, string module) =>
        $"/- GID: {gid}\n"
        + "   generality: G\n"
        + $"   mirror-B: D5/B/{gid[3..]}\n"
        + "   mirror-E: none(waiver:test)\n"
        + "   anchors: []\n"
        + "   digest: Fixture. -/\n\n"
        + $"namespace {module}\n\ndef result : Unit := ()\n\nend {module}\n";

    private static ValidatedPolicy Policy() => Assert.IsType<RegistryLoadOutcome.Accepted>(
        RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes("""
                domains:
                  Digit:
                    stratum: S1
                    definition: Raw digit representations.
                  Phase:
                    stratum: S1
                    definition: Additive phases.
                  Scale:
                    stratum: S1
                    definition: Logarithmic scales.
                """ + "\n"))).Policy;

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(
            files.OrderBy(static item => item.Key, StringComparer.Ordinal)
                .Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static TemporaryDirectory CreateRepository()
    {
        var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--initial-branch=dev");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        Write(repository.Path, "Meta/registry.yaml", TestRegistry.Canonical);
        Write(repository.Path, "Meta/domains.yaml", """
            domains:
              Digit:
                stratum: S1
                definition: Raw digit representations.
              Phase:
                stratum: S1
                definition: Additive phases.
            """ + "\n");
        foreach (var (path, text) in FormalBaseline()) Write(repository.Path, path, text);
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "fixture baseline");
        return repository;
    }

    private static void AddPressureFile(string root) => Write(
        root,
        "D5/S1/Digit/NewResult.lean",
        FormalFile("D5/S1/Digit/NewResult", "D5.S1.Digit.NewResult"));

    private static void Write(string root, string relativePath, string text)
    {
        var path = Path.Combine(root, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, text, new UTF8Encoding(false));
    }

    private static ImmutableSortedDictionary<string, ImmutableArray<byte>> SnapshotBytes(string root) =>
        GitRepositorySnapshotReader.ReadCurrent(root).Entries.ToImmutableSortedDictionary(
            static entry => entry.Path,
            static entry => entry.Bytes,
            StringComparer.Ordinal);
}

internal sealed class RecordingSplitDerivationRunner(bool success) : ISplitDerivationRunner
{
    internal int CallCount { get; private set; }

    public SplitDerivationResult Run(string repositoryRoot, string baseRevision)
    {
        CallCount++;
        var generated = Path.Combine(repositoryRoot, "Generated", "split-probe.txt");
        Directory.CreateDirectory(Path.GetDirectoryName(generated)!);
        File.WriteAllText(generated, "derived\n");
        return success
            ? new SplitDerivationResult(true, ImmutableArray.Create("make lean-report", "make emit", "make ingest"), string.Empty)
            : new SplitDerivationResult(false, ImmutableArray<string>.Empty, "synthetic derivation failure");
    }
}
