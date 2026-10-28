using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.CliIntegration.Tests;

public sealed class SourcePrerequisiteCliTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SourceCapacityMatchesNormalOwnerIncludingMaterialsAndExclusions(bool delta)
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] += new string('\n', 1001);
        fixture.Files["docs/develop/theory/Long.md"] = new string('\n', 5001);
        fixture.Files["Library/notes/Long.md"] = new string('\n', 3001);
        fixture.Files["lake-manifest.json"] = new string('\n', 1001);
        fixture.Files["Blueprint/D5/S0/Carrier/Ring.md"] = new string('\n', 1001);
        var changes = RawChangeSet.CreateWithKinds([
            ("docs/develop/theory/Long.md", RawChangeKind.Modified),
            ("Library/notes/Long.md", RawChangeKind.Added)]);
        var result = Source(fixture, changes, delta);
        Assert.Equal(1, result.ExitCode);
        using var json = JsonDocument.Parse(result.Output);
        var messages = json.RootElement.GetProperty("diagnostics").EnumerateArray()
            .Where(d => d.GetProperty("RuleId").GetProperty("Value").GetString() == "SL-003")
            .Select(d => d.GetProperty("Message").GetString()).Order().ToArray();
        var context = fixture.Build(changes);
        var expected = (delta ? RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), context)
            : RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(3), context.CurrentFacts))
            .Diagnostics.Select(d => d.Message).Order().ToArray();
        Assert.Equal(expected, messages);
    }

    [Theory]
    [InlineData(96, false, false, false)]
    [InlineData(97, true, true, false)]
    [InlineData(97, false, false, false)]
    [InlineData(192, false, false, false)]
    [InlineData(193, false, false, true)]
    public void CurrentToleranceAndDeltaMembershipAreDistinct(int count, bool introducePath, bool deltaBlocks, bool currentBlocks)
    {
        var fixture = new RuleFixture();
        for (var i = 0; i < count; i++)
        {
            var path = $"Library/notes/Note{i}.md";
            fixture.Files[path] = "note\n";
            if (!introducePath || i < count - 1) fixture.Baseline[path] = "note\n";
        }
        var changes = RawChangeSet.CreateWithKinds([($"Library/notes/Note{count - 1}.md",
            introducePath ? RawChangeKind.Added : RawChangeKind.Modified)]);
        Assert.Equal(currentBlocks ? 1 : 0, Source(fixture, changes, delta: false).ExitCode);
        Assert.Equal(currentBlocks || deltaBlocks ? 1 : 0, Source(fixture, changes, delta: true).ExitCode);
    }

    [Theory]
    [InlineData("Library/notes/Note.md", 3000, RawChangeKind.Added, 0)]
    [InlineData("Library/notes/Note.md", 3001, RawChangeKind.Added, 1)]
    [InlineData("Library/notes/Note.md", 3000, RawChangeKind.Modified, 0)]
    [InlineData("Library/notes/Note.md", 3001, RawChangeKind.Modified, 1)]
    [InlineData("Library/notes/Note.md", 3001, RawChangeKind.Deleted, 0)]
    [InlineData("docs/develop/theory/Note.md", 5000, RawChangeKind.Modified, 0)]
    [InlineData("docs/develop/theory/Note.md", 5001, RawChangeKind.Modified, 1)]
    [InlineData("docs/develop/theory/Note.md", 5001, RawChangeKind.Deleted, 0)]
    public void LibraryAndTheoryRespectChangeScopeAndLineLimits(string path, int lines, RawChangeKind kind, int expected)
    {
        var fixture = new RuleFixture();
        fixture.Baseline[path] = new string('\n', lines);
        if (kind != RawChangeKind.Deleted) fixture.Files[path] = new string('\n', lines);
        var changes = RawChangeSet.CreateWithKinds([(path, kind)]);
        Assert.Equal(expected, Source(fixture, changes, delta: true).ExitCode);
        Assert.Equal(0, Source(fixture, changes, delta: false).ExitCode);
    }

    [Fact]
    public void SourceKeepsInputAndPolicyFailuresSeparateFromRuleRejection()
    {
        var fixture = new RuleFixture();
        fixture.Files["unexpected/path.txt"] = "invalid path\n";
        Assert.Equal(1, Source(fixture, RawChangeSet.Create([]), delta: false).ExitCode);
        fixture.Files.Remove("unexpected/path.txt");
        fixture.Files["Meta/ci-checks.json"] = "{";
        Assert.Equal(1, Source(fixture, RawChangeSet.Create([]), delta: false).ExitCode);
        fixture.Files["Meta/FILEMAP.toml"] = "{";
        Assert.Equal(2, Source(fixture, RawChangeSet.Create([]), delta: false).ExitCode);
    }

    [Fact]
    public void DeltaUsesTouchedMembershipRatherThanNetCountOrUnrelatedPressure()
    {
        var fixture = new RuleFixture();
        for (var i = 0; i < 97; i++)
            fixture.Files[$"Library/notes/Note{i}.md"] = fixture.Baseline[$"Library/notes/Note{i}.md"] = "note\n";
        var unrelated = RawChangeSet.Create(["docs/develop/theory/Note.md"]);
        fixture.Files["docs/develop/theory/Note.md"] = "theory\n";
        Assert.Equal(0, Source(fixture, unrelated, delta: true).ExitCode);
        fixture.Files.Remove("Library/notes/Note0.md");
        fixture.Files["Library/notes/Renamed.md"] = "note\n";
        var rename = RawChangeSet.CreateWithKinds([("Library/notes/Note0.md", RawChangeKind.Deleted),
            ("Library/notes/Renamed.md", RawChangeKind.Added)]);
        Assert.Equal(1, Source(fixture, rename, delta: true).ExitCode);
        Assert.Equal(0, Source(fixture, rename, delta: false).ExitCode);
    }

    [Fact]
    public void ProductionGatewayReadsUntrackedAndUnstagedBytesWithoutReportOrIndexMutation()
    {
        using var directory = new TemporaryDirectory();
        var root = Path.Combine(directory.Path, "source prerequisite with spaces");
        Directory.CreateDirectory(root);
        var fixture = new RuleFixture();
        foreach (var (path, text) in fixture.Files) Write(path, text);
        string Git(params string[] args)
        {
            var result = TestProcessRunner.Run("git", args, root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }
        Git("init", "-q");
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var baseline = Git("rev-parse", "HEAD");
        var index = Git("ls-files", "--stage");
        Assert.Equal(0, Run().ExitCode);
        Write("docs/develop/theory/Untracked.md", new string('\n', 5001));
        Assert.Equal(1, Run().ExitCode);
        Write("docs/develop/theory/Untracked.md", new string('\n', 5000));
        Assert.Equal(0, Run().ExitCode);
        Write(RuleFixture.RingPath, fixture.Files[RuleFixture.RingPath] + new string('\n', 1001));
        Assert.Equal(1, Run().ExitCode);
        Assert.Equal(index, Git("ls-files", "--stage"));
        Assert.Equal(baseline, Git("rev-parse", "HEAD"));
        Assert.False(Directory.Exists(Path.Combine(root, ".lake")));

        void Write(string path, string text)
        {
            var destination = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, text);
        }
        StrataLint.Runtime.ProcessOutput Run() => TestProcessRunner.Run("dotnet",
            [typeof(StrataLint.Cli.Program).Assembly.Location, "check-source", "--current", "--protected-base", baseline],
            root, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
    }

    private static ExplicitCommandResult Source(RuleFixture fixture, RawChangeSet changes, bool delta)
    {
        static RawRepositorySnapshot Snapshot(Dictionary<string, string> files) =>
            RawRepositorySnapshot.Create(files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var gateway = new FakeRepositoryGateway(changes, Snapshot(fixture.Files), Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment("/fixture", gateway, new FakeLeanReportSource(null));
        return environment.CheckSource(delta ? ["--current", "--protected-base", new string('a', 40)] : ["--current"]);
    }
}
