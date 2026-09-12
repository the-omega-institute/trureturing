using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed partial class LeanCacheProvisionerTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Fact]
    public void PublicationFallsBackToIndependentCopyAndLeavesOldMapsOnRenameFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var stage = Path.Combine(temporary.Path, "stage");
        var shared = Path.Combine(temporary.Path, "shared");
        Directory.CreateDirectory(Path.Combine(stage, "artifacts"));
        Directory.CreateDirectory(Path.Combine(stage, "outputs", "pkg"));
        File.WriteAllText(Path.Combine(stage, "artifacts", "blob.art"), "blob");
        const string map = "{\"schemaVersion\":\"2026-02-25\",\"service\":null,\"data\":[]}";
        File.WriteAllText(Path.Combine(stage, "outputs", "pkg", "old.json"), map);
        var cloner = new RecordingDirectoryCloner { FailureReason = "unsupported filesystem" };
        var runner = new ProductionWorktreeProcessRunner();
        var counts = LeanArtifactPublisher.Publish(stage, shared, temporary.Path, temporary.Path, runner, cloner);
        Assert.Equal((1, 1), counts);
        File.WriteAllText(Path.Combine(stage, "artifacts", "blob.art"), "mutated stage");
        Assert.Equal("blob", File.ReadAllText(Path.Combine(shared, "artifacts", "blob.art")));
        Directory.CreateDirectory(Path.Combine(stage, "outputs", "blocked"));
        File.WriteAllText(Path.Combine(stage, "outputs", "blocked", "new.json"), map);
        File.WriteAllText(Path.Combine(shared, "outputs", "blocked"), "obstruction");
        Assert.Throws<IOException>(() => LeanArtifactPublisher.Publish(stage, shared, temporary.Path, temporary.Path, runner, cloner));
        Assert.Equal(map, File.ReadAllText(Path.Combine(shared, "outputs", "pkg", "old.json")));
        Assert.Equal("blob", File.ReadAllText(Path.Combine(shared, "artifacts", "blob.art")));
        Assert.Empty(Directory.GetDirectories(temporary.Path, ".stratalint-lake-publish-*"));
        File.WriteAllText(Path.Combine(stage, "outputs", "pkg", "old.json"), "incomplete");
        Assert.ThrowsAny<System.Text.Json.JsonException>(() => LeanArtifactPublisher.Publish(
            stage, shared, temporary.Path, temporary.Path, runner, cloner));
        Assert.Equal(map, File.ReadAllText(Path.Combine(shared, "outputs", "pkg", "old.json")));
        Assert.Equal("blob", File.ReadAllText(Path.Combine(shared, "artifacts", "blob.art")));
    }

    [Fact]
    public void NativeReaderSurvivesPartialAtomicPublication()
    {
        using var fixture = new SharedLakeFixture(native: true);
        if (!OperatingSystem.IsMacOS())
        {
            Assert.False(fixture.Command(fixture.Main, "warm-cache").Success);
            Assert.False(Directory.Exists(Path.Combine(fixture.Main, ".git", "stratalint-lake")));
            return;
        }
        var warmed = fixture.Command(fixture.Main, "warm-cache");
        Assert.True(warmed.Success, warmed.Error);
        var pins = LeanPinSet.TryReadWorktree(fixture.Main, out _)!;
        var runner = new ProductionWorktreeProcessRunner();
        var shared = LeanProcessPolicy.Create(fixture.Main, pins, runner).SharedCache;
        var oldMaps = Directory.GetFiles(Path.Combine(shared, "outputs"), "*.json", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        var oldArtifacts = Directory.GetFiles(Path.Combine(shared, "artifacts"));
        Assert.Equal(3, oldArtifacts.Length);
        File.WriteAllText(Path.Combine(fixture.Main, "Fixture.lean"), "def answer : Nat := 43\n");
        fixture.Git(fixture.Main, "add", "Fixture.lean");
        fixture.Git(fixture.Main, "commit", "-m", "new native output");
        fixture.Git(fixture.Main, "push", "origin", "dev");
        var cloner = new PublicationObstruction(shared);
        var failed = WorktreeCommand.Run(fixture.Main, ["warm-cache"], runner, cloner);
        Assert.False(failed.Success);
        Assert.Contains("Atomic cache publication failed", failed.Error);
        Assert.True(cloner.Obstructed);
        var artifactsAfter = Directory.GetFiles(Path.Combine(shared, "artifacts")).Length;
        Assert.True(artifactsAfter > oldArtifacts.Length);
        foreach (var (path, bytes) in oldMaps) Assert.Equal(bytes, File.ReadAllBytes(path));
        var beforeRead = Snapshot(shared);
        var reader = fixture.Command(fixture.Reader, "with-cache-reader", "--", "lake", "build", "-v");
        Assert.True(reader.Success, reader.Error);
        Assert.Contains("Reused Fixture", reader.Output);
        Assert.DoesNotContain("Built Fixture", reader.Output);
        Assert.True(File.Exists(Path.Combine(fixture.Reader, ".lake", "build", "lib", "lean", "Fixture.olean")));
        Assert.Equal(beforeRead, Snapshot(shared));
        output.WriteLine($"native atomic rename failed after artifacts {oldArtifacts.Length}->{artifactsAfter}; "
            + $"old mappings preserved={oldMaps.Count}; old reader exit=0, Reused=1, Built=0; shared mutations=0");
    }

    private static byte[] Snapshot(string shared)
    {
        const string program = """
            import sys,pathlib,json,hashlib
            root=pathlib.Path(sys.argv[1]); rows={}
            for p in [root,*sorted(root.rglob('*'))]:
                s=p.lstat()
                rows[str(p.relative_to(root))]=[s.st_mode,s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_nlink,s.st_ino,
                    hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None]
            print(json.dumps(rows,sort_keys=True))
            """;
        var result = TestProcessRunner.Run("python3", ["-c", program, shared], shared,
            TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.Equal(0, result.ExitCode);
        return result.StandardOutput;
    }

    private sealed class PublicationObstruction(string shared) : IDirectoryCloner
    {
        internal bool Obstructed { get; private set; }
        public DirectoryCloneResult Clone(string source, string target)
        {
            var copied = TestProcessRunner.Run("cp", ["-R", source, target], Path.GetDirectoryName(source)!,
                TestBudgets.LeanProcessHangGuard, 1024 * 1024);
            Assert.Equal(0, copied.ExitCode);
            if (Path.GetFileName(target).StartsWith(".stratalint-lake-publish-", StringComparison.Ordinal))
            {
                var newMap = Directory.GetFiles(Path.Combine(target, "outputs"), "*.json", SearchOption.AllDirectories)
                    .Select(path => Path.Combine(shared, Path.GetRelativePath(target, path)))
                    .First(path => !File.Exists(path));
                // Fault occurs after native staging, at the real rename destination. Blobs
                // must publish first; the old reader then consumes the retained native map.
                Directory.CreateDirectory(newMap);
                Obstructed = true;
            }
            return new(true, null, null);
        }
    }

    private static void AssertCacheGetBudget(string? raw, int expectedSeconds) => WithBudget(raw, () =>
    {
        Assert.Equal(expectedSeconds, LeanCacheProvisioner.DependencyFetchBudget.TotalSeconds);
        Assert.Equal(expectedSeconds, LeanCacheProvisioner.LeanCommandBudget.TotalSeconds);
    });

    private static void WithBudget(string? value, Action action)
    {
        var previous = Environment.GetEnvironmentVariable(BudgetVariable);
        try
        {
            Environment.SetEnvironmentVariable(BudgetVariable, value);
            action();
        }
        finally { Environment.SetEnvironmentVariable(BudgetVariable, previous); }
    }

    private sealed class BudgetRunner : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner inner = new();
        internal List<TimeSpan> Budgets { get; } = [];
        public ProcessOutput Run(string file, IReadOnlyList<string> args, string root, TimeSpan budget) =>
            inner.Run(file, args, root, budget);
        public ProcessOutput RunWithEnvironment(string file, IReadOnlyList<string> args, string root,
            TimeSpan budget, IReadOnlyDictionary<string, string> environment)
        {
            if (file != "git" && args.FirstOrDefault() != "--version")
                Budgets.Add(budget);
            return inner.RunWithEnvironment(file, args, root, budget, environment);
        }
    }
}
