using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed partial class LeanCacheProvisionerTests
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
            if (file.Contains("sandbox-exec", StringComparison.Ordinal) || args.FirstOrDefault() != "--version")
                Budgets.Add(budget);
            return inner.RunWithEnvironment(file, args, root, budget, environment);
        }
    }
}
