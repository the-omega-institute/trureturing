using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheProvisionerTests
{
    private const string BudgetVariable = "STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS";

    [Fact]
    public void DefaultBudgetRemainsThirtyMinutes()
    {
        AssertCacheGetBudget(null, 1800);
    }

    [Fact]
    public void ConfiguredBudgetAppliesToEveryProvisioningProcess()
    {
        WithBudget("5400", () =>
        {
            using var donor = new TemporaryDirectory();
            using var target = new TemporaryDirectory();
            using var sharedCache = new MathlibCacheFixture();
            var root = Path.Combine(target.Path, "worktree");
            Directory.CreateDirectory(root);
            WritePins(donor.Path);
            WritePins(root);
            var donorLake = Path.Combine(donor.Path, ".lake");
            Directory.CreateDirectory(donorLake);
            var pins = ReadPins(root);
            LeanCacheStamp.Write(donorLake, pins);
            var runner = new RecordingWorktreeProcessRunner
            {
                FailClonefile = true,
                FailCopy = true,
            };

            LeanCacheProvisioner.Provision(
                new LeanCacheDonorSelection(donor.Path, null),
                root,
                pins,
                runner);

            var provisioning = runner.Invocations
                .Where(static call => call.FileName is "cp" or "lake")
                .ToArray();
            Assert.Equal(4, provisioning.Length);
            Assert.All(provisioning, static call => Assert.Equal(5400, call.Timeout.TotalSeconds));
        });
    }

    [Theory]
    [InlineData("invalid", 1800)]
    [InlineData("1", 300)]
    [InlineData("9000", 7200)]
    public void ConfiguredBudgetUsesInvariantParsingAndClamps(string raw, int expectedSeconds)
    {
        AssertCacheGetBudget(raw, expectedSeconds);
    }

    private static void AssertCacheGetBudget(string? raw, int expectedSeconds)
    {
        WithBudget(raw, () =>
        {
            using var target = new TemporaryDirectory();
            using var sharedCache = new MathlibCacheFixture();
            var root = Path.Combine(target.Path, "worktree");
            Directory.CreateDirectory(root);
            WritePins(root);
            var runner = new RecordingWorktreeProcessRunner();

            LeanCacheProvisioner.Provision(
                new LeanCacheDonorSelection(null, "fixture has no donor"),
                root,
                ReadPins(root),
                runner);

            var cacheGet = Assert.Single(
                runner.Invocations,
                static call => call.FileName == "lake"
                    && call.Arguments.SequenceEqual(["exe", "cache", "get"]));
            Assert.Equal(expectedSeconds, cacheGet.Timeout.TotalSeconds);
        });
    }

    private static void WritePins(string root)
    {
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), "{\"version\":\"1.1.0\"}\n");
    }

    private static LeanPinSet ReadPins(string root) =>
        LeanPinSet.TryReadWorktree(root, out var reason)
        ?? throw new InvalidOperationException(reason);

    private static void WithBudget(string? value, Action action)
    {
        var previous = Environment.GetEnvironmentVariable(BudgetVariable);
        Environment.SetEnvironmentVariable(BudgetVariable, value);
        try
        {
            action();
        }
        finally
        {
            Environment.SetEnvironmentVariable(BudgetVariable, previous);
        }
    }
}

[CollectionDefinition("Lean cache environment", DisableParallelization = true)]
public sealed class LeanCacheEnvironmentCollection;
