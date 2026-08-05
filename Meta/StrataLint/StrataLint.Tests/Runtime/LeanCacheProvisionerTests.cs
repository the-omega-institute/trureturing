using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean cache budget environment")]
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
            var root = Path.Combine(target.Path, "worktree");
            Directory.CreateDirectory(Path.Combine(donor.Path, ".lake"));
            Directory.CreateDirectory(root);
            var runner = new RecordingWorktreeProcessRunner
            {
                FailClonefile = true,
                FailCopy = true,
            };

            LeanCacheProvisioner.Provision(
                new LeanCacheDonorSelection(donor.Path, null),
                root,
                runner);

            var provisioning = runner.Invocations
                .Where(static call => call.FileName is "cp" or "lake")
                .ToArray();
            Assert.Equal(3, provisioning.Length);
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
            var root = Path.Combine(target.Path, "worktree");
            Directory.CreateDirectory(root);
            var runner = new RecordingWorktreeProcessRunner();

            LeanCacheProvisioner.Provision(
                new LeanCacheDonorSelection(null, "fixture has no donor"),
                root,
                runner);

            var cacheGet = Assert.Single(
                runner.Invocations,
                static call => call.FileName == "lake");
            Assert.Equal(expectedSeconds, cacheGet.Timeout.TotalSeconds);
        });
    }

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

[CollectionDefinition("Lean cache budget environment", DisableParallelization = true)]
public sealed class LeanCacheBudgetEnvironmentCollection;
