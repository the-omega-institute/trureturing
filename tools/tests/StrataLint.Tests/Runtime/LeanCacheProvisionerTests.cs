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
                FailCopy = true,
            };
            using var writerGuard = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
            Assert.NotNull(writerGuard);

            LeanCacheProvisioner.Provision(
                new LeanCacheDonorSelection(donor.Path, null),
                root,
                pins,
                runner,
                writerGuard,
                new RecordingDirectoryCloner { FailureReason = "clonefile unavailable" });

            var provisioning = runner.Invocations
                .Where(static call => call.FileName is "cp" or "lake")
                .ToArray();
            Assert.Equal(3, provisioning.Length);
            Assert.All(provisioning, static call => Assert.Equal(5400, call.Timeout.TotalSeconds));
            Assert.DoesNotContain(provisioning, static call => call.Arguments.Contains("-c"));
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

    [Theory]
    [InlineData(false, false, "succeeded")]
    [InlineData(true, false, "failed")]
    [InlineData(false, true, "failed")]
    public void PostCleanInventoryFailurePreservesTheAuthoritativeCleanState(
        bool cleanReturnsFailure,
        bool cleanThrows,
        string expectedStatus)
    {
        using var target = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        WritePins(target.Path);
        var lake = Path.Combine(target.Path, ".lake");
        MathlibProjectionFixture.Write(lake);
        var runner = new RecordingWorktreeProcessRunner
        {
            FailClean = cleanReturnsFailure,
            ThrowClean = cleanThrows,
        };
        var inventoryCalls = 0;
        int CountFiles(string _)
        {
            inventoryCalls++;
            if (inventoryCalls == 1) return 2;
            throw new IOException("post-clean inventory unavailable");
        }
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(lake);
        Assert.NotNull(writerGuard);

        var exception = Assert.Throws<LeanCacheProvisionException>(() =>
            LeanCacheProvisioner.ReproduceExisting(
                target.Path,
                ReadPins(target.Path),
                runner,
                writerGuard,
                CountFiles));

        Assert.Equal(2, inventoryCalls);
        Assert.Equal("machine", exception.PruneOutcome.Scope);
        Assert.Null(exception.PruneOutcome.DeletedFiles);
        Assert.Equal(expectedStatus, exception.PruneOutcome.CleanStatus);
    }

    [Fact]
    public void ProvisionRejectsAWriterGuardForAnotherPhysicalTargetBeforeCallingDependencies()
    {
        using var owner = new TemporaryDirectory();
        using var donor = new TemporaryDirectory();
        using var target = new TemporaryDirectory();
        WritePins(donor.Path);
        WritePins(target.Path);
        var donorLake = Path.Combine(donor.Path, ".lake");
        MathlibProjectionFixture.Write(donorLake);
        LeanCacheStamp.Write(donorLake, ReadPins(donor.Path));
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();
        using var selection = new LeanCacheDonorSelection(donor.Path, null);
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(Path.Combine(owner.Path, ".lake"));
        Assert.NotNull(writerGuard);

        var exception = Assert.Throws<InvalidOperationException>(() =>
            LeanCacheProvisioner.Provision(
                selection,
                target.Path,
                ReadPins(target.Path),
                runner,
                writerGuard,
                cloner));

        Assert.Contains("not the requested target", exception.Message, StringComparison.Ordinal);
        Assert.Empty(runner.Invocations);
        Assert.Empty(cloner.Invocations);
    }

    [Fact]
    public void ReproduceRejectsAWriterGuardForAnotherPhysicalTargetBeforeCallingRunner()
    {
        using var owner = new TemporaryDirectory();
        using var target = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        WritePins(target.Path);
        var runner = new RecordingWorktreeProcessRunner();
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(Path.Combine(owner.Path, ".lake"));
        Assert.NotNull(writerGuard);

        var exception = Assert.Throws<InvalidOperationException>(() =>
            LeanCacheProvisioner.ReproduceExisting(
                target.Path,
                ReadPins(target.Path),
                runner,
                writerGuard));

        Assert.Contains("not the requested target", exception.Message, StringComparison.Ordinal);
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void CopiedStampIsAbsentAtThePostRenamePreStampFailurePoint()
    {
        using var donor = new TemporaryDirectory();
        using var target = new TemporaryDirectory();
        WritePins(donor.Path);
        WritePins(target.Path);
        var donorLake = Path.Combine(donor.Path, ".lake");
        MathlibProjectionFixture.Write(donorLake);
        LeanCacheStamp.Write(donorLake, ReadPins(donor.Path));
        var runner = new RecordingWorktreeProcessRunner();
        var publisher = new RenameThenFailLeanCachePublisher();
        using var selection = new LeanCacheDonorSelection(donor.Path, null);
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(Path.Combine(target.Path, ".lake"));
        Assert.NotNull(writerGuard);

        Assert.Throws<IOException>(() => LeanCacheProvisioner.Provision(
            selection,
            target.Path,
            ReadPins(target.Path),
            runner,
            writerGuard,
            new RecordingDirectoryCloner(),
            publisher));

        Assert.True(publisher.Invoked);
        Assert.False(publisher.StampExistedAfterRename);
        Assert.False(Directory.Exists(Path.Combine(target.Path, ".lake")));
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
            using var writerGuard = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
            Assert.NotNull(writerGuard);

            LeanCacheProvisioner.Provision(
                new LeanCacheDonorSelection(null, "fixture has no donor"),
                root,
                ReadPins(root),
                runner,
                writerGuard);

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

internal sealed class RenameThenFailLeanCachePublisher : ILeanCachePublisher
{
    internal bool Invoked { get; private set; }

    internal bool StampExistedAfterRename { get; private set; }

    public void Publish(string staged, string target, LeanPinSet pins)
    {
        Invoked = true;
        Directory.Move(staged, target);
        StampExistedAfterRename = File.Exists(LeanCacheStamp.PathFor(target));
        throw new IOException("failure injected after rename and before stamp publication");
    }
}

[CollectionDefinition("Lean cache environment", DisableParallelization = true)]
public sealed class LeanCacheEnvironmentCollection;
