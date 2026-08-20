using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheProvisionerTests
{
    private const string BudgetVariable = "STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS";

    [Fact]
    public void DefaultBudgetIsTheDeclaredOneHourPolicyOverride()
    {
        // Pinned to the policy-override declared on
        // LeanCacheProvisioner.DefaultProvisionBudgetSeconds. Changing this number
        // means retiring or revising that declaration, not editing a literal.
        AssertCacheGetBudget(null, 3600);
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
                "lake",
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
    [InlineData("invalid", 3600)]
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
                "lake",
                runner,
                writerGuard,
                CountFiles));

        Assert.Equal(2, inventoryCalls);
        Assert.Equal("machine", exception.PruneOutcome.Scope);
        Assert.Null(exception.PruneOutcome.DeletedFiles);
        Assert.Equal(expectedStatus, exception.PruneOutcome.CleanStatus);
    }

    [Fact]
    public void UnknownPostCleanInventoryIsNullInTheCommandReceipt()
    {
        using var target = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        WritePins(target.Path);
        MathlibProjectionFixture.Write(Path.Combine(target.Path, ".lake"));
        var runner = new RecordingWorktreeProcessRunner();
        var inventoryCalls = 0;
        int CountFiles(string _)
        {
            inventoryCalls++;
            if (inventoryCalls == 1) return 2;
            throw new IOException("post-clean inventory unavailable");
        }

        var result = LeanCacheEnsureCommand.Run(
            target.Path,
            [],
            runner,
            new RecordingDirectoryCloner(),
            CountFiles);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal(2, inventoryCalls);
        using var receipt = JsonDocument.Parse(result.Error["LEAN_CACHE ".Length..]);
        Assert.True(receipt.RootElement.TryGetProperty("mathlib_cache_pruned_files", out var prunedFiles));
        Assert.Equal(JsonValueKind.Null, prunedFiles.ValueKind);
        Assert.Equal("succeeded", receipt.RootElement.GetProperty("mathlib_cache_clean_status").GetString());
    }

    [Fact]
    public void CleanupFailureCannotMaskTheAuthoritativePruneOutcome()
    {
        using var target = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        WritePins(target.Path);
        var lake = Path.Combine(target.Path, ".lake");
        var runner = new RecordingWorktreeProcessRunner
        {
            BlockStampAfterClean = true,
        };
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(lake);
        Assert.NotNull(writerGuard);

        var exception = Assert.Throws<LeanCacheProvisionException>(() =>
            LeanCacheProvisioner.Provision(
                new LeanCacheDonorSelection(null, "fixture has no donor"),
                target.Path,
                ReadPins(target.Path),
                "lake",
                runner,
                writerGuard,
                new RecordingDirectoryCloner(),
                LeanCachePublisher.Instance,
                _ => throw new IOException("partial cache cleanup failed")));

        Assert.Equal("machine", exception.PruneOutcome.Scope);
        Assert.Equal(1, exception.PruneOutcome.DeletedFiles);
        Assert.Equal("succeeded", exception.PruneOutcome.CleanStatus);
        var authoritative = Assert.IsType<LeanCacheProvisionException>(exception.InnerException);
        Assert.Equal(exception.PruneOutcome, authoritative.PruneOutcome);
        var aggregate = Assert.IsType<AggregateException>(authoritative.InnerException);
        Assert.Contains(
            aggregate.InnerExceptions,
            static inner => inner is LeanCacheProvisionException
                && inner.Message.Contains("stamp publication failed", StringComparison.Ordinal));
        Assert.Contains(
            aggregate.InnerExceptions,
            static inner => inner is IOException
                && inner.Message.Contains("partial cache cleanup failed", StringComparison.Ordinal));
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
                "lake",
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
                "lake",
                runner,
                writerGuard,
                LeanCacheProvisioner.CountLtarFiles));

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
        var observerInvoked = false;
        var stampExistedAfterRename = true;
        var publisher = new LeanCachePublisher(canonical =>
        {
            observerInvoked = true;
            stampExistedAfterRename = File.Exists(LeanCacheStamp.PathFor(canonical));
            throw new IOException("failure injected after rename and before stamp publication");
        });
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
            [
                new(false, true, 5, 1, "clonefile(2) failed: EIO"),
                new(true, false, null, 1, null),
            ]),
        };
        using var selection = new LeanCacheDonorSelection(donor.Path, null);
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(Path.Combine(target.Path, ".lake"));
        Assert.NotNull(writerGuard);
        var cleanupCalls = 0;
        void Remove(string path)
        {
            cleanupCalls++;
            if (cleanupCalls == 2) throw new IOException("publication staging cleanup failed");
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }

        var exception = Assert.Throws<LeanCacheProvisionException>(() => LeanCacheProvisioner.Provision(
            selection,
            target.Path,
            ReadPins(target.Path),
            "lake",
            runner,
            writerGuard,
            cloner,
            publisher,
            Remove,
            static _ => { }));

        Assert.True(observerInvoked);
        Assert.False(stampExistedAfterRename);
        Assert.False(Directory.Exists(Path.Combine(target.Path, ".lake")));
        Assert.Equal(2, exception.Clonefile.Attempts);
        Assert.Equal([5], exception.Clonefile.Errnos);
        Assert.Contains("publication staging cleanup failed", exception.Clonefile.CleanupError, StringComparison.Ordinal);
        Assert.IsType<IOException>(exception.InnerException);
    }

    [Fact]
    public void CompletenessFailureAfterSuccessfulRetryPreservesReceiptAndMissingDetails()
    {
        string? removedModule = null;
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
            [
                new(false, true, 5, 1, "clonefile(2) failed: EIO"),
                new(true, false, null, 1, null),
            ]),
            AfterClone = (_, staged) =>
            {
                if (!Directory.Exists(staged)) return;
                removedModule = MathlibProjectionFixture.FirstModule;
                var relative = removedModule.Replace('/', Path.DirectorySeparatorChar);
                var firstOlean = Path.Combine(
                    staged,
                    "packages",
                    "mathlib",
                    ".lake",
                    "build",
                    "lib",
                    "lean",
                    relative + ".olean");
                File.Delete(firstOlean);
            },
        };

        var exception = Assert.Throws<MathlibOleanCompletenessException>(() =>
            ProvisionFromDonor(cloner));

        Assert.NotNull(removedModule);
        Assert.Equal(1, exception.MissingOleanFiles);
        Assert.Equal([removedModule!], exception.MissingOleanSamples);
        Assert.Equal(MathlibCachePruneOutcome.NotRun, exception.PruneOutcome);
        Assert.Equal(2, exception.Clonefile.Attempts);
        Assert.Equal([5], exception.Clonefile.Errnos);
    }

    [Fact]
    public void RetryableCloneFailuresUseFiveAttemptsAndCleanBeforeEveryBackoff()
    {
        var scripted = new Queue<DirectoryCloneResult>(
        [
            new(false, true, 5, 1, "clonefile(2) failed: EIO"),
            new(false, true, 5, 1, "clonefile(2) failed: EIO"),
            new(false, true, 5, 1, "clonefile(2) failed: EIO"),
            new(false, true, 5, 1, "clonefile(2) failed: EIO"),
            new(false, true, 5, 1, "clonefile(2) failed: EIO"),
        ]);
        var targetWasAbsent = new List<bool>();
        var cloner = new RecordingDirectoryCloner
        {
            Results = scripted,
            BeforeClone = (_, path) => targetWasAbsent.Add(!Directory.Exists(path)),
            AfterClone = (_, path) => Directory.CreateDirectory(path),
        };
        var runner = new RecordingWorktreeProcessRunner();
        var waits = new List<TimeSpan>();
        var cleanupCalls = 0;
        void Remove(string path)
        {
            cleanupCalls++;
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }
        var result = ProvisionFromDonor(cloner, runner, removePartial: Remove, wait: waits.Add);

        Assert.Equal("copy", result.Method);
        Assert.Equal(5, cloner.Invocations.Count);
        Assert.Equal([true, true, true, true, true], targetWasAbsent);
        Assert.Equal(5, cleanupCalls);
        Assert.Equal(
            [
                TimeSpan.FromMilliseconds(250),
                TimeSpan.FromMilliseconds(500),
                TimeSpan.FromMilliseconds(1000),
                TimeSpan.FromMilliseconds(2000),
            ],
            waits);
        var copy = Assert.Single(runner.Invocations, static call => call.FileName == "cp");
        Assert.Equal("-R", copy.Arguments[0]);
        Assert.Equal(5, result.Clonefile.Attempts);
        Assert.Equal([5, 5, 5, 5, 5], result.Clonefile.Errnos);
        Assert.Equal(5, result.Clonefile.LastErrno);
        Assert.Null(result.Clonefile.CleanupError);
    }

    [Fact]
    public void NonMacOsSkipsNativeClonefileAndDirectlyUsesRecursiveCopy()
    {
        var nativeCalls = 0;
        var cloner = new ApfsDirectoryCloner(
            isMacOS: static () => false,
            cloneFile: (_, _, _) =>
            {
                nativeCalls++;
                return 0;
            });
        var runner = new RecordingWorktreeProcessRunner();

        var result = ProvisionFromDonor(cloner, runner);

        Assert.Equal("copy", result.Method);
        Assert.Equal(0, nativeCalls);
        Assert.Equal(0, result.Clonefile.Attempts);
        Assert.Empty(result.Clonefile.Errnos);
        var copy = Assert.Single(runner.Invocations, static call => call.FileName == "cp");
        Assert.Equal("-R", copy.Arguments[0]);
    }

    [Fact]
    public void RecursiveCopyFailureFallsBackToCacheGet()
    {
        using var sharedCache = new MathlibCacheFixture();
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
                [new(false, false, 17, 1, "clonefile(2) failed: EEXIST")]),
        };
        var runner = new RecordingWorktreeProcessRunner { FailCopy = true };

        var result = ProvisionFromDonor(cloner, runner);

        Assert.Equal("cache-get", result.Method);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "cp" && call.Arguments[0] == "-R");
        Assert.Contains(
            runner.Invocations,
            static call => Path.GetFileName(call.FileName) == "lake"
                && call.Arguments.SequenceEqual(["exe", "cache", "get"]));
        Assert.Equal(1, result.Clonefile.Attempts);
        Assert.Equal([17], result.Clonefile.Errnos);
    }

    [Theory]
    [InlineData(false, "ordinary copy unavailable")]
    [InlineData(true, "ordinary copy threw")]
    public void RecursiveCopyFailureCleanupCannotStopFetchOrReplaceKnownCauses(
        bool copyThrows,
        string copyReason)
    {
        using var sharedCache = new MathlibCacheFixture();
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
                [new(false, true, 5, 1, "clonefile(2) failed: EIO")]),
            AfterClone = (_, staged) => Directory.CreateDirectory(staged),
        };
        var runner = new RecordingWorktreeProcessRunner
        {
            FailCopy = !copyThrows,
            ThrowCopy = copyThrows,
        };
        var cleanupCalls = 0;
        void Remove(string path)
        {
            cleanupCalls++;
            if (cleanupCalls == 1) throw new IOException("retry staging cleanup failed");
            if (cleanupCalls == 3) throw new IOException("copy staging cleanup failed");
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }

        var result = ProvisionFromDonor(cloner, runner, removePartial: Remove);

        Assert.Equal("cache-get", result.Method);
        Assert.Contains(
            runner.Invocations,
            static call => Path.GetFileName(call.FileName) == "lake"
                && call.Arguments.SequenceEqual(["exe", "cache", "get"]));
        Assert.Equal(1, result.Clonefile.Attempts);
        Assert.Equal([5], result.Clonefile.Errnos);
        Assert.Contains("retry staging cleanup failed", result.Clonefile.CleanupError, StringComparison.Ordinal);
        Assert.Contains("copy staging cleanup failed", result.Clonefile.CleanupError, StringComparison.Ordinal);
        Assert.Contains("EIO", result.Warning, StringComparison.Ordinal);
        Assert.Contains("retry staging cleanup failed", result.Warning, StringComparison.Ordinal);
        Assert.Contains(copyReason, result.Warning, StringComparison.Ordinal);
        Assert.Contains("copy staging cleanup failed", result.Warning, StringComparison.Ordinal);
    }

    [Fact]
    public void NonMacOsCopyAndCleanupFailuresStillReachFetchWithNotRunReceipt()
    {
        using var sharedCache = new MathlibCacheFixture();
        var cloner = new ApfsDirectoryCloner(
            isMacOS: static () => false,
            cloneFile: static (_, _, _) => throw new InvalidOperationException("must not call clonefile"));
        var runner = new RecordingWorktreeProcessRunner { FailCopy = true };
        var cleanupCalls = 0;
        void Remove(string path)
        {
            cleanupCalls++;
            if (cleanupCalls == 2) throw new IOException("copy staging cleanup failed");
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }

        var result = ProvisionFromDonor(cloner, runner, removePartial: Remove);

        Assert.Equal("cache-get", result.Method);
        Assert.Equal(0, result.Clonefile.Attempts);
        Assert.Empty(result.Clonefile.Errnos);
        Assert.Contains("copy staging cleanup failed", result.Clonefile.CleanupError, StringComparison.Ordinal);
        Assert.Contains("ordinary copy unavailable", result.Warning, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(13)]  // EACCES
    [InlineData(45)]  // ENOTSUP
    [InlineData(17)]  // EEXIST
    [InlineData(18)]  // EXDEV
    [InlineData(22)]  // EINVAL
    [InlineData(28)]  // ENOSPC
    [InlineData(1)]   // EPERM
    [InlineData(62)]  // ELOOP
    [InlineData(107)] // ENOTCAPABLE
    [InlineData(30)]  // EROFS
    [InlineData(63)]  // ENAMETOOLONG
    [InlineData(2)]   // ENOENT
    [InlineData(20)]  // ENOTDIR
    [InlineData(11)]  // EDEADLK
    public void ClonefileDocumentedDeterministicFailuresImmediatelyUseCopy(int errno)
    {
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
                [new(false, ApfsDirectoryCloner.IsRetryable(errno), errno, 1, $"clonefile(2) failed: errno {errno}")]),
        };
        var runner = new RecordingWorktreeProcessRunner();
        var waits = new List<TimeSpan>();
        var result = ProvisionFromDonor(cloner, runner, wait: waits.Add);

        Assert.Equal("copy", result.Method);
        Assert.Single(cloner.Invocations);
        Assert.Empty(waits);
        Assert.Contains(runner.Invocations, static call => call.FileName == "cp");
        Assert.Equal(1, result.Clonefile.Attempts);
        Assert.Equal([errno], result.Clonefile.Errnos);
    }

    [Fact]
    public void ManagedCloneExceptionDoesNotRetryBeforeCopyFallback()
    {
        var cloner = new RecordingDirectoryCloner
        {
            ExceptionToThrow = new IOException("managed clone failure"),
        };
        var waits = new List<TimeSpan>();
        var result = ProvisionFromDonor(cloner, wait: waits.Add);

        Assert.Equal("copy", result.Method);
        Assert.Single(cloner.Invocations);
        Assert.Empty(waits);
        Assert.Equal(0, result.Clonefile.Attempts);
        Assert.Empty(result.Clonefile.Errnos);
        Assert.Contains("managed clone failure", result.Warning, StringComparison.Ordinal);
    }

    [Fact]
    public void RetryCleanupFailureStopsRetriesAndPreservesBothCauses()
    {
        var scripted = new Queue<DirectoryCloneResult>(
        [
            new(false, true, 5, 1, "clonefile(2) failed: EIO"),
            new(true, false, null, 1, null),
        ]);
        var cloner = new RecordingDirectoryCloner
        {
            Results = scripted,
            AfterClone = (_, path) => Directory.CreateDirectory(path),
        };
        var cleanupCalls = 0;
        void Remove(string path)
        {
            cleanupCalls++;
            if (cleanupCalls == 1) throw new IOException("retry cleanup unavailable");
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }
        var waits = new List<TimeSpan>();
        var result = ProvisionFromDonor(cloner, removePartial: Remove, wait: waits.Add);

        Assert.Equal("copy", result.Method);
        Assert.Single(cloner.Invocations);
        Assert.Empty(waits);
        Assert.Equal(5, result.Clonefile.LastErrno);
        Assert.Equal(1, result.Clonefile.Attempts);
        Assert.Contains("EIO", result.Warning, StringComparison.Ordinal);
        Assert.Contains("retry cleanup unavailable", result.Clonefile.CleanupError, StringComparison.Ordinal);
        Assert.Contains("retry cleanup unavailable", result.Warning, StringComparison.Ordinal);
    }

    private static LeanCacheProvisionResult ProvisionFromDonor(
        IDirectoryCloner cloner,
        IWorktreeProcessRunner? runner = null,
        Action<string>? removePartial = null,
        Action<TimeSpan>? wait = null,
        ILeanCachePublisher? publisher = null)
    {
        using var donor = new TemporaryDirectory();
        using var target = new TemporaryDirectory();
        WritePins(donor.Path);
        WritePins(target.Path);
        var donorLake = Path.Combine(donor.Path, ".lake");
        MathlibProjectionFixture.Write(donorLake);
        LeanCacheStamp.Write(donorLake, ReadPins(donor.Path));
        removePartial ??= static path =>
        {
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        };
        wait ??= static _ => { };
        using var selection = new LeanCacheDonorSelection(donor.Path, null);
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(Path.Combine(target.Path, ".lake"));
        Assert.NotNull(writerGuard);
        return LeanCacheProvisioner.Provision(
            selection,
            target.Path,
            ReadPins(target.Path),
            "lake",
            runner ?? new RecordingWorktreeProcessRunner(),
            writerGuard,
            cloner,
            publisher ?? LeanCachePublisher.Instance,
            removePartial,
            wait);
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
                "lake",
                runner,
                writerGuard,
                new RecordingDirectoryCloner());

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
