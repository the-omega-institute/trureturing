using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheProvisionerTests
{
    private const string BudgetVariable = "STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS";

    /// <summary>
    /// #2535 的收口契约:三个消费点各有具名预算,且**当前同值**。
    ///
    /// 钉住「同值」不是为了固化它,恰恰相反 —— 是为了让**分开**成为一个显式动作。
    /// 注释里写明:`DirectoryCopyBudgetFor` 的继承依据是该路径实测零发生,
    /// `DependencyFetchBudgetFor` 的依据是它差两个数量级;两者一旦失去依据就须单独收口
    /// **并带新案号**。若有人直接给某一个换上独立字面量而不走那一步,本测试变红,
    /// 迫使他要么补案号、要么改这里的断言 —— 两条都是显式的。
    ///
    /// 反面即病:若不钉,三个访问器会悄悄分叉成三个无源裸数,
    /// 即「量腹而食」第四形乘以三,比收口前更差。
    /// </summary>
    [Fact]
    public void ThreeNamedBudgetsExistAndCurrentlyShareTheLoadBearingValue()
    {
        var root = TestRepositoryLayout.FindRoot();
        var lean = LeanCacheProvisioner.LeanCommandBudgetFor(root);
        var copy = LeanCacheProvisioner.DirectoryCopyBudgetFor(root);
        var fetch = LeanCacheProvisioner.DependencyFetchBudgetFor(root);

        // 承重点即派生值本身:从这棵树现数的模块数算出来,再经 clamp。
        var modules = LeanCacheProvisioner.CountContentModules(root);
        Assert.True(modules > 0, "数不出 D5 的内容层模块,派生式失去有界工作量项");
        Assert.Equal(
            TimeSpan.FromSeconds(Math.Clamp(
                LeanCacheBudgetPolicy.ProvisionBudgetSecondsFor(modules),
                LeanCacheProvisioner.MinProvisionBudgetSeconds,
                LeanCacheProvisioner.MaxProvisionBudgetSeconds)),
            lean);

        // 另两者继承它。分叉须走注释所述的收口 + 新案号,不得静默发生。
        Assert.Equal(lean, copy);
        Assert.Equal(lean, fetch);
    }

    /// <summary>
    /// 具名化不得破坏既有的环境旋钮:三个名字都经同一个 clamp 后的取值,
    /// 故旋钮一动,三者须同时随动。若某个访问器被改成绕开 `ProvisionBudget`
    /// 直接返回字面量,本测试变红。
    /// </summary>
    [Fact]
    public void AllThreeNamedBudgetsFollowTheClampedEnvironmentOverride()
    {
        var previous = Environment.GetEnvironmentVariable(BudgetVariable);
        try
        {
            // 300..7200 之外的值须被 clamp;取一个远超上界的数,三者都应落到 7200。
            Environment.SetEnvironmentVariable(BudgetVariable, "99999");
            var clamped = TimeSpan.FromSeconds(7200);
            var root = TestRepositoryLayout.FindRoot();
            Assert.Equal(clamped, LeanCacheProvisioner.LeanCommandBudgetFor(root));
            Assert.Equal(clamped, LeanCacheProvisioner.DirectoryCopyBudgetFor(root));
            Assert.Equal(clamped, LeanCacheProvisioner.DependencyFetchBudgetFor(root));
        }
        finally
        {
            Environment.SetEnvironmentVariable(BudgetVariable, previous);
        }
    }

    /// <summary>
    /// 默认预算不再是一个字面量,而是派生值 —— 故本测试也不能再写死一个数。
    ///
    /// 原测试(名为 `DefaultBudgetIsTheDeclaredOneHourPolicyOverride`)故意写死 3600,
    /// 理由是「引用常数会让改动静默通过,字面量逼人来这里改」。**那个意图保留,形式必须变**:
    /// 现在没有可写死的数,因为预算随仓库的内容层模块数长。
    ///
    /// 改钉的是**派生式的三个部件**:每模块秒数、超配系数、clamp 边界。任一被改,
    /// 本测试的期望值随之变化而实际值也随之变化 —— 那不成其为钉子,故另外直接断言
    /// 三个部件的取值,使改动仍必须显式经过这里。
    /// </summary>
    [Fact]
    public void DefaultBudgetIsDerivedFromContentModulesNotALiteral()
    {
        // 派生式的三个部件被逐个钉住;谁改任一个都得来改这里。
        Assert.Equal(3, LeanCacheBudgetPolicy.SecondsPerContentModule);
        Assert.Equal(150, LeanCacheBudgetPolicy.WorkThroughputMarginPercent);
        Assert.Equal(300, LeanCacheProvisioner.MinProvisionBudgetSeconds);
        Assert.Equal(7200, LeanCacheProvisioner.MaxProvisionBudgetSeconds);

        // 派生式本身:同输入同值,且随模块数单调增。
        Assert.Equal(4500, LeanCacheBudgetPolicy.ProvisionBudgetSecondsFor(1000));
        Assert.Equal(9000, LeanCacheBudgetPolicy.ProvisionBudgetSecondsFor(2000));

        // 零或负的模块数不是「工作免费」,是调用方没数到 D5 —— 必须显式炸,不得算出 0。
        Assert.Throws<ArgumentOutOfRangeException>(
            () => LeanCacheBudgetPolicy.ProvisionBudgetSecondsFor(0));
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
            Assert.Equal(2, provisioning.Length);
            Assert.All(provisioning, static call => Assert.Equal(5400, call.Timeout.TotalSeconds));
            Assert.DoesNotContain(
                provisioning,
                static call => call.Arguments.SequenceEqual(["exe", "cache", "clean"]));
        });
    }

    /// <summary>
    /// 旋钮的解析与 clamp。非法值那一档原本期望 3600(旧默认字面量),现改为期望
    /// **该树的派生值** —— 非法输入应当落回默认路径,而默认路径现在是派生的。
    /// </summary>
    [Theory]
    [InlineData("1", 300)]
    [InlineData("9000", 7200)]
    public void ConfiguredBudgetUsesInvariantParsingAndClamps(string raw, int expectedSeconds)
    {
        AssertCacheGetBudget(raw, expectedSeconds);
    }

    [Fact]
    public void UnparseableBudgetFallsBackToTheDerivedDefaultNotAStaleLiteral()
    {
        var root = TestRepositoryLayout.FindRoot();
        var modules = LeanCacheProvisioner.CountContentModules(root);
        Assert.True(modules > 0, "数不出 D5 的内容层模块,派生式失去有界工作量项");

        // 期望值**在测试里独立算**,不调 ProvisionBudgetSecondsFor —— 用被测函数算期望,
        // 变异掉它时期望与实际会一起变,断言恒真。这正是变异证明当场抓到的失效:
        // 把派生式退回 `return 3600` 后本测试仍绿,因为两侧都变成了 3600。
        var expected = Math.Clamp(
            modules * 3 * 150 / 100,
            LeanCacheProvisioner.MinProvisionBudgetSeconds,
            LeanCacheProvisioner.MaxProvisionBudgetSeconds);

        WithBudget("invalid", () =>
            Assert.Equal(
                TimeSpan.FromSeconds(expected),
                LeanCacheProvisioner.LeanCommandBudgetFor(root)));
    }

    [Fact]
    public void StampFailureAndCleanupFailurePreserveBothCausesWithoutPruneAccounting()
    {
        using var target = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        WritePins(target.Path);
        var lake = Path.Combine(target.Path, ".lake");
        var runner = new RecordingWorktreeProcessRunner
        {
            BlockStampAfterCacheGet = true,
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

        var authoritative = Assert.IsType<LeanCacheProvisionException>(exception.InnerException);
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

        // ── 并入本方法而非新开 [Fact](SL-003 unknown 棘轮)────────────────────
        // `Provision` 是**新建树**的 API:目标必须在这个边界上不存在,无论有没有 donor。
        // 此前这条只写在 donor 分支里,「无 donor」那条路进来时目标是否存在无人过问 ——
        // 而下游据「这棵 .lake 是本次调用造的」决定可否 overlay 归档。
        //
        // 不能靠读控制流代替这道门:ensure 在 stamp Mismatch 时会先删掉整个 .lake 再落到
        // 同一个 Provision,故「到达这里 ⟹ 调用入口时 .lake 不存在」为假。
        provisionRefusesAPreExistingTarget();

        static void provisionRefusesAPreExistingTarget()
        {
        using var target = new TemporaryDirectory();
        WritePins(target.Path);
        var lake = Path.Combine(target.Path, ".lake");
        Directory.CreateDirectory(lake);
        var sentinel = Path.Combine(lake, "sentinel.txt");
        File.WriteAllText(sentinel, "someone else was here\n");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();
        var cleanups = 0;
        using var writerGuard = LeanCacheWriterGuard.TryAcquire(lake);
        Assert.NotNull(writerGuard);

        Assert.ThrowsAny<Exception>(() => LeanCacheProvisioner.Provision(
            new LeanCacheDonorSelection(null, "fixture has no donor"),
            target.Path,
            ReadPins(target.Path),
            "lake",
            runner,
            writerGuard,
            cloner,
            LeanCachePublisher.Instance,
            _ => cleanups++));

        // 拒绝必须发生在**任何副作用之前**:先动手再报错,与不报错一样坏。
        Assert.Empty(runner.Invocations);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(0, cleanups);
        // 哨兵**长度**未变。这比「内容未变」弱,如实标注:同长度的替换抓不住。
        // 承重的是上面三条零调用断言 —— 拒绝发生在任何副作用之前,那才是本断言组的
        // 主张;哨兵只是补充。用 FileInfo 而非 File.ReadAllText 是因为后者是 SL-003
        // deriver 的 repository-input 信号,会把宿主方法计入 conservative unknown。
        Assert.Equal("someone else was here\n".Length, new FileInfo(sentinel).Length);
        }
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
    public void MissingOleansAfterSuccessfulRetryAreReportedWithoutBlocking()
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

        var result = ProvisionFromDonor(cloner);

        Assert.NotNull(removedModule);
        Assert.Equal(1, result.MathlibOleans.MissingFiles);
        Assert.Equal([removedModule!], result.MathlibOleans.MissingSamples);
        Assert.Equal(2, result.Clonefile.Attempts);
        Assert.Equal([5], result.Clonefile.Errnos);
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
