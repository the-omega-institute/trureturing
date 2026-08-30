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
        var lean = LeanCacheProvisioner.LeanCommandBudget;
        var copy = LeanCacheProvisioner.DirectoryCopyBudget;
        var fetch = LeanCacheProvisioner.DependencyFetchBudget;

        // 承重点即活性上限本身。上一版这里断言的是「模块数算出来的派生值」,
        // 而那个派生每次都被 clamp 压回上限 —— 断言恒真,「派生」二字不承重。
        Assert.Equal(
            TestBudgets.LeanCacheProvisionBudget,
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
            // 下界..上界之外的值须被 clamp;取一个远超上界的数,三者都应落到上界。
            Environment.SetEnvironmentVariable(BudgetVariable, "99999");
            var clamped = TestBudgets.LeanCacheProvisionCeiling;
            Assert.Equal(clamped, LeanCacheProvisioner.LeanCommandBudget);
            Assert.Equal(clamped, LeanCacheProvisioner.DirectoryCopyBudget);
            Assert.Equal(clamped, LeanCacheProvisioner.DependencyFetchBudget);
        }
        finally
        {
            Environment.SetEnvironmentVariable(BudgetVariable, previous);
        }
    }

    /// <summary>
    /// 该值是 `policy-override`,其**取值依据**是覆盖全量冷建并留并发余量。
    ///
    /// 上一版把它判为「域外活性上限」,依据是「对正常路径 766s 有 9.4 倍」——
    /// **那个 766s 是 CI 热态报告生产的耗时,而本值界的是本地 worktree 的 Lake 命令**,
    /// 拿一个环境的读数当了另一个环境的判据。本地三级回退(clonefile → archive →
    /// ReproduceExisting)全落空即全量冷建 **3388s**,比值只有 2.13。
    ///
    /// 故本测试钉的是**本地口径**的那个关系,不再是 CI 口径。
    /// </summary>
    [Fact]
    public void BudgetClearsTheLocalFullColdBuildWithConcurrencyHeadroom()
    {
        // 本地全量冷建实测(2026-08-23,28 核,含并发,EXIT=0,1571 模块)。
        const int LocalFullColdBuildSeconds = 3388;

        // #4120 修订时(2026-08-30)的规模投影:dev `9b629c376` 2672 模块 × 2.156588 s/模块
        // (= 3388/1571,本机上界侧锚点)= 5763s;CI 侧下界(run 33286112262,72 分钟未建完)
        // ≥ 4320s 与之同量级。首次收口的判据(清过冷建读数的两倍)须对**当前**规模成立,
        // 否则复审线被跨过后只改复审线、不改预算,就是「改数让测试绿」。
        const int ProjectedFullColdBuildSecondsAtRevision = 5763;

        // 负读数①:旧值 1800 对 1656 的 8% 余量被并发吃掉而失败。故须显著多于 1 倍。
        Assert.True(
            LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
                > LocalFullColdBuildSeconds * 2,
            "预算未清过本地全量冷建的两倍,并发余量不足以避免重演 1800 的失败");
        Assert.True(
            LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
                > ProjectedFullColdBuildSecondsAtRevision * 2,
            "预算未清过 #4120 修订时规模投影冷建的两倍:复审线到期后预算本身未重新收口");

        // 有限:预算必须封顶,否则挂死检测失效。
        Assert.True(
            LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds
                < LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
    }

    /// <summary>
    /// `policy-override` 须**报全**:这不是派生值、日期、域、正反读数、永久案号、
    /// owner、退出条件、非永久。报不全即规矩所指的「无源未报」(第四形)。
    ///
    /// 本测试读该常数的声明文本并逐项核对 —— 缺任一项即红,迫使改动者补齐而非静默删注。
    /// </summary>
    [Fact]
    public void PolicyOverrideDeclarationReportsEveryRequiredItem()
    {
        var file = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "StrataLint.Cli", "Runtime", "LeanCacheBudgetPolicy.cs"));

        // 只看该常数自己的 <summary> 块(#4122 tests 席:全文件 token 检查会被别处出现的同一
        // 字符串满足,例如复审线常数的注释里也写着案号与日期)。
        var constantIndex = file.IndexOf("internal const int DefaultProvisionBudgetSeconds", StringComparison.Ordinal);
        Assert.True(constantIndex > 0, "DefaultProvisionBudgetSeconds declaration not found");
        var head = file[..constantIndex];
        var summaryStart = head.LastIndexOf("/// <summary>", StringComparison.Ordinal);
        Assert.True(summaryStart >= 0, "DefaultProvisionBudgetSeconds has no <summary> block");
        var declaration = head[summaryStart..];

        foreach (var required in new[]
        {
            "policy-override",       // 明报型别
            "这不是派生值",           // 明报非派生
            "2026-08-25",            // 日期
            "**域**",                 // 域
            "**正读数**",             // 正读数
            "**负读数**",             // 负读数
            "issues/2535",           // 永久案号(首次收口)
            "2026-08-30",            // 修订日期(#4120)
            "issues/4120",           // 修订案号
            "**owner**",              // owner
            "退出条件",               // 退出条件 / 复审触发
            "**非永久**",             // 非永久
        })
        {
            Assert.True(
                declaration.Contains(required, StringComparison.Ordinal),
                $"policy-override 声明缺项:{required}");
        }
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
    /// 旋钮的解析与 clamp:低于下界落到下界,高于上界落到上界(上界 = 声明的 policy-override 值,
    /// 无派生 —— 派生式已于 #3119 删除)。
    /// </summary>
    [Theory]
    [InlineData("1", 300)]
    [InlineData("30000", 21600)]
    public void ConfiguredBudgetUsesInvariantParsingAndClamps(string raw, int expectedSeconds)
    {
        AssertCacheGetBudget(raw, expectedSeconds);
    }

    /// <summary>
    /// 非法旋钮取值应回落到默认路径,而默认路径就是上限本身。
    /// 上一版此处期望「该树的派生值」,现无派生可言。
    /// </summary>
    [Fact]
    public void UnparseableBudgetFallsBackToTheCeiling()
    {
        WithBudget("invalid", () =>
            Assert.Equal(
                TestBudgets.LeanCacheProvisionBudget,
                LeanCacheProvisioner.LeanCommandBudget));
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
                TestBudgets.LeanCacheRetryOne,
                TestBudgets.LeanCacheRetryTwo,
                TestBudgets.LeanCacheRetryThree,
                TestBudgets.LeanCacheRetryFour,
            ],
            waits);
        Assert.Equal(4, waits.Count);
        for (var index = 1; index < waits.Count; index++)
        {
            Assert.Equal(waits[index - 1] + waits[index - 1], waits[index]);
        }
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
