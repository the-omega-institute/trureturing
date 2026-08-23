using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

/// <summary>
/// 归档接入 ensure 的自动链(#2729 判决 B 步后半,入口二)。
///
/// stamp 只表示**依赖层**身份。stamp Match 而内容层为冷,正是 CI 上「dependency cache
/// 命中、project build cache 未命中」的形态 —— 不在此处取内容层,后面的 producer 就会
/// 从源码重编。
///
/// 三席给的机器门是一条蕴含式,这里逐向钉住:
///   archive_status != not_attempted  ⟹  内容层初始为冷 ∧ build 根未被占用
/// 反向即:内容层不冷、或 build 根已被占用时,**一次都不该调**归档。
/// </summary>
public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void ColdProjectWithAMatchingStampFetchesTheArchiveAndRecordsItsProducer()
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "cold-with-match");
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"prefix\","
                + "\"producer_commit_sha\":\"89abcdef0123456789abcdef0123456789abcdef\","
                + "\"workflow_run_id\":\"7777\"}\n",
        };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("unpacked", receipt.GetProperty("archive_status").GetString());
        Assert.Equal("prefix", receipt.GetProperty("archive_mode").GetString());
        Assert.Equal(
            "89abcdef0123456789abcdef0123456789abcdef",
            receipt.GetProperty("archive_producer_commit_sha").GetString());
        Assert.Equal("7777", receipt.GetProperty("archive_workflow_run_id").GetString());
    }

    /// <summary>
    /// 机器门的反向。内容层已经是热的就没有取的理由 —— 而「没有理由却仍然取」在 CI 上
    /// 意味着每次 project cache 命中都再付一次网络往返(三席的 ④ 重复付费)。
    /// </summary>
    [Fact]
    public void WarmProjectDoesNotReachForTheArchive()
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "warm-project");
        fixture.WriteProjectOlean();
        var runner = new RecordingWorktreeProcessRunner { ArchiveReceipt = "unused" };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.Equal("not_attempted", receipt.GetProperty("archive_status").GetString());
        Assert.Equal(
            "project olean state is warm",
            receipt.GetProperty("archive_skip_reason").GetString());
    }

    /// <summary>
    /// 取不到不是错,是慢。归档 miss / rejected / 取回失败都必须**降级为原样返回**,
    /// 并把原因落进收据 —— 静默降级正是本战线一路删掉的设计。
    /// </summary>
    [Theory]
    [InlineData("LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"no release\"}\n", "miss", "no release")]
    [InlineData(
        "LEAN_CACHE_FETCH {\"status\":\"rejected\",\"stage\":\"provenance\",\"reason\":\"release author is nobody\"}\n",
        "rejected",
        "provenance: release author is nobody")]
    public void AnUnusableArchiveDegradesAndSaysWhy(string stub, string status, string reason)
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, $"degrade-{status}");
        // 脚本的约定是 miss/rejected 走非零退出;桩必须照这个约定回,否则测的就不是
        // 真实形状。ensure 侧现在校验判词与退出码自洽,桩若回 0 会被判 failed。
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = stub,
            ArchiveExitCode = 1,
        };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("present", receipt.GetProperty("status").GetString());
        Assert.Equal(status, receipt.GetProperty("archive_status").GetString());
        Assert.Equal(reason, receipt.GetProperty("archive_reason").GetString());
    }

    /// <summary>
    /// 入口一:没有本机 donor 时(新机器、第一棵树、CI 冷启动),`.lake` 整个不存在。
    /// `lake exe cache get` 只补依赖层,内容层仍空 —— 归档是它唯一的私有供给。
    ///
    /// 顺序不能反:归档只供内容层,得先有 `.lake` 才有地方展开,故它接在 provision
    /// **之后**。
    /// </summary>
    [Fact]
    public void AbsentLakeWithNoDonorFetchesTheArchiveAfterTheDependencyLayer()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "absent-lake-no-donor");
        WriteFetcher(target);
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"exact\"}\n",
            AfterArchiveFetch = _ =>
            {
                // 顺序是本单的承重论证:归档只供内容层,得先有 `.lake` 才有地方展开。
                // 不在这里断言,顺序反了这条用例照样绿 —— 回调自己会把目录造出来。
                Assert.True(
                    File.Exists(Path.Combine(target, ".lake", "cache-get.marker")),
                    "the dependency layer must be in place before the archive is fetched");
                var olean = Path.Combine(
                    target, ".lake", "build", "lib", "lean", "FromArchive.olean");
                Directory.CreateDirectory(Path.GetDirectoryName(olean)!);
                File.WriteAllText(olean, "content layer\n");
            },
        };

        var receipt = ReadReceipt(WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner()));

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("unpacked", receipt.GetProperty("archive_status").GetString());
        Assert.Equal("warm", receipt.GetProperty("project_olean_state").GetString());
    }

    /// <summary>
    /// `ProbeFailed` 不是 `Cold`。探不到内容层状态时不取归档 —— 拿不准的时候不动树。
    ///
    /// 这条是评审席点的:三态里只有 `Cold` 该触发取回,而 `switch` 写漏一个分支就会把
    /// `ProbeFailed` 归到 `Cold` 那边,且不会有任何绿灯发现。
    /// </summary>
    [Fact]
    public void AFailedProbeIsNotTreatedAsCold()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor without project oleans\n");
        LeanCacheStamp.Write(Path.Combine(repository.Path, ".lake"), ReadPins(repository.Path));
        // 坏根造在 **donor** 上:目标的 `.lake` 必须不存在才走入口一,clone 会把这个形状
        // 原样搬过来,于是 provision 之后探针在目标上报 ProbeFailed。
        // 必须恰好是 `ProjectOleanRoot`(`.lake/build/lib/lean`)本身是文件。造在它的
        // **父目录**上不行:那样探的路径其父是文件,`InspectPath` 抛
        // `DirectoryNotFoundException` → 判 Absent → 归到 **Cold**,归档照取。
        // 实测过这个差一层的错。
        var donorProjectRoot = Path.Combine(repository.Path, ".lake", "build", "lib", "lean");
        Directory.CreateDirectory(Path.GetDirectoryName(donorProjectRoot)!);
        File.WriteAllText(donorProjectRoot, "not a directory\n");
        var target = AddWorktree(repository.Path, "probe-failed-target");
        WriteFetcher(target);
        var runner = new RecordingWorktreeProcessRunner { ArchiveReceipt = "unused" };

        var receipt = ReadReceipt(WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner()));

        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.Equal("not_attempted", receipt.GetProperty("archive_status").GetString());
    }

    /// <summary>
    /// 整树 clone 来的 donor **内容层可能是冷的**:那条路走的 `SelectDonor` 传的是
    /// `requireProjectWarm: false`,只有 missing-build 那条传 `true`。
    ///
    /// 此前我按 `Strategy == "cloned"` 断定「两层都有」并跳过归档,该补的场景不补。
    /// 判据现在挂在**实际热度**上,不挂在策略上 —— 策略是过程,热度是结果。
    /// </summary>
    [Fact]
    public void ACloneFromAColdDonorStillFetchesTheContentLayer()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        // donor 有 .lake 与依赖层,但**没有** project olean —— 内容层为冷。
        WriteCache(repository.Path, "donor without project oleans\n");
        LeanCacheStamp.Write(Path.Combine(repository.Path, ".lake"), ReadPins(repository.Path));
        var target = AddWorktree(repository.Path, "cold-donor-clone");
        WriteFetcher(target);
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"no release\"}\n",
            ArchiveExitCode = 1,
        };

        var receipt = ReadReceipt(WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner()));

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("miss", receipt.GetProperty("archive_status").GetString());

        // 依赖层是 clone 搬来的,归档 overlay 不得动它。Lake 的 unpack 是就地 overlay、
        // 不先删 build 根,这条断言把那个前提钉住 —— 若哪天换成「先清空再解包」,
        // 这里会红。
        Assert.Equal(
            "donor without project oleans\n",
            File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
    }

    /// <summary>
    /// 本机 donor 命中时整树都搬过来了,内容层不缺 —— 此时再取一次归档是纯粹的浪费,
    /// 而且会在一条已经成功的路径上引入一次可能失败的网络往返。
    /// </summary>
    [Fact]
    public void ALocalDonorMakesTheArchiveUnnecessary()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        LeanCacheStamp.Write(Path.Combine(repository.Path, ".lake"), ReadPins(repository.Path));
        var target = AddWorktree(repository.Path, "donor-supplies-both");
        WriteFetcher(target);
        var runner = new RecordingWorktreeProcessRunner { ArchiveReceipt = "unused" };

        var receipt = ReadReceipt(WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner()));

        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.Equal("not_attempted", receipt.GetProperty("archive_status").GetString());
        Assert.Equal(
            "project olean state is warm",
            receipt.GetProperty("archive_skip_reason").GetString());
    }

    private static void WriteFetcher(string root)
    {
        var script = LeanArchiveFetch.ScriptPath(root);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, "#!/usr/bin/env bash\nexit 0\n");
    }

    private static JsonElement ReadReceipt(CommandResult result)
    {
        Assert.True(result.Success, result.Error);
        const string prefix = "LEAN_CACHE ";
        var line = result.Output
            .Split('\n')
            .Last(candidate => candidate.StartsWith(prefix, StringComparison.Ordinal));
        return JsonDocument.Parse(line[prefix.Length..]).RootElement.Clone();
    }

    /// <summary>
    /// 机器门的**另一半**。蕴含式是「取归档 ⟹ 内容层冷 ∧ build 根未占用」,上面那条只
    /// 钉了「冷」这一半;若不钉「未占用」,删掉 content-root guard 一样不会红。
    ///
    /// build 根被占用时不能就地展开 —— 那是别人的目录,#2844 之前这条路上出过一次
    /// 「为腾位置而删目标内容」的设计,已被删掉,这里不许它从另一个入口回来。
    /// </summary>
    [Fact]
    public void OccupiedBuildRootIsNotUnpackedOver()
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "occupied-build-root");
        fixture.OccupyBuildRoot();
        var runner = new RecordingWorktreeProcessRunner { ArchiveReceipt = "unused" };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.Equal("not_attempted", receipt.GetProperty("archive_status").GetString());
        Assert.Equal(
            "content root already exists",
            receipt.GetProperty("archive_skip_reason").GetString());
    }

    /// <summary>
    /// 取回成功之后必须**重探热度**,否则收据里的 project_olean_state 还是取回之前那个
    /// 冷读数 —— 下游据它判「要不要冷编译」,一个陈旧的冷读数会让归档白取。
    /// 桩在这里真的落下 olean,删掉重探那两行就会红。
    /// </summary>
    [Fact]
    public void SuccessfulFetchIsFollowedByAFreshWarmthProbe()
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "reprobe-after-fetch");
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"exact\"}\n",
            AfterArchiveFetch = _ => fixture.WriteProjectOlean(),
        };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("unpacked", receipt.GetProperty("archive_status").GetString());
        Assert.Equal("warm", receipt.GetProperty("project_olean_state").GetString());
    }

    /// <summary>
    /// 预算不是拍出来的,是 workflow 那个值的投影。二者一旦分叉,归档预算就可能大于它
    /// 所在的 job —— 那正是评审席抓到的缺陷:一次挂住的取回能吃光整个 job,把「取不到
    /// 就降级」变成「job 超时取消」。
    /// </summary>
    [Fact]
    public void LeanInspectJobBudgetMatchesTheWorkflow()
    {
        var workflow = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));
        var lines = workflow.Split('\n');

        var job = Array.FindIndex(
            lines,
            static line => line.StartsWith("  lean-inspect:", StringComparison.Ordinal));
        Assert.True(job >= 0, "the lean-inspect job is gone");

        var timeout = Array.FindIndex(
            lines,
            job,
            static line => line.TrimStart().StartsWith("timeout-minutes:", StringComparison.Ordinal));
        Assert.True(timeout > job, "lean-inspect declares no timeout-minutes");

        Assert.Equal(
            LeanCacheBudgetPolicy.LeanInspectJobBudgetMinutes,
            int.Parse(lines[timeout].Split(':')[1].Trim()));
        Assert.True(
            LeanCacheBudgetPolicy.PostArchiveReserveMinutes
                < LeanCacheBudgetPolicy.LeanInspectJobBudgetMinutes,
            "the reserve must leave the archive some budget");
    }

    /// <summary>
    /// candidate 侧代码不得拿到 GitHub token。
    ///
    /// `ci.yml` 由 `pull_request_target` 触发:workflow 文本来自 base 侧,但 `candidate/`
    /// 里检出的是 **PR 作者可控的代码**,而 ensure 正是那份代码。它现在会去调 `gh`。
    /// 今天仓内 token 暴露为 **0 处**(本断言即钉住这一点),故不可利用 —— **但这个设计
    /// 会制造添加 token 的压力**:归档路径在 CI 上必然因缺 auth 而失败,下一个想让它
    /// 工作的人自然会加 `GH_TOKEN`,**那一刻才是漏洞**。
    ///
    /// 所以拦的不是今天的状态,是那个将来的动作。要让归档在 CI 上真正可用,正解是走
    /// **公开 HTTPS**(本仓 `visibility=public`,release 资产与 REST 元数据都无需认证),
    /// 或把下载与核验放进 **base-owned** 的步骤,而不是把 token 递给候选代码。
    /// </summary>
    [Fact]
    public void CandidateOwnedCodeIsNeverHandedAGitHubToken()
    {
        var workflow = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));

        foreach (var name in new[] { "GH_TOKEN", "GITHUB_TOKEN", "github.token" })
        {
            Assert.DoesNotContain(name, workflow, StringComparison.Ordinal);
        }
    }

    private sealed class EnsureArchiveFixture
    {
        private readonly string target;

        internal EnsureArchiveFixture(string repositoryRoot, string name)
        {
            Repository = repositoryRoot;
            InitializeRepository(Repository);
            target = AddWorktree(Repository, name);

            // stamp Match:依赖层身份对得上。内容层此时为空,即 CI 上 dependency cache
            // 命中而 project build cache 未命中的那一刻。
            var lake = Path.Combine(target, ".lake");
            Directory.CreateDirectory(lake);
            LeanCacheStamp.Write(lake, ReadPins(target));

            // 脚本必须存在,否则 helper 在调用前就判 Failed,测的就不是接入逻辑了。
            var script = LeanArchiveFetch.ScriptPath(target);
            Directory.CreateDirectory(Path.GetDirectoryName(script)!);
            File.WriteAllText(script, "#!/usr/bin/env bash\nexit 0\n");
        }

        private string Repository { get; }

        internal void OccupyBuildRoot()
        {
            var build = Path.Combine(target, ".lake", "build");
            Directory.CreateDirectory(build);
            File.WriteAllText(Path.Combine(build, "someone-elses.txt"), "occupied\n");
        }

        internal void WriteProjectOlean()
        {
            var olean = Path.Combine(
                target, ".lake", "build", "lib", "lean", "Warm.olean");
            Directory.CreateDirectory(Path.GetDirectoryName(olean)!);
            File.WriteAllText(olean, "warm\n");
        }

        internal JsonElement Ensure(RecordingWorktreeProcessRunner runner)
        {
            var result = WorktreeCommand.Run(
                Repository,
                ["ensure-cache", "--path", target],
                runner,
                new RecordingDirectoryCloner());
            Assert.True(result.Success, result.Error);

            const string prefix = "LEAN_CACHE ";
            var line = result.Output
                .Split('\n')
                .Last(candidate => candidate.StartsWith(prefix, StringComparison.Ordinal));
            return JsonDocument.Parse(line[prefix.Length..]).RootElement.Clone();
        }
    }
}
