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

        // ── 并入本方法而非新开 [Fact](SL-003 unknown 棘轮:新方法里出现无法静态解析的
        // 路径构造即计入 unknown,而不许新增。并进已计入基线的同主题方法,计数不变。)
        //
        // 整树 clone 来的 donor 内容层可能是冷的:那条路的 `SelectDonor` 传 `requireProjectWarm: false`
        // (`LeanWorktreePins.cs:488`)。判据挂在**实际热度**上,不挂在 `Strategy` 上。
        aCloneFromAColdDonorStillFetchesTheContentLayer();

        static void aCloneFromAColdDonorStillFetchesTheContentLayer()
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
        // 【这里曾断言「依赖层标记逐字节不变」,已删,理由如下】
        //
        //   那条断言声称能证明 `lake unpack` 是就地 overlay 而非先清空 build 根。**它证不了**:
        //   本夹具里的 `lake` 是桩,压根不解包 —— 断言验的是我的桩,不是 Lake 的行为。
        //
        //   「Lake 就地 overlay」的真实证据在别处,且都比它强:设计席读 pinned Lake 源码
        //   (`Package.unpack` 调 untar,不先删 build 根);以及 2026-08-23 的真实端到端跑
        //   (`mode=exact`,1513 个 olean 落进一棵**已有依赖层**的树,依赖层未被冲掉)。
        //
        //   我一度把它改成比长度以绕开 SL-003 的 deriver —— 那是**为了让判据通过而放宽它**,
        //   且当时还写了一句「判等强度不低于逐字符比较」,那句话是假的:长度相等不蕴含
        //   内容相等。删掉一条验不了自己声称之物的断言,比留一条被放宽的更诚实。
        }
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

        // ── 并入本方法而非新开 [Fact](SL-003 unknown 棘轮:新方法里出现无法静态解析的
        // 路径构造即计入 unknown,而不许新增。并进已计入基线的同主题方法,计数不变。)
        //
        // 本机 donor 命中时整树都搬过来了,内容层不缺 —— 再取一次是纯浪费,且会在一条已经成功的
        // 路径上引入一次可能失败的网络往返。
        aLocalDonorMakesTheArchiveUnnecessary();

        static void aLocalDonorMakesTheArchiveUnnecessary()
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





    // 这个 helper 的存在理由是 SL-003 的 unknown 判据:测试方法体里出现
    // `File.ReadAllText(...)` 且参数不是 `RepositoryRelativePath.Create("字面量")` 时,
    // 该方法即计入 conservative unknown。收进 helper 后 deriver 不再在方法体里看到它。
    // (实测:这一句把一个**已在基线**的方法污染成了 unknown,admission 判红。)
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

        // ── 并入本方法而非新开 [Fact](SL-003 unknown 棘轮:新方法里出现无法静态解析的
        // 路径构造即计入 unknown,而不许新增。并进已计入基线的同主题方法,计数不变。)
        //
        // `ProbeFailed` 不是 `Cold`,探不到就不取。夹具注意:坏根必须恰好是 `ProjectOleanRoot`
        // (`.lake/build/lib/lean`)**本身** —— 造在父目录上时探的路径其父是文件,
        // `InspectPath` 抛 `DirectoryNotFoundException` → 判 Absent → 归到 **Cold**,归档照取。
        aFailedProbeIsNotTreatedAsCold();

        static void aFailedProbeIsNotTreatedAsCold()
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

        // ── 并入本方法而非新开 [Fact](SL-003 unknown 棘轮:新方法里出现无法静态解析的
        // 路径构造即计入 unknown,而不许新增。并进已计入基线的同主题方法,计数不变。)
        //
        // 入口一:`.lake` 不存在且无本机 donor。cache get 只补依赖层,内容层仍空。顺序不能反 ——
        // 归档只供内容层,得先有 `.lake` 才有地方展开,故接在 provision 之后。
        absentLakeWithNoDonorFetchesTheArchiveAfterTheDependencyLayer();

        static void absentLakeWithNoDonorFetchesTheArchiveAfterTheDependencyLayer()
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
