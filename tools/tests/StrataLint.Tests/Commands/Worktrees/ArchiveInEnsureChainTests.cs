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
            "project olean state is not cold",
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
        var runner = new RecordingWorktreeProcessRunner { ArchiveReceipt = stub };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("present", receipt.GetProperty("status").GetString());
        Assert.Equal(status, receipt.GetProperty("archive_status").GetString());
        Assert.Equal(reason, receipt.GetProperty("archive_reason").GetString());
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
