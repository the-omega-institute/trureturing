using StrataLint.Cli;

namespace StrataLint.Tests;

/// <summary>
/// 建树时报告货源树的状态,**只读、不修、不挡**。
///
/// 这是 `LeanDonorRefresh` 的对偶:那个设计发现货源陈旧就自己去 pull + build 别人的树,
/// 失败还被吞成一个不进收据的字符串;这里只把读数摆出来,连同一条人可以直接粘贴执行的
/// 命令,由人决定要不要去暖它。同样的信息需求,一个越界一个不越界。
///
/// 判据刻意选最便宜的两个:落后多少提交(`git rev-list --count`),以及货源的 `.lake`
/// 是否为本次 base 的 pin 而建(stamp)。**不验 mathlib 完整性**——那要遍历 8000+ 文件,
/// 会把三秒的建树拖慢,而 stamp 匹配本来也不证明完整。故字段名是 `donor_cache_pin`
/// 而非 `warm`,不冒领它没证明的东西。
/// </summary>
public sealed partial class WorktreeCommandTests
{
    [Fact]
    public void ReceiptReportsHowFarTheDonorTrailsTheBase()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        AdvanceDev(repository.Path, 2);
        DetachDonorTo(repository.Path, "dev~2");
        var target = Path.Combine(repository.Path, "trailing-lane");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--kind", "math", "--name", "trailing", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        Assert.True(result.Success, result.Error);
        using var receipt = ParseInitReceipt(result.Output);
        Assert.Equal(2, receipt.RootElement.GetProperty("donor_behind_base").GetInt32());
    }

    [Fact]
    public void AStaleDonorCacheWarnsWithoutFailingTheInitialization()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var lake = Path.Combine(repository.Path, ".lake");
        Directory.CreateDirectory(lake);
        // 为**别的** pin 建的缓存:身份不匹配本次 base。
        LeanCacheStamp.Write(
            lake,
            LeanPinSet.Create(
                System.Text.Encoding.UTF8.GetBytes("leanprover/lean4:v9.99.0\n"),
                System.Text.Encoding.UTF8.GetBytes("{\"version\":\"0.0.0\"}\n")));
        var target = Path.Combine(repository.Path, "stale-donor-lane");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--kind", "math", "--name", "stale-donor", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        // 建树照常成功:warning 是 advisory,不是门。
        Assert.True(result.Success, result.Error);
        using var receipt = ParseInitReceipt(result.Output);
        Assert.Equal("mismatch", receipt.RootElement.GetProperty("donor_cache_pin").GetString());
        Assert.Contains("WARNING", result.Error, StringComparison.Ordinal);
        // 给的是可执行的命令,不是一句结论。
        Assert.Contains("make lean", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void AnAbsentDonorCacheIsReportedRatherThanTreatedAsAFailure()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "no-donor-cache-lane");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--kind", "math", "--name", "no-donor-cache", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        Assert.True(result.Success, result.Error);
        using var receipt = ParseInitReceipt(result.Output);
        Assert.Equal("absent", receipt.RootElement.GetProperty("donor_cache_pin").GetString());
        Assert.Contains("WARNING", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ACurrentAndMatchingDonorEmitsNoWarningAtAll()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "warm-donor-lane");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--kind", "math", "--name", "warm-donor", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        Assert.True(result.Success, result.Error);
        using var receipt = ParseInitReceipt(result.Output);
        Assert.Equal(0, receipt.RootElement.GetProperty("donor_behind_base").GetInt32());
        Assert.Equal("match", receipt.RootElement.GetProperty("donor_cache_pin").GetString());
        // 没有可报的就一个字都不说 —— 否则 warning 会退化成背景噪音。
        Assert.Equal(string.Empty, result.Error);
    }

    [Fact]
    public void ProbingTheDonorIntroducesNoWriteAndNoLeanProcess()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        AdvanceDev(repository.Path, 1);
        DetachDonorTo(repository.Path, "dev~1");
        var target = Path.Combine(repository.Path, "read-only-probe-lane");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["--kind", "math", "--name", "read-only-probe", "--path", target, "--base", "dev", "--skip-restore"],
            runner);

        Assert.True(result.Success, result.Error);
        // 探测不得引入 lake,也不得引入把货源往前推的 git 写动词。
        // (建树自身对 .git 的写——`worktree add`——不在此列,那是本命令的本职。)
        var forbidden = runner.Invocations
            .Where(static call =>
                Path.GetFileName(call.FileName) == "lake"
                || (call.FileName == "git"
                    && call.Arguments.Count > 0
                    && (call.Arguments[0] == "pull"
                        || call.Arguments[0] == "merge"
                        || call.Arguments[0] == "reset"
                        || call.Arguments[0] == "checkout")))
            .Select(static call => $"{call.FileName} {string.Join(' ', call.Arguments)}")
            .ToArray();
        Assert.Empty(forbidden);
    }

    /// <summary>
    /// `worktree_init` 收据是裸 JSON;同类里那个 `ParseReceipt` 剥的是 `LEAN_CACHE ` 前缀,
    /// 用错会把 11 个字符连同 `{` 一起吃掉,报成一句与本测试无关的 JSON 语法错。
    /// </summary>
    private static System.Text.Json.JsonDocument ParseInitReceipt(string output) =>
        System.Text.Json.JsonDocument.Parse(output);

    private static void AdvanceDev(string root, int commits)
    {
        for (var index = 0; index < commits; index++)
        {
            File.AppendAllText(Path.Combine(root, "README.md"), $"advance {index}\n");
            ReviewRegressionTests.RunGit(root, "add", "README.md");
            ReviewRegressionTests.RunGit(root, "commit", "-m", $"advance {index}");
        }
    }

    private static void DetachDonorTo(string root, string revision) =>
        ReviewRegressionTests.RunGit(root, "checkout", "--detach", revision);
}
