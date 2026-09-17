using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

/// <summary>
/// stamp 匹配不代表项目产物已就绪。
/// 内容层为冷且 build 根未占用时才尝试归档;热内容层或已占用的根不得访问归档。
/// </summary>
public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void PrivateReleaseFallbackPreservesDefaultThroughBoundedEnsureOwner()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "private-release-default");
        LeanCacheStamp.Write(Path.Combine(target, ".lake"), ReadPins(target));
        var script = LeanArchiveFetch.ScriptPath(target);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, """
            #!/bin/sh
            printf '%s\n' "$@" > fetch-arguments
            for argument in "$@"; do
              if [ "$argument" = --allow-seed ]; then
                echo 'LEAN_CACHE_FETCH {"status":"unpacked","mode":"seed"}'
                exit 0
              fi
            done
            echo 'LEAN_CACHE_FETCH {"status":"miss","reason":"seed not allowed"}'
            exit 1
            """ + "\n");

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache", "--path", target]);

        Assert.True(result.Success, result.Error);
        var receipt = ReadReceipt(result);
        Assert.Equal("miss", receipt.GetProperty("archive_status").GetString());
        Assert.Equal("seed not allowed", receipt.GetProperty("archive_reason").GetString());
        Assert.Equal(["fetch", "--repository", target, "--writer-owned"],
            File.ReadAllLines(Path.Combine(target, "fetch-arguments")));
    }

    [Fact]
    public void ColdProjectWithAMatchingStampFetchesTheArchiveAndRecordsItsProducer()
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "cold-with-match");
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"partition\","
                + "\"producer_commit_sha\":\"89abcdef0123456789abcdef0123456789abcdef\","
                + "\"workflow_run_id\":\"7777\"}\n",
        };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("unpacked", receipt.GetProperty("archive_status").GetString());
        Assert.Equal("partition", receipt.GetProperty("archive_mode").GetString());
        Assert.Equal(
            "89abcdef0123456789abcdef0123456789abcdef",
            receipt.GetProperty("archive_producer_commit_sha").GetString());
        Assert.Equal("7777", receipt.GetProperty("archive_workflow_run_id").GetString());

        // Clonefile donor 的依赖层可用时,项目内容层仍可能为冷。
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

        }
    }

    /// <summary>
    /// 内容层已经为热时不访问归档。
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

        // 本地热 donor 已提供项目内容层,不再访问归档。
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
    /// 归档 miss、rejected 或取回失败时保留现有缓存,并在收据中记录原因。
    /// </summary>
    [Theory]
    [InlineData("LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"no release\"}\n", "miss", "no release")]
    [InlineData(
        "LEAN_CACHE_FETCH {\"status\":\"rejected\",\"stage\":\"provenance\",\"reason\":\"release author is nobody\"}\n",
        "rejected",
        "provenance: release author is nobody")]
    [InlineData(
        "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"exact\"}\n",
        "failed",
        "archive receipt says unpacked but the fetcher exited 1")]
    public void AnUnusableArchiveDegradesAndSaysWhy(string stub, string status, string reason)
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, $"degrade-{status}");
        string? callbackRoot = null;
        bool? concurrentWriterAcquired = null;
        // 脚本的约定是 miss/rejected 走非零退出;桩必须照这个约定回,否则测的就不是
        // 真实形状。ensure 侧现在校验判词与退出码自洽,桩若回 0 会被判 failed。
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = stub,
            ArchiveExitCode = 1,
            AfterArchiveFetch = root =>
            {
                callbackRoot = root;
                using var concurrent = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
                concurrentWriterAcquired = concurrent is not null;
            },
        };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(1, runner.ArchiveInvocations);
        var invocation = Assert.Single(runner.Invocations, static call => call.FileName == "/bin/bash");
        Assert.Equal(
            [Path.Combine(fixture.Target, "tools", "scripts", "worktree", "lean-cache-publish.sh"),
                "fetch", "--repository", fixture.Target, "--writer-owned"],
            invocation.Arguments);
        Assert.Equal(fixture.Target, invocation.WorkingDirectory);
        Assert.Equal(fixture.Target, callbackRoot);
        Assert.False(concurrentWriterAcquired);
        using var releasedWriter = LeanCacheWriterGuard.TryAcquire(Path.Combine(fixture.Target, ".lake"));
        Assert.NotNull(releasedWriter);
        Assert.Equal("present", receipt.GetProperty("status").GetString());
        Assert.Equal(status, receipt.GetProperty("archive_status").GetString());
        Assert.Equal(reason, receipt.GetProperty("archive_reason").GetString());
    }





    [Theory]
    [InlineData(0, "not_attempted")]
    [InlineData(9, "failed")]
    public void ActionsSeedSkipReceiptPreservesItsReasonAndExitConsistency(int fetchExit, string expected)
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "actions-seed");
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"skipped\",\"reason\":\"Actions supplied an applicable seed\"}\n",
            ArchiveExitCode = fetchExit,
        };

        var receipt = fixture.Ensure(runner);

        Assert.Equal("present", receipt.GetProperty("status").GetString());
        Assert.Equal(expected, receipt.GetProperty("archive_status").GetString());
        if (fetchExit == 0)
            Assert.Equal("Actions supplied an applicable seed", receipt.GetProperty("archive_skip_reason").GetString());
        else
            Assert.Contains("exited 9", receipt.GetProperty("archive_reason").GetString()!, StringComparison.Ordinal);
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
    /// 归档不得覆盖已有的 build 根。
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

        // ProbeFailed 不等于 Cold,无法探测时不得访问归档。
        aFailedProbeIsNotTreatedAsCold();

        static void aFailedProbeIsNotTreatedAsCold()
        {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor without project oleans\n");
        LeanCacheStamp.Write(Path.Combine(repository.Path, ".lake"), ReadPins(repository.Path));
        // 将 donor 的 .lake/build/lib/lean 本身设为文件,使 clone 后的目标探测失败。
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
    /// 归档成功后重新探测项目产物,使收据反映安装后的状态。
    /// </summary>
    [Fact]
    public void SuccessfulFetchIsFollowedByAFreshWarmthProbe()
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "reprobe-after-fetch");
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"partition\"}\n",
            AfterArchiveFetch = _ => fixture.WriteProjectOlean(),
        };

        var receipt = fixture.Ensure(runner);

        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("unpacked", receipt.GetProperty("archive_status").GetString());
        Assert.Equal("warm", receipt.GetProperty("project_olean_state").GetString());

        // 无本地 donor 时先补依赖层,再安装归档内容层。
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
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"partition\"}\n",
            AfterArchiveFetch = _ =>
            {
                // 回调写入项目产物前,依赖层必须已经就绪。
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

        internal string Target => target;

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
