using System.Text.Json.Nodes;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Theory]
    [InlineData("clone")]
    [InlineData("unreadable")]
    [InlineData("cleanup")]
    [InlineData("source-busy-after-clone")]
    [InlineData("source-pins-after-clone")]
    [InlineData("source-stamp-after-clone")]
    [InlineData("target-stamp-after-clone")]
    [InlineData("staging-symlink")]
    [InlineData("target-symlink")]
    public void FailedDependencyRestoreNeverPublishesSuccessOrDeletesExistingArtifacts(string failure)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor", projectWarm: true);
        var target = AddWorktree(repository.Path, "failed-dependencies");
        WriteCache(target, "retained compiler", mathlibComplete: false, projectWarm: true);
        var lake = Path.Combine(target, ".lake");
        var before = Directory.GetFiles(lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        var cloned = false;
        var runner = new RecordingWorktreeProcessRunner
        {
            BusyRoot = failure == "source-busy-after-clone" ? repository.Path : null,
            BusyWhen = () => cloned,
        };
        var cloner = new RecordingDirectoryCloner
        {
            Results = failure == "clone" ? new([new(false, false, 18, 1, "cross-device")]) : [],
            ExceptionToThrow = failure == "unreadable" ? new UnauthorizedAccessException("unreadable source") : null,
            AfterClone = (_, staged) =>
            {
                cloned = true;
                if (failure == "source-pins-after-clone")
                    File.AppendAllText(Path.Combine(repository.Path, "lean-toolchain"), "changed");
                if (failure == "source-stamp-after-clone")
                    File.Delete(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake")));
                if (failure == "target-stamp-after-clone")
                    File.Delete(LeanCacheStamp.PathFor(lake));
                if (failure == "staging-symlink")
                    File.CreateSymbolicLink(Path.Combine(staged, "mathlib/link"), Path.Combine(lake, "build/cache.bin"));
                if (failure == "target-symlink")
                    Directory.CreateSymbolicLink(Path.Combine(lake, "packages"), Path.Combine(repository.Path, ".lake/packages"));
            },
        };
        var cleanupCalls = 0;
        void Cleanup(string path)
        {
            if (failure == "cleanup" && ++cleanupCalls == 1) throw new IOException("injected staging cleanup failure");
            LeanCacheProvisioner.RemovePartial(path);
        }

        var result = LeanCacheEnsureCommand.Run(repository.Path,
            ["--path", target, "--restore-dependencies"], runner, cloner, Cleanup);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        foreach (var (path, bytes) in before)
        {
            if (failure == "target-stamp-after-clone" && path == LeanCacheStamp.PathFor(lake)) continue;
            Assert.Equal(bytes, File.ReadAllBytes(path));
        }
        Assert.Empty(Directory.GetDirectories(lake, "packages.stage-*"));
        Assert.DoesNotContain(runner.Invocations, call => Path.GetFileName(call.FileName) is "lake" or "lean");
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("failed", receipt.RootElement.GetProperty("status").GetString());
        if (failure == "clone")
            Assert.Equal(18, receipt.RootElement.GetProperty("clonefile_errno").GetInt32());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DependencyCloneRetryAndMissingStampFailureKeepAccurateReceipts(bool missingStamp)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor", projectWarm: true);
        var target = AddWorktree(repository.Path, "dependency-retry");
        var lake = Path.Combine(target, ".lake");
        Directory.CreateDirectory(lake);
        WriteRestoreFixture(lake, "owned", "retained");
        if (!missingStamp) LeanCacheStamp.Write(lake, ReadPins(target));
        var cloner = new RecordingDirectoryCloner
        {
            Results = missingStamp
                ? new([new(true, false, null, 1, null), new(false, false, 18, 1, "dependency staging failed")])
                : new([new(false, true, 5, 1, "retryable EIO")]),
            AfterClone = (_, staged) => Directory.CreateDirectory(staged),
        };

        var result = WorktreeCommand.Run(repository.Path, missingStamp
            ? ["ensure-cache", "--path", target]
            : ["ensure-cache", "--path", target, "--restore-dependencies"],
            new RecordingWorktreeProcessRunner(), cloner);

        Assert.Equal(!missingStamp, result.Success);
        Assert.Equal("retained", File.ReadAllText(Path.Combine(lake, "owned")));
        Assert.Empty(Directory.GetDirectories(lake, "*.stage-*"));
        using var receipt = ParseReceipt(result.Success ? result.Output : result.Error);
        Assert.Equal(2, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
        Assert.Equal(missingStamp ? 18 : 5, receipt.RootElement.GetProperty("clonefile_errno").GetInt32());
        if (missingStamp)
        {
            Assert.DoesNotContain("remove", receipt.RootElement.GetProperty("reason").GetString());
            Assert.Contains("existing target artifacts were retained", receipt.RootElement.GetProperty("reason").GetString());
            Assert.False(File.Exists(LeanCacheStamp.PathFor(lake)));
            Assert.False(Directory.Exists(Path.Combine(lake, "build")));
        }
    }

    [Fact]
    public void RestoreIncludesAllManifestPackagesAndRefusesUnstampedOrMainTargets()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor", projectWarm: true);
        var target = AddWorktree(repository.Path, "extra-package");
        var lake = Path.Combine(target, ".lake");
        Directory.CreateDirectory(lake);
        LeanCacheStamp.Write(lake, ReadPins(target));
        var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(repository.Path, "lake-manifest.json")))!;
        manifest["packages"]!.AsArray().Add(new JsonObject
        {
                ["type"] = "git", ["name"] = "extra", ["rev"] = new string('b', 40),
                ["url"] = "https://example.test/extra", ["inputRev"] = "main",
                ["subDir"] = null,
                ["configFile"] = "lakefile.toml", ["manifestFile"] = "lake-manifest.json",
                ["inherited"] = true
            });
        foreach (var root in new[] { repository.Path, target })
        {
            File.WriteAllText(Path.Combine(root, "lake-manifest.json"), manifest.ToJsonString());
            StrataLint.TestSupport.RegPackageFixture.Write(root);
        }
        WriteRestoreFixture(Path.Combine(repository.Path, ".lake/packages/extra"),
            ".lake/build/lib/lean/Extra.olean", "extra artifact");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var restored = WorktreeCommand.Run(repository.Path,
            ["ensure-cache", "--path", target, "--restore-dependencies"], runner, cloner);
        Assert.True(restored.Success, restored.Error);
        Assert.Equal("extra artifact", File.ReadAllText(Path.Combine(lake,
            "packages/extra/.lake/build/lib/lean/Extra.olean")));
        Assert.Single(cloner.Invocations);
        File.Delete(LeanCacheStamp.PathFor(lake));
        foreach (var root in new[] { target, repository.Path })
        {
            var refused = WorktreeCommand.Run(repository.Path,
                ["ensure-cache", "--path", root, "--restore-dependencies"], runner, cloner);
            Assert.False(refused.Success);
        }
        Assert.Single(cloner.Invocations);
    }
}
