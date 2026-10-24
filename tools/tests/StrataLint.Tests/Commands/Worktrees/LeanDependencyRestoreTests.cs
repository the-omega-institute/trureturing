using System.Text.Json.Nodes;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    public void DependencyRecoveryAddsMissingMaterialAndPreservesEveryExistingByte(bool stamped, bool emptyBuild)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor build\n", projectWarm: true);
        var target = AddWorktree(repository.Path, "dependency-restore");
        var lake = Path.Combine(target, ".lake");
        var donorPackage = Path.Combine(repository.Path, ".lake/packages/mathlib");
        var package = Path.Combine(lake, "packages/mathlib");
        WriteRestoreFixture(package, ".lake/build/lib/lean/Mathlib/Algebra/Basic.olean", "");
        WriteRestoreFixture(package, ".lake/build/lib/lean/Mathlib/Algebra/Basic.olean.hash", "retained hash");
        // File/directory conflicts remain authoritative too, rather than becoming replacements.
        WriteRestoreFixture(donorPackage, "conflict/child", "donor child");
        WriteRestoreFixture(package, "conflict", "retained conflicting file");
        WriteRestoreFixture(donorPackage, ".lake/build/lib/lean/Mathlib/Topology/Basic.trace", "native trace");
        foreach (var excluded in new[] { ".release", "staging", "reports", "stratalint", "old.stage-x" })
            WriteRestoreFixture(donorPackage, excluded + "/export", "excluded export");
        WriteRestoreFixture(lake, "target-owned", "retained owner");
        if (emptyBuild) Directory.CreateDirectory(Path.Combine(lake, "build"));
        if (stamped)
        {
            WriteSplitOwnership(target);
            _ = WriteFormerOwners(target);
            LeanCacheStamp.Write(lake, ReadPins(target));
            WriteRestoreFixture(lake, "build/lib/lean/InProgress.olean", "retained compiler bytes");
            WriteRestoreFixture(lake, "build/stratalint/raw-lean-report.json", "retained report bytes");
        }
        var before = Directory.GetFiles(lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) =>
            {
                using var targetWriter = LeanCacheWriterGuard.TryAcquire(lake);
                using var sourceWriter = LeanCacheWriterGuard.TryAcquire(Path.Combine(repository.Path, ".lake"));
                Assert.Null(targetWriter);
                Assert.Null(sourceWriter);
            },
        };

        var result = WorktreeCommand.Run(repository.Path,
            stamped ? ["ensure-cache", "--path", target, "--restore-dependencies"]
                : ["ensure-cache", "--path", target], runner, cloner);

        Assert.True(result.Success, result.Error);
        foreach (var (path, bytes) in before) Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.True(File.Exists(Path.Combine(package, "Mathlib/Topology/Basic.lean")));
        Assert.Equal("native trace", File.ReadAllText(Path.Combine(package,
            ".lake/build/lib/lean/Mathlib/Topology/Basic.trace")));
        foreach (var excluded in new[] { ".release", "staging", "reports", "stratalint", "old.stage-x" })
            Assert.False(Directory.Exists(Path.Combine(package, excluded)));
        Assert.Empty(Directory.GetDirectories(lake, "*.stage-*"));
        Assert.DoesNotContain(runner.Invocations, call => Path.GetFileName(call.FileName) is "lake" or "lean");
        Assert.Equal(stamped ? 1 : 2, cloner.Invocations.Count);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(stamped ? "restored" : "seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Contains("native Lake must validate", receipt.RootElement.GetProperty("reason").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
    }

    [Theory]
    [InlineData(false, "toolchain")]
    [InlineData(true, "toolchain")]
    [InlineData(false, "dependency")]
    [InlineData(true, "dependency")]
    [InlineData(false, "platform")]
    [InlineData(true, "platform")]
    [InlineData(false, "missing-packages")]
    [InlineData(true, "missing-packages")]
    [InlineData(false, "busy-source")]
    [InlineData(true, "busy-source")]
    [InlineData(false, "busy-target")]
    [InlineData(true, "busy-target")]
    public void DependencyRecoveryRefusesUnavailableOrIncompatibleSourcesWithoutTouchingTarget(bool missingStamp, string failure)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor build", projectWarm: true);
        var target = AddWorktree(repository.Path, "dependency-refusal");
        WriteCache(target, "retained build", stamp: !missingStamp, mathlibComplete: false, projectWarm: true);
        var lake = Path.Combine(target, ".lake");
        var before = Directory.GetFiles(lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        if (failure == "toolchain")
            File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v0.0.0\n");
        if (failure == "dependency")
        {
            var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(repository.Path, "lake-manifest.json")))!;
            manifest["packages"]!.AsArray().Add(new JsonObject
            {
                ["type"] = "git", ["name"] = "extra", ["rev"] = new string('b', 40),
                ["url"] = "https://example.test/extra", ["inputRev"] = "main",
                ["subDir"] = null,
                ["configFile"] = "lakefile.toml", ["manifestFile"] = "lake-manifest.json",
                ["inherited"] = true
            });
            File.WriteAllText(Path.Combine(repository.Path, "lake-manifest.json"), manifest.ToJsonString());
            StrataLint.TestSupport.RegPackageFixture.Write(repository.Path);
        }
        if (failure == "platform")
        {
            var stampPath = LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"));
            var stamp = JsonNode.Parse(File.ReadAllText(stampPath))!;
            stamp["arch"] = "incompatible";
            File.WriteAllText(stampPath, stamp.ToJsonString());
        }
        if (failure == "missing-packages")
            Directory.Delete(Path.Combine(repository.Path, ".lake/packages"), recursive: true);
        using var busy = failure is "busy-source" or "busy-target"
            ? LeanCacheWriterGuard.TryAcquire(Path.Combine(failure == "busy-source" ? repository.Path : target, ".lake"))
            : null;
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(repository.Path,
            missingStamp ? ["ensure-cache", "--path", target]
                : ["ensure-cache", "--path", target, "--restore-dependencies"],
            new RecordingWorktreeProcessRunner(), cloner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal(missingStamp && failure == "missing-packages" ? 1 : 0, cloner.Invocations.Count);
        foreach (var (path, bytes) in before) Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.Empty(Directory.GetDirectories(lake, "*.stage-*"));
    }

    [Fact]
    public void MatchingStampedPartialDependenciesKeepNormalNoReseedBehavior()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor", projectWarm: true);
        var target = AddWorktree(repository.Path, "normal-partial");
        WriteCache(target, "retained", mathlibComplete: false, projectWarm: true);
        var cloner = new RecordingDirectoryCloner();
        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(), cloner);
        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.False(LeanCacheFixtureFile.MathlibProjectionExists(target));
    }

    private static void WriteRestoreFixture(string root, string relative, string bytes)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, bytes);
    }
}
