using System.Text;
using System.Text.Json;
using StrataLint.EngineeringScope;
using StrataLint.Runtime;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class LeanArtifactCacheRoutingTests
{
    [Theory]
    [InlineData(false, "1")]
    [InlineData(true, "")]
    public void ScopedWriterRoutesLakeArtifactCacheByCheckoutKind(bool linked, string expectedArtifactValue)
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = linked ? AddWorktree(repository.Path, "artifact-routing") : repository.Path;
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE");
        try
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE", "targeted");
            var result = LeanCacheEnsureCommand.RunWithWriter(
                repository.Path,
                linked ? ["--path", target, "--", "/usr/bin/env"] : ["--", "/usr/bin/env"],
                new ProductionWorktreeProcessRunner(),
                new RecordingDirectoryCloner());

            Assert.True(result.Success, result.Error);
            Assert.Contains($"LAKE_ARTIFACT_CACHE={expectedArtifactValue}\n", result.Output, StringComparison.Ordinal);
            Assert.Contains("LAKE_RESTORE_ARTIFACTS=1\n", result.Output, StringComparison.Ordinal);
            Assert.Contains("LAKE_NO_CACHE=1\n", result.Output, StringComparison.Ordinal);
            Assert.Contains("MATHLIB_NO_CACHE_ON_UPDATE=1\n", result.Output, StringComparison.Ordinal);
            using var receipt = JsonDocument.Parse(result.Output["LEAN_CACHE ".Length..].Split('\n')[0]);
            Assert.Equal("targeted", receipt.RootElement.GetProperty("scope").GetString());
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE", previous);
        }
    }

    [Theory]
    [InlineData("lake", "build", ":report", false)]
    [InlineData("lake", "build", "default", false)]
    [InlineData("lake", "build", "aggregate", false)]
    [InlineData("lake", "build", "D5.A", true)]
    public void ScopeMarkerCannotNarrowWholeLakeOperations(string executable, string verb, string target, bool expected)
    {
        var environment = new Dictionary<string, string?> {{ "STRATALINT_LEAN_CACHE_SCOPE", "targeted" }};
        Assert.Equal(expected, LeanCacheEnsureCommand.IsScopedCacheRequest(
            [executable, verb, target], name => environment.GetValueOrDefault(name)));
    }

    [Fact]
    public void ScopedWriterUsesOrdinaryEnsureWhenCurrentCacheIsHot()
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteHotCache(repository.Path);
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE");
        try
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE", "targeted");
            var result = LeanCacheEnsureCommand.RunWithWriter(
                repository.Path,
                ["--", "/usr/bin/env"],
                new ProductionWorktreeProcessRunner(),
                new RecordingDirectoryCloner());

            Assert.True(result.Success, result.Error);
            Assert.Contains("LAKE_ARTIFACT_CACHE=1\n", result.Output, StringComparison.Ordinal);
            Assert.Contains("LAKE_RESTORE_ARTIFACTS=1\n", result.Output, StringComparison.Ordinal);
            Assert.DoesNotContain("LAKE_NO_CACHE=1\n", result.Output, StringComparison.Ordinal);
            using var receipt = JsonDocument.Parse(result.Output["LEAN_CACHE ".Length..].Split('\n')[0]);
            Assert.Equal("present", receipt.RootElement.GetProperty("status").GetString());
            Assert.False(receipt.RootElement.TryGetProperty("scope", out _));
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE", previous);
        }
    }

    [Fact]
    public void StampedDependencyOnlyCacheDoesNotPromoteScopedRequestToEnsure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var lake = Path.Combine(repository.Path, ".lake");
        Directory.CreateDirectory(lake);
        LeanCacheStamp.Write(lake, ReadPins(repository.Path));
        MathlibProjectionFixture.Write(lake);
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE");
        try
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE", "targeted");
            var result = LeanCacheEnsureCommand.RunWithWriter(
                repository.Path,
                ["--", "/usr/bin/env"],
                new ProductionWorktreeProcessRunner(),
                new RecordingDirectoryCloner());

            Assert.True(result.Success, result.Error);
            using var receipt = JsonDocument.Parse(result.Output["LEAN_CACHE ".Length..].Split('\n')[0]);
            Assert.Equal("scoped", receipt.RootElement.GetProperty("status").GetString());
            Assert.Equal("targeted", receipt.RootElement.GetProperty("scope").GetString());
            Assert.Contains("LAKE_NO_CACHE=1\n", result.Output, StringComparison.Ordinal);
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_SCOPE", previous);
        }
    }

    private static string AddWorktree(string root, string name)
    {
        Git(root, "worktree", "add", "-b", $"harness/{name}", Path.Combine(root, name), "HEAD");
        return Path.Combine(root, name);
    }

    private static void InitializeRepository(string root)
    {
        Git(root, "init", "--initial-branch=dev");
        Git(root, "config", "user.email", "stratalint@example.invalid");
        Git(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# lean cache fixture\n");
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), LeanCacheFixtureFile.Manifest());
        StrataLint.TestSupport.RegPackageFixture.Write(root);
        Git(root, "add", "README.md", "lean-toolchain", "lake-manifest.json", "Reg", "tools/lean-inspector-reg");
        Git(root, "commit", "-m", "fixture baseline");
    }

    private static LeanPinSet ReadPins(string root) =>
        LeanPinSet.TryReadWorktree(root, out var reason)
            ?? throw new InvalidOperationException(reason);

    private static void WriteHotCache(string root)
    {
        var lake = Path.Combine(root, ".lake");
        Directory.CreateDirectory(lake);
        LeanCacheStamp.Write(lake, ReadPins(root));
        _ = ProjectOleanFixture.Write(root, "ExistingProject");
        MathlibProjectionFixture.Write(lake);
    }

    private static string Git(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run("git", arguments, root,
            BoundedProcessRunner.HangDetectionBudget, 64 * 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        return Encoding.UTF8.GetString(result.StandardOutput);
    }
}
