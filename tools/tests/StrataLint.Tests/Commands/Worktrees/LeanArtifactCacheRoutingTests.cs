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
                new ProductionWorktreeProcessRunner().WithEnvironment(new Dictionary<string, string>
                {
                    ["LAKE_ARTIFACT_CACHE"] = "1",
                }),
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
    [InlineData("lake", "build", "Trureturing", false)]
    [InlineData("lake", "build", ":moduleReports", false)]
    [InlineData("lake", "build", "Trureturing:static", false)]
    [InlineData("lake", "build", "trureturing/Trureturing:static", false)]
    [InlineData("lake", "build", "leanInspector/LeanInformationAudit", false)]
    [InlineData("lake", "build", "leanInspectorInterface/LeanInformationAuditInterface:static", false)]
    [InlineData("lake", "build", "D5.A:olean", true)]
    [InlineData("lake", "build", "D5.A", true)]
    public void ScopeMarkerCannotNarrowWholeLakeOperations(string executable, string verb, string target, bool expected)
    {
        var environment = new Dictionary<string, string?> {{ "STRATALINT_LEAN_CACHE_SCOPE", "targeted" }};
        Assert.Equal(expected, LeanCacheEnsureCommand.IsScopedCacheRequest(
            [executable, verb, target], name => environment.GetValueOrDefault(name)));
    }

    [Theory]
    [InlineData(null, false)]
    [InlineData("", false)]
    [InlineData("selected-scope.json", true)]
    public void ModuleReportFacetRequiresScopedMembership(string? path, bool expected)
    {
        Assert.Equal(expected, LeanCacheEnsureCommand.IsScopedCacheRequest(
            ["lake", "build", ":moduleReports"], name => name switch
            {
                "STRATALINT_LEAN_CACHE_SCOPE" => "scoped",
                "STRATALINT_INSPECTOR_SCOPE_FILE" => path,
                _ => null,
            }));
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void UnknownCheckoutIdentityCannotAdmitArtifactProducer(bool hot, bool corrupt)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        if (hot) WriteHotCache(repository.Path);
        var marker = Path.Combine(repository.Path, ".git");
        Directory.Move(marker, marker + "-saved");
        if (corrupt) File.WriteAllText(marker, "gitdir: missing-administration\n");
        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path,
            ["--", "/usr/bin/env"], new ProductionWorktreeProcessRunner(),
            new RecordingDirectoryCloner(), FileSystemLeanCacheStateProbe.Instance,
            name => name == "STRATALINT_LEAN_CACHE_SCOPE" ? "targeted" : null);

        Assert.False(result.Success);
        Assert.Contains("worktree identity unavailable", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("LAKE_ARTIFACT_CACHE=1", result.Output, StringComparison.Ordinal);
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

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EmptyScopedWorktreeEnsuresFromUsableLocalDonor(bool sibling)
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var donor = sibling ? AddWorktree(repository.Path, "hot-donor") : repository.Path;
        WriteHotCache(donor);
        var target = AddWorktree(repository.Path, "empty-selected");
        var cloner = new RecordingDirectoryCloner();
        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path,
            ["--path", target, "--", "/usr/bin/env"], new ProductionWorktreeProcessRunner(),
            cloner, FileSystemLeanCacheStateProbe.Instance,
            name => name == "STRATALINT_LEAN_CACHE_SCOPE" ? "targeted" : null);

        Assert.True(result.Success, result.Error);
        Assert.Equal(Path.Combine(LeanCacheGuard.PhysicalPath(donor), ".lake"),
            Assert.Single(cloner.Invocations).Source);
        using var receipt = JsonDocument.Parse(result.Output["LEAN_CACHE ".Length..].Split('\n')[0]);
        Assert.Equal("seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.False(receipt.RootElement.TryGetProperty("scope", out _));
        Assert.DoesNotContain("LAKE_NO_CACHE=1\n", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void RetiredRootOwnersDoNotCountAsUsableProjectHeat()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(Path.Combine(repository.Path, "lakefile.toml"), "name = \"trureturing\"\n");
        var lake = Path.Combine(repository.Path, ".lake");
        Directory.CreateDirectory(lake);
        LeanCacheStamp.Write(lake, ReadPins(repository.Path));
        MathlibProjectionFixture.Write(lake);
        var obsolete = ProjectOleanFixture.Write(repository.Path, "LeanInformationAudit/Obsolete");
        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path,
            ["--", "/usr/bin/env"], new ProductionWorktreeProcessRunner(),
            new RecordingDirectoryCloner(), FileSystemLeanCacheStateProbe.Instance,
            name => name == "STRATALINT_LEAN_CACHE_SCOPE" ? "targeted" : null);

        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(obsolete));
        Assert.Contains("\"status\":\"scoped\"", result.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(LeanCacheStamp.PathFor(lake)));
    }

    [Fact]
    public void ScopedWarmthProbeFailureCannotFallBackToColdExecution()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        Directory.CreateDirectory(Path.Combine(repository.Path, ".lake"));
        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path,
            ["--", "/usr/bin/env"], new ProductionWorktreeProcessRunner(),
            new RecordingDirectoryCloner(),
            new DelegatingLeanCacheStateProbe(_ => new(OleanWarmth.ProbeFailed, "unreadable cache")),
            name => name == "STRATALINT_LEAN_CACHE_SCOPE" ? "targeted" : null);

        Assert.False(result.Success);
        Assert.Contains("cache warmth inspection failed", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("\"status\":\"scoped\"", result.Output, StringComparison.Ordinal);
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
