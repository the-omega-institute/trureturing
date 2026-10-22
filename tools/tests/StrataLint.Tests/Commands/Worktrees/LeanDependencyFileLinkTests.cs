using System.Text.Json.Nodes;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void DependencyRecoveryPreservesPackageRelativeFileLinks(bool stamped, bool existingLink)
    {
        using var repository = new TemporaryDirectory();
        InitializeFileLinkRepository(repository.Path);
        WriteCache(repository.Path, "donor build", projectWarm: true);
        var donorPackage = Path.Combine(repository.Path, ".lake/packages/batteries");
        WriteRestoreFixture(donorPackage, "README.md", "donor documentation");
        WriteRestoreFixture(donorPackage, "docs/other.md", "additional documentation");
        var target = AddWorktree(repository.Path, "package-file-link");
        WriteCache(target, "retained compiler", stamp: stamped, mathlibComplete: false, projectWarm: true);
        var lake = Path.Combine(target, ".lake");
        var package = Path.Combine(lake, "packages/batteries");
        var link = Path.Combine(package, "docs/README.md");
        WriteRestoreFixture(package, "README.md", "authoritative target documentation");
        WriteRestoreFixture(package, "docs/target-only.md", "target-only source");
        WriteRestoreFixture(package, ".lake/build/target-only.olean", "target-only dependency compiler");
        WriteRestoreFixture(lake, "build/stratalint/raw-lean-report.json", "target-only report");
        if (existingLink) File.CreateSymbolicLink(link, "../README.md");
        var before = Directory.GetFiles(lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, path => (Bytes: File.ReadAllBytes(path), Time: File.GetLastWriteTimeUtc(path)));
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner
        {
            // The recording cloner does not preserve file links. Model the native clone's
            // pinned Batteries docs/README.md -> ../README.md entry at its public boundary.
            AfterClone = (source, staged) =>
            {
                if (Path.GetFileName(source) == "packages")
                    File.CreateSymbolicLink(Path.Combine(staged, "batteries/docs/README.md"), "../README.md");
            },
        };

        var result = WorktreeCommand.Run(repository.Path, stamped
            ? ["ensure-cache", "--path", target, "--restore-dependencies"]
            : ["ensure-cache", "--path", target], runner, cloner);

        Assert.True(result.Success, result.Error);
        Assert.Equal("../README.md", new FileInfo(link).LinkTarget);
        Assert.Equal("authoritative target documentation", File.ReadAllText(link));
        foreach (var (path, prior) in before)
        {
            Assert.Equal(prior.Bytes, File.ReadAllBytes(path));
            Assert.Equal(prior.Time, File.GetLastWriteTimeUtc(path));
        }
        Assert.Equal("additional documentation", File.ReadAllText(Path.Combine(package, "docs/other.md")));
        foreach (var directory in new[] { lake, Path.Combine(lake, "packages"), package })
            Assert.False(File.GetAttributes(directory).HasFlag(FileAttributes.ReparsePoint));
        Assert.Empty(Directory.GetDirectories(lake, "*.stage-*"));
        Assert.Equal(stamped ? 1 : 2, cloner.Invocations.Count);
        Assert.DoesNotContain(runner.Invocations, call => Path.GetFileName(call.FileName) is "lake" or "lean");
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(stamped ? "restored" : "seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
    }

    [Theory]
    [InlineData(false, "escape")]
    [InlineData(true, "escape")]
    [InlineData(false, "absolute")]
    [InlineData(true, "absolute")]
    [InlineData(false, "loop")]
    [InlineData(true, "loop")]
    [InlineData(false, "directory-hop")]
    [InlineData(true, "directory-hop")]
    [InlineData(false, "directory")]
    [InlineData(true, "directory")]
    [InlineData(false, "dangling")]
    [InlineData(true, "dangling")]
    [InlineData(false, "package-root")]
    [InlineData(true, "package-root")]
    public void DependencyRecoveryRejectsUnsafePackageLinksWithoutFollowingThem(bool atTarget, string kind)
    {
        using var repository = new TemporaryDirectory();
        using var outside = new TemporaryDirectory();
        InitializeFileLinkRepository(repository.Path);
        WriteCache(repository.Path, "donor build", projectWarm: true);
        var donorPackage = Path.Combine(repository.Path, ".lake/packages/batteries");
        WriteRestoreFixture(donorPackage, "README.md", "donor documentation");
        WriteRestoreFixture(donorPackage, "docs/other.md", "additional documentation");
        var target = AddWorktree(repository.Path, "unsafe-package-link");
        WriteCache(target, "retained compiler", mathlibComplete: false, projectWarm: true);
        var lake = Path.Combine(target, ".lake");
        WriteRestoreFixture(lake, "build/stratalint/raw-lean-report.json", "retained report");
        WriteRestoreFixture(outside.Path, "README.md", "outside bytes");
        var before = Directory.GetFiles(lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        var unsafeLink = "";
        var linkText = "";
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, staged) =>
            {
                var package = Path.Combine(atTarget ? Path.Combine(lake, "packages") : staged, "batteries");
                if (kind == "package-root")
                {
                    if (Directory.Exists(package)) Directory.Delete(package, recursive: true);
                    Directory.CreateDirectory(Path.GetDirectoryName(package)!);
                    Directory.CreateSymbolicLink(package, outside.Path);
                    unsafeLink = package;
                    linkText = outside.Path;
                    return;
                }
                WriteRestoreFixture(package, "README.md", "local documentation");
                WriteRestoreFixture(package, "docs/local.md", "local documentation");
                unsafeLink = Path.Combine(package, "docs/README.md");
                linkText = kind switch
                {
                    "escape" => "../../outside.md",
                    "absolute" => Path.Combine(outside.Path, "README.md"),
                    "loop" => "../loop",
                    "directory-hop" => "jump/../local.md",
                    "directory" => "../docs",
                    _ => "../absent.md",
                };
                if (kind == "escape") WriteRestoreFixture(Path.GetDirectoryName(package)!, "outside.md", "outside package");
                if (kind == "loop") File.CreateSymbolicLink(Path.Combine(package, "loop"), "docs/README.md");
                if (kind == "directory-hop") Directory.CreateSymbolicLink(Path.Combine(package, "docs/jump"), outside.Path);
                File.CreateSymbolicLink(unsafeLink, linkText);
                if (atTarget)
                    File.CreateSymbolicLink(Path.Combine(staged, "batteries/docs/README.md"), "../README.md");
            },
        };

        var result = WorktreeCommand.Run(repository.Path,
            ["ensure-cache", "--path", target, "--restore-dependencies"], runner, cloner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        foreach (var (path, bytes) in before) Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.Equal("outside bytes", File.ReadAllText(Path.Combine(outside.Path, "README.md")));
        Assert.Single(Directory.GetFiles(outside.Path));
        if (atTarget) Assert.Equal(linkText, new FileInfo(unsafeLink).LinkTarget);
        Assert.Empty(Directory.GetDirectories(lake, "*.stage-*"));
        Assert.DoesNotContain(runner.Invocations, call => Path.GetFileName(call.FileName) is "lake" or "lean");
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("failed", receipt.RootElement.GetProperty("status").GetString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingStampBuildRecoveryStillRejectsRelativeFileLinks(bool atTarget)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor build", projectWarm: true);
        var target = AddWorktree(repository.Path, "build-file-link");
        WriteCache(target, "retained compiler", stamp: false, mathlibComplete: false, projectWarm: true);
        var lake = Path.Combine(target, ".lake");
        WriteRestoreFixture(lake, "build/stratalint/raw-lean-report.json", "retained report");
        var before = Directory.GetFiles(lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (source, staged) =>
            {
                if (Path.GetFileName(source) != "build") return;
                var build = atTarget ? Path.Combine(lake, "build") : staged;
                File.CreateSymbolicLink(Path.Combine(build, "file-link"), "cache.bin");
                if (atTarget) File.WriteAllText(Path.Combine(staged, "file-link"), "incoming conflict");
            },
        };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(), cloner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        foreach (var (path, bytes) in before) Assert.Equal(bytes, File.ReadAllBytes(path));
        if (atTarget) Assert.Equal("cache.bin", new FileInfo(Path.Combine(lake, "build/file-link")).LinkTarget);
        Assert.False(File.Exists(LeanCacheStamp.PathFor(lake)));
        Assert.Empty(Directory.GetDirectories(lake, "*.stage-*"));
        using var receipt = ParseReceipt(result.Error);
        Assert.Contains("forbidden symlink", receipt.RootElement.GetProperty("reason").GetString());
    }

    private static void InitializeFileLinkRepository(string root)
    {
        InitializeRepository(root);
        var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "lake-manifest.json")))!;
        manifest["packages"]!.AsArray().Add(new JsonObject
        {
            ["type"] = "git", ["name"] = "batteries", ["rev"] = "66e469188fe07963e5cf666c7d4433f45b8131c5",
            ["url"] = "https://github.com/leanprover-community/batteries", ["inputRev"] = "main",
            ["subDir"] = null, ["configFile"] = "lakefile.toml", ["manifestFile"] = "lake-manifest.json",
            ["inherited"] = true,
        });
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), manifest.ToJsonString());
        StrataLint.TestSupport.RegPackageFixture.Write(root);
        Git(root, "add", "lake-manifest.json", "Reg", "tools/lean-inspector-reg");
        Git(root, "commit", "-m", "fixture dependency file link");
    }
}
