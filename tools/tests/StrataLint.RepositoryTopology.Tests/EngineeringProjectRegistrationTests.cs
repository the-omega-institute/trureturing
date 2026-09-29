using System.Text;
using StrataLint.Engine;
using StrataLint.EngineeringScope;

namespace StrataLint.RepositoryTopology.Tests;

public sealed class EngineeringProjectRegistrationTests
{
    [Xunit.Fact]
    public void CurrentRepositoryExecutionAndBuildInputsExpandOnlyExplicitExistingMaterials()
    {
        var root = TestRepositoryLayout.FindRoot();
        var tracked = StrataLint.Engine.GitIndexRepositoryFiles.EnumerateTracked(root)
            .ToDictionary(entry => entry.RelativePath, entry => entry.Mode, StringComparer.Ordinal);
        var untracked = BoundedProcessRunner.Run("git", ["ls-files", "--others", "--exclude-standard", "-z"],
            root, TimeSpan.FromSeconds(120), 64 * 1024 * 1024);
        var utf8 = new UTF8Encoding(false, true);
        Assert.True(untracked.ExitCode == 0, utf8.GetString(untracked.StandardError));
        var inspectedDirectories = new HashSet<string>(StringComparer.Ordinal);
        var paths = tracked.Keys.Concat(utf8.GetString(untracked.StandardOutput).Split('\0', StringSplitOptions.RemoveEmptyEntries))
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)
            .Where(path =>
            {
                Assert.True(RepoPath.TryCreate(path, out _), $"invalid repository path: {path}");
                if (tracked.TryGetValue(path, out var mode))
                    Assert.True(mode is "100644" or "100755" or "120000", $"non-regular repository entry: {path} ({mode})");
                FileMapSymlinkPolicy.RequirePlainAncestors(root, path, inspectedDirectories);
                var info = new FileInfo(Path.Combine(root, path));
                if (info.LinkTarget is not null) return true;
                if (!info.Exists) return false;
                Assert.False((info.Attributes & FileAttributes.ReparsePoint) != 0, $"non-regular repository entry: {path}");
                return true;
            }).ToArray();
        // Read consumes only the manifest body and the complete existing path set.
        // Empty Content is deliberately unused; snapshot decoding and declared-link
        // validation remain the responsibility of the snapshot reader's own tests.
        var sources = paths.Select(path => new EngineeringSource(path,
            path == EngineeringProjectRegistry.ManifestPath
                ? utf8.GetString(File.ReadAllBytes(Path.Combine(root, path))) : string.Empty)).ToArray();
        var registry = EngineeringProjectRegistry.Read(sources);
        foreach (var project in registry.Projects)
        {
            Assert.NotEmpty(EngineeringProjectRegistry.ExpandInputs(paths, project.BuildInputs!, [], project.Path));
            if (project.IsTest)
                _ = EngineeringProjectRegistry.ExpandInputs(paths, project.ExecutionInputs!, project.ExecutionExcludes!, project.Path);
        }
    }
}
