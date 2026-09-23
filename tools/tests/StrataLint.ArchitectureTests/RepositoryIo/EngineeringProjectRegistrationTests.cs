using StrataLint.TestSupport;
using System.Text;

namespace StrataLint.ArchitectureTests;

public sealed class EngineeringProjectRegistrationTests
{

    [Fact]
    public void RepositoryRegistrationKeepsScriptCiExclusionAndBothProofProjects()
    {
        var topology = RepositoryRules.ReadTrackedProjects(RepositoryLayout.FindRoot());
        const string scripts = "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
        Assert.Equal("cross-cutting-test", Assert.Single(topology.Projects, project => project.Path == scripts).Registration.Role);
        Assert.DoesNotContain(scripts, EngineeringTestPlanPolicy.Evaluate(topology));
        Assert.Equal(new[]
        {
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/tests/CompileFailProof/CompileFailProof.csproj",
        }, topology.Projects.Where(project => project.Registration.Role == "compile-fail-proof").Select(project => project.Path));
    }

    [Fact]
    public void CurrentRepositoryExecutionAndBuildInputsExpandOnlyExplicitExistingMaterials()
    {
        var root = RepositoryLayout.FindRoot();
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
                ? File.ReadAllText(Path.Combine(root, path), utf8) : string.Empty)).ToArray();
        var registry = EngineeringProjectRegistry.Read(sources);
        foreach (var project in registry.Projects)
        {
            Assert.NotEmpty(EngineeringProjectRegistry.ExpandInputs(paths, project.BuildInputs!, [], project.Path));
            if (project.IsTest)
                _ = EngineeringProjectRegistry.ExpandInputs(paths, project.ExecutionInputs!, project.ExecutionExcludes!, project.Path);
        }
    }
}
