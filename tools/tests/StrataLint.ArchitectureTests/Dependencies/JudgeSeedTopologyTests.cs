using System.Text.Json.Nodes;

namespace StrataLint.ArchitectureTests;

public sealed class JudgeSeedTopologyTests
{
    private const string Product = "tools/scripts/report/JudgeSeedTask.csproj";
    private const string Owner = "tools/tests/JudgeSeedTask.Tests/JudgeSeedTask.Tests.csproj";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ActualJudgeSeedProjectRequiresItsOwner(bool removeOwner)
    {
        var root = RepositoryLayout.FindRoot();
        var current = RawRepositorySnapshot.Create(
            GitIndexRepositoryFiles.EnumerateDeclared(root, "tools")
                .Where(static entry => entry.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
                .Select(static entry => RawRepositoryEntry.FromText(
                    entry.RelativePath,
                    File.ReadAllText(entry.FullPath))));
        Assert.Contains(current.Entries, entry => entry.Path == Product);
        var baseline = Registered(current.Entries.Where(entry => entry.Path != Product && entry.Path != Owner));
        var candidate = Registered(current.Entries.Where(entry => !removeOwner || entry.Path != Owner));

        var result = RepositoryRules.EvaluateSnapshots(baseline, candidate);

        if (removeOwner)
        {
            Assert.False(result.IsAccepted);
            Assert.Equal("candidate introduces topology debt: missing-owned-project JudgeSeedTask -> JudgeSeedTask.Tests",
                result.Message);
            Assert.Equal(new TestProjectTopologyDebt("missing-owned-project", "JudgeSeedTask", "JudgeSeedTask.Tests"),
                Assert.Single(result.IntroducedDebt));
        }
        else
        {
            Assert.True(result.IsAccepted, result.Message);
            Assert.Empty(result.IntroducedDebt);
            Assert.Contains(Owner, EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(candidate)));
        }
    }

    private static RepositorySnapshot Registered(IEnumerable<RawRepositoryEntry> entries)
    {
        var files = entries.ToArray();
        var paths = files.Select(entry => entry.Path).ToHashSet(StringComparer.Ordinal);
        var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(RepositoryLayout.FindRoot(), EngineeringProjectRegistry.ManifestPath)))!;
        var registrations = manifest["projects"]!.AsArray();
        foreach (var item in registrations.ToArray())
            if (!paths.Contains(item!["path"]!.GetValue<string>())) registrations.Remove(item);
        return Decode(files.Append(RawRepositoryEntry.FromText(EngineeringProjectRegistry.ManifestPath, manifest.ToJsonString())));
    }

    private static RepositorySnapshot Decode(IEnumerable<RawRepositoryEntry> entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
}
