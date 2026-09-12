using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapResourceParityTests
{
    [Fact]
    public void RepositoryNoResourceFamiliesAreExactlyTheApprovedReferences()
    {
        var map = FileMapLoader.LoadRepository(TestRepositoryLayout.FindRoot());
        Assert.Equal(new[] { "README.md",
            "docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md",
            "docs/develop/spec/trureturing_engineering_optimization_v1.md", "docs/reports/**" },
            map.Entries.Where(entry => entry.Require.IsEmpty).Select(entry => entry.Pattern));
        foreach (var path in new[] { "docs/develop/theory/input.md", "Library/Notes/input.md", "Problems/input.md",
            "Blueprint/D5/Result.md", "D5/ledger.md", "CLAUDE.md", "tools/scripts/workflow/ci_plan.py",
            "tools/StrataLint.Scribe/FileMap/FileMapResources.cs",
            "tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json" })
            Assert.NotEmpty(Assert.Single(map.Match(path)).Require);
        var filemap = Assert.Single(map.Resources, resource => resource.Id == "filemap");
        Assert.Equal(["current"], filemap.CacheLayers.ToArray());
        Assert.Equal(["build"], filemap.Prerequisites.ToArray());
        Assert.Equal(["judge"], Assert.Single(map.Resources, resource => resource.Id == "build").CacheLayers.ToArray());
        Assert.Equal(["elan", "engineering"], Assert.Single(map.Resources, resource => resource.Id == "engineering").CacheLayers.ToArray());
        Assert.DoesNotContain("lake", filemap.Tools);
    }

    [Fact]
    public void StrictLoaderAgreesWithSharedLightPlannerFixture()
    {
        var data = JsonNode.Parse(TestRepositoryLayout.ReadAllText(StrataLint.TestSupport.RepositoryRelativePath.Create(
            "tools/tests/StrataLint.Tests/Commands/FileMapPlanning/canonical.json")))!;
        var map = FileMapLoader.Parse(Encoding.UTF8.GetBytes(data["filemap"]!.GetValue<string>()), "canonical fixture");
        foreach (var item in data["cases"]!.AsArray())
        {
            var matches = map.Match(item!["path"]!.GetValue<string>());
            if (item["require"] is null) Assert.Empty(matches);
            else Assert.Equal(item["require"]!.AsArray().Select(value => value!.GetValue<string>()), Assert.Single(matches).Require);
        }
        Assert.Equal(data["resources"]!.AsArray().Select(value => value!["id"]!.GetValue<string>()),
            map.Resources.Select(resource => resource.Id));
        foreach (var resource in map.Resources)
        {
            var expected = data["resources"]!.AsArray().Single(value => value!["id"]!.GetValue<string>() == resource.Id)!;
            Assert.Equal(expected["stage"]!.GetValue<string>(), resource.Stage);
            Assert.Equal(expected["owner"]!.GetValue<string>(), resource.Owner);
            Assert.Equal(Strings(expected["prerequisites"]), resource.Prerequisites);
            Assert.Equal(Strings(expected["tools"]), resource.Tools);
            Assert.Equal(Strings(expected["cache_layers"]), resource.CacheLayers);
            Assert.Equal(Strings(expected["materials"]), resource.Materials);
        }
    }

    private static IEnumerable<string> Strings(JsonNode? node) => node!.AsArray().Select(value => value!.GetValue<string>());
}
