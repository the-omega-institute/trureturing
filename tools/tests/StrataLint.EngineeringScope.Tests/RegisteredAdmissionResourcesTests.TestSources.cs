using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("JudgeSeedTask.Tests", false)]
    [InlineData("StrataLint.Anchors.Tests", false)]
    [InlineData("StrataLint.ArchitectureTests", false)]
    [InlineData("StrataLint.Cache.Tests", false)]
    [InlineData("StrataLint.Engine.Tests", false)]
    [InlineData("StrataLint.EngineeringScope.Tests", false)]
    [InlineData("StrataLint.Lean.Tests", true)]
    [InlineData("StrataLint.Policy.Tests", false)]
    [InlineData("StrataLint.Repository.Tests", false)]
    [InlineData("StrataLint.Scribe.Documents.Tests", false)]
    [InlineData("StrataLint.Scribe.Tests", false)]
    [InlineData("StrataLint.ScriptTests", false)]
    [InlineData("StrataLint.Tests", true)]
    [InlineData("Trureturing.Truth.Tests", false)]
    public void RegisteredTestSourceSelectsItsCompleteProjectAndSourceContracts(string name, bool lake)
    {
        foreach (var mode in new[] { "pr", "push" })
        {
            var plan = Plan($"tools/tests/{name}/AdmissionResourceProbe.cs", "", mode);
            var projects = Strings(plan["execution"]!["projects"]!).Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal));
            var expected = new[] { $"tools/tests/{name}/{name}.csproj",
                "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj",
                "tools/tests/StrataLint.Repository.Tests/StrataLint.Repository.Tests.csproj" }.Distinct().Order(StringComparer.Ordinal);
            Assert.Equal(expected, projects);
            Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
            Assert.DoesNotContain("delta", Strings(plan["resources"]!));
            Assert.DoesNotContain("current", Strings(plan["resources"]!));
            Assert.Equal(new[] { "SL-003", "filemap" }, Strings(plan["execution"]!["checks"]!));
            Assert.Equal(new[] { "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
            Assert.Equal(mode == "pr" ? "required" : "not-applicable", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
            Assert.Equal(lake, Strings(plan["tools"]!).Contains("lake"));
            Assert.Equal(lake, Strings(plan["cache_layers"]!).Contains("elan"));
            foreach (var cache in new[] { "dependency", "project", "report" }) Assert.DoesNotContain(cache, Strings(plan["cache_layers"]!));
        }
    }

    [Theory]
    [InlineData("tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj")]
    [InlineData("tools/tests/StrataLint.Lean.Tests/packages.lock.json")]
    [InlineData("tools/tests/Directory.Build.props")]
    [InlineData("Meta/engineering-projects.json")]
    public void TestSourcesDoNotHideFullEngineeringObligations(string input)
    {
        var plan = Plan("tools/tests/StrataLint.Engine.Tests/AdmissionResourceProbe.cs", input);
        Assert.Contains("engineering", Strings(plan["resources"]!));
        Assert.Contains("delta", Strings(plan["resources"]!));
        Assert.Contains("lean-report", Strings(plan["execution"]!["steps"]!));
        var registered = JsonNode.Parse(TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/engineering-projects.json")))!["projects"]!.AsArray();
        var expected = registered.Where(row => row!["ci"]!.GetValue<bool>()).Select(row => row!["path"]!.GetValue<string>()).Order(StringComparer.Ordinal);
        Assert.Equal(expected, Strings(plan["execution"]!["projects"]!).Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal)));
    }

    [Fact]
    public void TestSourcesPreserveMetadataSemanticEvidenceWithoutRestoringFullEngineering()
    {
        var plan = Plan("tools/tests/StrataLint.Engine.Tests/AdmissionResourceProbe.cs", "Meta/Digestion/backfill/admission-resource-probe.json");
        Assert.Contains("delta-metadata", Strings(plan["resources"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        Assert.Equal(new[] { "SL-003", "SL-015", "SL-019", "filemap" }, Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "lean-report", "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
        Assert.Equal(new[] { "StrataLint.ArchitectureTests", "StrataLint.Engine.Tests", "StrataLint.Repository.Tests" },
            Strings(plan["execution"]!["projects"]!).Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal))
                .Select(Path.GetFileNameWithoutExtension));
    }

    [Theory]
    [InlineData("tools/tests/JudgeSeedTask.Tests/JudgeSeedInputsTests.cs")]
    [InlineData("tools/tests/StrataLint.EngineeringScope.Tests/ResourceAdapterTests.cs")]
    [InlineData("tools/tests/Trureturing.Truth.Tests/AdmissionResourceProbe.cs")]
    public void TestSourceNoResourceCompanionDoesNotChangeSelection(string path)
    {
        var alone = Plan(path, "");
        var mixed = Plan(path, RegisteredNoResourceContent);
        foreach (var field in new[] { "resources", "tools", "cache_layers", "selected_stages", "execution" })
            Assert.True(JsonNode.DeepEquals(alone[field], mixed[field]), field);
    }
}
