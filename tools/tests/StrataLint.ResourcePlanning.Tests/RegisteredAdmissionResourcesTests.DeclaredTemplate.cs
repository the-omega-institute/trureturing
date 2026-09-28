using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("OctahedralCochainSharpness", "push")]
    [InlineData("OctahedralCochainSharpness", "pr")]
    [InlineData("TripartiteH1Repair", "push")]
    [InlineData("TripartiteH1Repair", "pr")]
    public void ConsumedGraphFrozenPinsSelectDeclaredTemplateAndRetainTruthChecks(string module, string mode)
    {
        var plan = Plan("", $"Golden/Frozen/state/D5/S3/Combinatorics/Graph/{module}.lean.json", mode);
        Assert.Contains("test-declared-template", Strings(plan["stages"]!["engineering"]!["resources"]!));
        Assert.Contains("tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj",
            Strings(plan["execution"]!["tests"]!));
        foreach (var resource in new[] { "current", "filemap", "scribe" })
            Assert.Contains(resource, Strings(plan["resources"]!));
        Assert.Equal(mode == "pr", Strings(plan["resources"]!).Contains("delta"));
        Assert.Equal(mode == "pr" ? "required" : "not-applicable",
            plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        Assert.Contains("SL-008", Strings(plan["execution"]!["checks"]!));
        Assert.Contains("lake", Strings(EngineeringRequirements(plan)["tools"]!));
    }

    [Theory]
    [InlineData("tools/tests/StrataLint.DeclaredTemplate.Tests/DeclaredTemplateReviewTests.cs", "push", false)]
    [InlineData("tools/tests/StrataLint.DeclaredTemplate.Tests/DeclaredTemplateReviewTests.cs", "pr", false)]
    [InlineData("tools/TestSupport/StrataLint.DeclaredTemplateTestSupport/DeclaredTemplateFixture.cs", "push", true)]
    [InlineData("tools/TestSupport/StrataLint.DeclaredTemplateTestSupport/DeclaredTemplateFixture.cs", "pr", true)]
    public void DeclaredTemplateChangesRunOnlyTheirRegisteredConsumers(string path, string mode, bool shared)
    {
        var plan = Plan(path, "", mode);
        var consumers = new[] { "StrataLint.ArchitectureTests", "StrataLint.DeclaredTemplate.Tests", "StrataLint.RepositoryFileMap.Tests" }
            .Concat(shared ? new[] { "StrataLint.Tests" } : []);
        Assert.Equal(WithWorktreeContract(consumers.Append("StrataLint.RepositoryTopology.Tests").Order(StringComparer.Ordinal).Select(name => $"tools/tests/{name}/{name}.csproj")),
            Strings(plan["execution"]!["tests"]!));
    }
}
