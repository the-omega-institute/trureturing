using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("tools/tests/StrataLint.DeclaredTemplate.Tests/DeclaredTemplateReviewTests.cs", "push", false)]
    [InlineData("tools/tests/StrataLint.DeclaredTemplate.Tests/DeclaredTemplateReviewTests.cs", "pr", false)]
    [InlineData("tools/TestSupport/StrataLint.DeclaredTemplateTestSupport/DeclaredTemplateFixture.cs", "push", true)]
    [InlineData("tools/TestSupport/StrataLint.DeclaredTemplateTestSupport/DeclaredTemplateFixture.cs", "pr", true)]
    public void DeclaredTemplateChangesRunOnlyTheirRegisteredConsumers(string path, string mode, bool shared)
    {
        var plan = Plan(path, "", mode);
        var consumers = new[] { "StrataLint.ArchitectureTests", "StrataLint.DeclaredTemplate.Tests" }
            .Concat(shared ? new[] { "StrataLint.Tests" } : []);
        Assert.Equal(WithRepositoryContract(consumers.Append("StrataLint.RepositoryTopology.Tests").Order(StringComparer.Ordinal).Select(name => $"tools/tests/{name}/{name}.csproj")),
            Strings(plan["execution"]!["tests"]!));
    }
}
