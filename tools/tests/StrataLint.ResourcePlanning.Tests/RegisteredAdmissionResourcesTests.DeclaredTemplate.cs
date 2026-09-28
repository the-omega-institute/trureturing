using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("tools/lean-inspector/tests/test_instance_support.py", "push")]
    [InlineData("tools/lean-inspector/tests/test_instance_support.py", "pr")]
    [InlineData("tools/lean-inspector/tests/test_native_support.py", "push")]
    [InlineData("tools/lean-inspector/tests/test_native_support.py", "pr")]
    public void InstanceSupportRuntimeChangesSelectDeclaredTemplate(string path, string mode)
    {
        var plan = Plan(path, "", mode);
        Assert.Contains("tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj",
            Strings(plan["execution"]!["tests"]!));
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
