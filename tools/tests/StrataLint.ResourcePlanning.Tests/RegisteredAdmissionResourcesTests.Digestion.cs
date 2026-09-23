using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Theory]
    [InlineData("tools/tests/StrataLint.Digestion.Tests/DigestionCasStoreTests.cs", "push", false)]
    [InlineData("tools/tests/StrataLint.Digestion.Tests/DigestionCasStoreTests.cs", "pr", false)]
    [InlineData("tools/TestSupport/StrataLint.DigestionTestSupport/DigestionTestSupport.cs", "push", true)]
    [InlineData("tools/TestSupport/StrataLint.DigestionTestSupport/DigestionTestSupport.cs", "pr", true)]
    public void DigestionChangesRunOnlyTheirRegisteredConsumers(string path, string mode, bool shared)
    {
        var plan = Plan(path, "", mode);
        var consumers = new[] { "StrataLint.ArchitectureTests", "StrataLint.Digestion.Tests" }
            .Concat(shared ? new[] { "StrataLint.Tests" } : []);
        Assert.Equal(WithRepositoryContract(consumers.Select(name => $"tools/tests/{name}/{name}.csproj")),
            Strings(plan["execution"]!["tests"]!));
    }
}
