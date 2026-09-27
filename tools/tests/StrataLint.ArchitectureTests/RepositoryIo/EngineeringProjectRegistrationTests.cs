using StrataLint.TestSupport;

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
}
