using StrataLint.TestSupport;

namespace StrataLint.ArchitectureTests;

public sealed class EngineeringProjectRegistrationTests
{

    [Fact]
    public void RepositoryRegistrationKeepsBothProofProjects()
    {
        var topology = RepositoryRules.ReadTrackedProjects(RepositoryLayout.FindRoot());
        Assert.Equal(new[]
        {
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/tests/CompileFailProof/CompileFailProof.csproj",
        }, topology.Projects.Where(project => project.Registration.Role == "compile-fail-proof").Select(project => project.Path));
    }
}
