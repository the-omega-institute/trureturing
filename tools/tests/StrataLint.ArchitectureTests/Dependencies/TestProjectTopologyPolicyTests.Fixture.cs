namespace StrataLint.ArchitectureTests;

public sealed partial class TestProjectTopologyPolicyTests
{
    private static (TestProjectTopologySnapshot ProtectedBase, TestProjectTopologySnapshot Candidate)
        EqualSizedDebtSwap()
    {
        var protectedBase = Snapshot(
            OwnedTest(
                "Legacy.Tests",
                "Legacy.Tests",
                "../../Legacy/Legacy.csproj"));
        var candidate = Snapshot(
            Production("Legacy", "Legacy"),
            OwnedTest(
                "Legacy.Tests",
                "Legacy.Tests",
                "../../Legacy/Legacy.csproj"),
            OwnedTest("Rogue.Tests", "Rogue.Tests"));
        return (protectedBase, candidate);
    }

    private static TestProjectTopologySnapshot Snapshot(
        params TestProjectTopologyProject[] projects) => new(projects);

    private static TestProjectTopologyProject Production(
        string directory,
        string assembly,
        string? projectStem = null,
        string extraProperty = "") => ProjectWithExtraProperty(
        $"tools/{directory}/{projectStem ?? directory}.csproj",
        assembly,
        xunit: false,
        extraProperty: extraProperty);

    private static TestProjectTopologyProject OwnedTest(
        string directory,
        string assembly,
        params string[] references) => ProjectWithDefaultProperties(
        $"tools/tests/{directory}/{directory}.csproj",
        assembly,
        xunit: true,
        references: references);

    private static TestProjectTopologyProject ProjectWithDefaultProperties(
        string path,
        string assembly,
        bool xunit,
        params string[] references) => ProjectWithExtraProperty(
        path,
        assembly,
        xunit,
        extraProperty: string.Empty,
        references);

    private static TestProjectTopologyProject ProjectWithExtraProperty(
        string path,
        string assembly,
        bool xunit,
        string extraProperty,
        params string[] references)
    {
        var packageReference = xunit
            ? "<PackageReference Include=\"xunit\" />"
            : string.Empty;
        var projectReferences = string.Join(
            string.Empty,
            references.Select(static reference =>
                $"<ProjectReference Include=\"{reference}\" />"));
        var content = $"""
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup>
                <AssemblyName>{assembly}</AssemblyName>
                {extraProperty}
              </PropertyGroup>
              <ItemGroup>
                {packageReference}
                {projectReferences}
              </ItemGroup>
            </Project>
            """;
        return new TestProjectTopologyProject(path, content);
    }

    private static TestProjectTopologyDebt Debt(
        string kind,
        string subject,
        string related) => new(kind, subject, related);
}
