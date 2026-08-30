using StrataLint.Engine;

namespace StrataLint.Engine.Tests;

public sealed class SelfTestGovernancePolicyTests
{
    [Fact]
    public void TowerChainRequiresTheCanonicalJudges()
    {
        const string tower = """
            schema_version: 1
            components:
              - id: csharp-architecture
                kind: repository-files
                members:
                  - tools/tests/StrataLint.ArchitectureTests/MAP.md
                judged_by:
                  - architecture-tests
                  - banned-api-analyzers
                  - engineering-ci
                verification: verified
            bootstrap:
              id: bootstrap-pr-1
              judge: open
              reason: fixture
              genesis_event: sha256:0000000000000000000000000000000000000000000000000000000000000000
              commit: f000000000000000000000000000000000000000
              pull_request: 1
              verification: ASSUMED-UNVERIFIED
            """;

        Assert.Empty(SelfTestGovernancePolicy.InspectTower(tower));
        Assert.Contains(
            SelfTestGovernancePolicy.InspectTower(tower.Replace(
                "      - banned-api-analyzers\n",
                string.Empty,
                StringComparison.Ordinal)),
            finding => finding.Contains("judged_by", StringComparison.Ordinal));
    }

    [Fact]
    public void BannedApiProjectAndLockFixturesFailClosed()
    {
        const string project = """
            <Project><ItemGroup>
              <PackageReference Include="Microsoft.CodeAnalysis.BannedApiAnalyzers" PrivateAssets="all" />
              <AdditionalFiles Include="../Architecture/BannedSymbols.txt" />
              <AdditionalFiles Include="../Architecture/BannedSymbols.Determinism.txt" />
              <AdditionalFiles Include="../Architecture/BannedSymbols.Guid.txt" />
            </ItemGroup></Project>
            """;
        const string lockFile = """
            {"dependencies":{"net99.0":{"Microsoft.CodeAnalysis.BannedApiAnalyzers":{
              "type":"Direct","requested":"[1.2.3, )","resolved":"1.2.3"}}}}
            """;

        Assert.Empty(SelfTestGovernancePolicy.InspectBannedApiProject(
            project, requireGuidDenylist: true));
        Assert.Empty(SelfTestGovernancePolicy.InspectBannedApiLock(lockFile, "1.2.3"));
        Assert.NotEmpty(SelfTestGovernancePolicy.InspectBannedApiProject(
            project.Replace(" PrivateAssets=\"all\"", string.Empty, StringComparison.Ordinal),
            requireGuidDenylist: true));
        Assert.Throws<FormatException>(() => SelfTestGovernancePolicy.ReadBannedApiVersion(
            "<Project><ItemGroup></ItemGroup></Project>"));
    }

    [Fact]
    public void BannedSymbolMatricesAreExact()
    {
        var culture = string.Join('\n', SelfTestGovernancePolicy.RequiredCultureSensitiveMembers());
        var determinism = string.Join('\n', SelfTestGovernancePolicy.RequiredAmbientRuntimeMembers);
        const string guid = "M:System.Guid.NewGuid";

        Assert.Empty(SelfTestGovernancePolicy.InspectBannedSymbols(
            culture, determinism, guid));
        Assert.NotEmpty(SelfTestGovernancePolicy.InspectBannedSymbols(
            culture + "\nM:System.String.Clone", determinism, guid));
    }

    [Fact]
    public void ToolsNamespaceFixtureRejectsBucketNamespace()
    {
        Assert.Empty(SelfTestGovernancePolicy.CheckToolsNamespace(
            "tools/StrataLint.Engine/Coordinates/Gid.cs",
            "StrataLint.Engine",
            "namespace StrataLint.Engine;\n"));
        Assert.NotEmpty(SelfTestGovernancePolicy.CheckToolsNamespace(
            "tools/StrataLint.Engine/Coordinates/Gid.cs",
            "StrataLint.Engine",
            "namespace StrataLint.Engine.Coordinates;\n"));
    }
}
