using StrataLint.Engine;
using StrataLint.TestSupport;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

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
    [Fact]
    public void RegisteredNonNearestOwnerWins()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/near/Near.csproj", "<Project><PropertyGroup><RootNamespace>Nearest</RootNamespace></PropertyGroup></Project>");
        fixture.Write("tools/near/Source.cs", "namespace Declared.Space;");
        fixture.Register(Owner("tools/near/Source.cs"),
            new("tools/near/Near.csproj", "Nearest", "test-support", false, []));
        Assert.Empty(fixture.Inspect());
    }

    [Fact]
    public void UnregisteredNeighborCannotChangeRegisteredOwner()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/near/Source.cs", "namespace Declared.Space;");
        fixture.Register(Owner("tools/near/Source.cs"));
        Assert.Empty(fixture.Inspect());
        fixture.Write("tools/near/Neighbor.csproj", "<Project><PropertyGroup><RootNamespace>Wrong</RootNamespace></PropertyGroup></Project>");
        Assert.Empty(fixture.Inspect());
        fixture.Track();
        Assert.Contains("unregistered engineering project: tools/near/Neighbor.csproj", Assert.Single(fixture.Inspect()));
    }

    [Fact]
    public void DeclaredNamespaceIsIndependentOfProjectXmlAndAssembly()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/owner/Source.cs", "namespace Xml.Namespace;");
        fixture.Register(Owner("tools/owner/Source.cs"));
        Assert.Equal("tools/owner/Source.cs: namespace Xml.Namespace does not match Declared.Space",
            Assert.Single(fixture.Inspect()));
    }

    [Fact]
    public void ExactGlobalNamespaceExceptionAllowsArbitraryRegisteredPath()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/shared/Bootstrap.cs", "internal class Bootstrap {}");
        fixture.Register(Owner("tools/shared/Bootstrap.cs") with
        { GlobalNamespaceExceptions = ["tools/shared/Bootstrap.cs"] });
        Assert.Empty(fixture.Inspect());
    }

    [Fact]
    public void SameBasenameElsewhereDoesNotInheritGlobalException()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/owner/AssemblyInfo.cs", "// registered exception");
        fixture.Write("tools/owner/other/AssemblyInfo.cs", "internal class MustHaveNamespace {}");
        fixture.Register(Owner("tools/owner/**/*.cs") with
        { GlobalNamespaceExceptions = ["tools/owner/AssemblyInfo.cs"] });
        Assert.Equal("tools/owner/other/AssemblyInfo.cs: source must declare exactly one namespace",
            Assert.Single(fixture.Inspect()));
    }

    [Fact]
    public void ExceptionDoesNotPermitWrongOrMultipleNamespaces()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/owner/AssemblyInfo.cs", "namespace Wrong;");
        fixture.Register(Owner("tools/owner/AssemblyInfo.cs") with
        { GlobalNamespaceExceptions = ["tools/owner/AssemblyInfo.cs"] });
        Assert.Equal("tools/owner/AssemblyInfo.cs: namespace Wrong does not match Declared.Space",
            Assert.Single(fixture.Inspect()));
        fixture.Write("tools/owner/AssemblyInfo.cs", "namespace Declared.Space;\nnamespace Wrong;");
        Assert.Equal("tools/owner/AssemblyInfo.cs: source must declare exactly one namespace",
            Assert.Single(fixture.Inspect()));
    }

    [Fact]
    public void ExplicitLinkedSourceUsesDeclarationAndBlueprintScopeIsExplicit()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("shared/Linked.cs", "namespace Declared.Space;");
        fixture.Write("Blueprint/Definition.scribe.cs", "namespace Definition.Data;");
        fixture.Register(Owner("shared/Linked.cs", "Blueprint/**/*.scribe.cs") with
        { NamespaceExclude = ["Blueprint/**/*.scribe.cs"] });
        Assert.Empty(fixture.Inspect());
        fixture.Write("shared/Linked.cs", "namespace Wrong;");
        Assert.Equal("shared/Linked.cs: namespace Wrong does not match Declared.Space", Assert.Single(fixture.Inspect()));
    }

    [Fact]
    public void MissingSourceOwnershipFailsBeforeNamespaceValidation()
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/owner/Undeclared.cs", "namespace Wrong;");
        fixture.Register(Owner());
        Assert.Contains("unregistered engineering source: tools/owner/Undeclared.cs", Assert.Single(fixture.Inspect()));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ConflictingSharedNamespaceOrExceptionFailsBeforeChecking(bool exceptionConflict)
    {
        using var fixture = new NamespaceFixture();
        const string source = "tools/shared/Shared.cs";
        fixture.Write(source, "namespace Wrong;");
        var second = new EngineeringProjectFixture("tools/other/Other.csproj", "Other", "test-support", false,
            [source], RootNamespace: exceptionConflict ? "Declared.Space" : "Other.Space",
            GlobalNamespaceExceptions: exceptionConflict ? [source] : []);
        fixture.Write(second.Path, "<Project />");
        fixture.Register(Owner(source), second);
        var finding = Assert.Single(fixture.Inspect());
        Assert.Contains("conflicting namespace registration", finding);
        Assert.Contains(source, finding);
        Assert.Contains("tools/owner/Owner.csproj", finding);
        Assert.Contains(second.Path, finding);
    }

    [Fact]
    public void MatchingSharedNamespaceDeclarationsAreAllowed()
    {
        using var fixture = new NamespaceFixture();
        const string source = "tools/shared/Shared.cs";
        fixture.Write(source, "namespace Declared.Space;");
        fixture.Write("tools/other/Other.csproj", "<Project />");
        fixture.Register(Owner(source), new("tools/other/Other.csproj", "Other", "test-support", false,
            [source], RootNamespace: "Declared.Space"));
        Assert.Empty(fixture.Inspect());
    }

    [Theory]
    [InlineData("source")]
    [InlineData("exception")]
    [InlineData("scope")]
    public void DanglingDeclarationsFailBeforeNamespaceValidation(string kind)
    {
        using var fixture = new NamespaceFixture();
        fixture.Write("tools/owner/Source.cs", "namespace Wrong;");
        var owner = Owner("tools/owner/Source.cs");
        const string missing = "tools/owner/Missing.cs";
        fixture.Register(kind switch
        {
            "source" => owner with { Include = [missing] },
            "exception" => owner with { GlobalNamespaceExceptions = [missing] },
            _ => owner with { NamespaceExclude = [missing] },
        });
        var finding = Assert.Single(fixture.Inspect());
        Assert.Contains(missing, finding);
        Assert.Contains("registered", finding);
    }

    [Fact]
    public void GlobalExceptionMustBelongToItsProjectAndCheckedScope()
    {
        using var fixture = new NamespaceFixture();
        const string source = "tools/shared/Shared.cs";
        fixture.Write(source, "namespace Declared.Space;");
        fixture.Write("tools/other/Other.csproj", "<Project />");
        fixture.Register(Owner() with { GlobalNamespaceExceptions = [source] },
            new("tools/other/Other.csproj", "Other", "test-support", false, [source], RootNamespace: "Declared.Space"));
        Assert.Contains("registered global namespace exception", Assert.Single(fixture.Inspect()));
        fixture.Register(Owner(source) with { GlobalNamespaceExceptions = [source], NamespaceExclude = [source] },
            new("tools/other/Other.csproj", "Other", "test-support", false, []));
        Assert.Contains("registered global namespace exception", Assert.Single(fixture.Inspect()));
    }

    private static EngineeringProjectFixture Owner(params string[] include) =>
        new("tools/owner/Owner.csproj", "Unrelated.Assembly", "test-support", false, include,
            RootNamespace: "Declared.Space");

    private sealed class NamespaceFixture : IDisposable
    {
        private readonly TemporaryDirectory directory = new();

        internal NamespaceFixture()
        {
            Git("init", "--quiet");
            Write("tools/owner/Owner.csproj", "<Project><PropertyGroup><RootNamespace>Xml.Namespace</RootNamespace></PropertyGroup></Project>");
        }

        internal void Write(string path, string text)
        {
            var fullPath = Path.Combine(directory.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllText(fullPath, text);
        }

        internal void Register(params EngineeringProjectFixture[] projects)
        {
            Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(projects));
            Track();
        }

        internal void Track() => Git("add", ".");
        internal string[] Inspect() => SelfTestGovernancePolicy.InspectToolsNamespaces(directory.Path).ToArray();
        private void Git(params string[] arguments) => Assert.Equal(0, TestProcessRunner.Run(
            "git", arguments, directory.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024).ExitCode);
        public void Dispose() => directory.Dispose();
    }

}
