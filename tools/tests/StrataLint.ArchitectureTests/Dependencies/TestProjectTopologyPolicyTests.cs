using StrataLint.TestSupport;
using TestProjectTopologyPolicy = StrataLint.Engine.RepositoryRules;

namespace StrataLint.ArchitectureTests;

public sealed partial class TestProjectTopologyPolicyTests
{
    private const string CanonicalHarnessPath =
        "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";

    [Fact]
    public void UnchangedBaseDebtIsAccepted()
    {
        var inherited = Snapshot(Production("Legacy", "Legacy"));

        var result = TestProjectTopologyPolicy.Evaluate(inherited, inherited);

        Assert.True(result.IsAccepted, result.Message);
        Assert.False(result.RequiresStrictReduction);
        Assert.Equal(
            [Debt("missing-owned-project", "Legacy", "Legacy.Tests")],
            result.BaseDebt.ToArray());
        Assert.Equal(result.BaseDebt.ToArray(), result.CandidateDebt.ToArray());
    }

    [Fact]
    public void NewProductionProjectWithoutOwnedTestIsRejected()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(Production("NewProduct", "NewProduct")));

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("missing-owned-project", "NewProduct", "NewProduct.Tests")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void RegisteredNestedProductionNeedsItsOwnedDual()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(ProjectWithDefaultProperties(
                "tools/Nested/NewProduct/NewProduct.csproj",
                "NewProduct",
                xunit: false)));

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("missing-owned-project", "NewProduct", "NewProduct.Tests")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void NamedTestSupportProjectIsOutsideTheProductionDualAndItsInboundReferences()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(
                Production("NewProduct", "NewProduct"),
                ProjectWithDefaultProperties(
                    "tools/TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj",
                    "StrataLint.TestSupport",
                    xunit: false),
                OwnedTest(
                    "NewProduct.Tests",
                    "NewProduct.Tests",
                    "../../NewProduct/NewProduct.csproj",
                    "../../TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj")));

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.CandidateDebt);
    }

    [Fact]
    public void RegisteredProductionAndOwnedPairIsAccepted()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(
                Production("NewProduct", "NewProduct"),
                OwnedTest(
                    "NewProduct.Tests",
                    "NewProduct.Tests",
                    "../../NewProduct/NewProduct.csproj")));

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.CandidateDebt);
    }

    [Fact]
    public void OwnedTestWithSecondProductionReferenceIsRejected()
    {
        var protectedBase = Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest("Alpha.Tests", "Alpha.Tests", "../../Alpha/Alpha.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", "../../Beta/Beta.csproj"));
        var candidate = Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest(
                "Alpha.Tests",
                "Alpha.Tests",
                "../../Alpha/Alpha.csproj",
                "../../Beta/Beta.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", "../../Beta/Beta.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.False(result.IsAccepted);
        Assert.Contains(
            Debt("extra-production-reference", "Alpha.Tests", "Beta"),
            result.IntroducedDebt);
    }

    [Fact]
    public void EqualSizedDebtSwapIsRejectedBySetContainment()
    {
        var (protectedBase, candidate) = EqualSizedDebtSwap();

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.False(result.IsAccepted);
        Assert.False(result.RequiresStrictReduction);
        Assert.Single(result.BaseDebt);
        Assert.Single(result.CandidateDebt);
        Assert.Equal(
            [Debt("orphan-owned-project", "Rogue.Tests", "Rogue")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void TouchingDebtVertexWithoutStrictReductionIsRejected()
    {
        var protectedBase = Snapshot(Production("Legacy", "Legacy"));
        var candidate = Snapshot(Production(
            "Legacy",
            "Legacy",
            extraProperty: "<Description>candidate touched this project</Description>"));

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.False(result.IsAccepted);
        Assert.True(result.RequiresStrictReduction);
        Assert.Equal(result.BaseDebt.ToArray(), result.CandidateDebt.ToArray());
    }

    [Fact]
    public void ChangingCleanVertexMayKeepCleanWithoutPayingUnrelatedDebt()
    {
        var protectedBase = Snapshot(
            Production("Legacy", "Legacy"),
            Production("Clean", "Clean"),
            OwnedTest("Clean.Tests", "Clean.Tests", "../../Clean/Clean.csproj"));
        var candidate = Snapshot(
            Production("Legacy", "Legacy"),
            Production(
                "Clean",
                "Clean",
                extraProperty: "<Description>clean edit</Description>"),
            OwnedTest("Clean.Tests", "Clean.Tests", "../../Clean/Clean.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.True(result.IsAccepted, result.Message);
        Assert.False(result.RequiresStrictReduction);
        Assert.Equal(result.BaseDebt.ToArray(), result.CandidateDebt.ToArray());
    }

    [Fact]
    public void CreatingMissingDualStrictlyContractsDebtAndIsAccepted()
    {
        var protectedBase = Snapshot(Production("Legacy", "Legacy"));
        var candidate = Snapshot(
            Production("Legacy", "Legacy"),
            OwnedTest(
                "Legacy.Tests",
                "Legacy.Tests",
                "../../Legacy/Legacy.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.True(result.IsAccepted, result.Message);
        Assert.True(result.RequiresStrictReduction);
        Assert.Single(result.BaseDebt);
        Assert.Empty(result.CandidateDebt);
    }

    [Fact]
    public void CaseOnlyChangeToInheritedDebtIdentityIsNotIntroducedDebt()
    {
        var protectedBase = Snapshot(
            Production("Closed", "Closed"),
            Production("Remaining", "Remaining"));
        var candidate = Snapshot(
            Production("Closed", "Closed"),
            OwnedTest(
                "Closed.Tests",
                "Closed.Tests",
                "../../Closed/Closed.csproj"),
            Production("Remaining", "remaining"));

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.True(result.IsAccepted, result.Message);
        Assert.True(result.RequiresStrictReduction);
        Assert.Equal(2, result.BaseDebt.Length);
        Assert.Single(result.CandidateDebt);
        Assert.Empty(result.IntroducedDebt);
        Assert.Equal(
            [Debt("missing-owned-project", "Closed", "Closed.Tests")],
            result.RemovedDebt.ToArray());
    }

    [Fact]
    public void EmptyBaseDebtAutomaticallyRejectsAnyHeadDebtWithoutModeSwitch()
    {
        var protectedBase = Snapshot(
            Production("Clean", "Clean"),
            OwnedTest("Clean.Tests", "Clean.Tests", "../../Clean/Clean.csproj"));
        var candidate = Snapshot(
            Production("Clean", "Clean"),
            OwnedTest("Clean.Tests", "Clean.Tests", "../../Clean/Clean.csproj"),
            OwnedTest("Orphan.Tests", "Orphan.Tests"));

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.Empty(result.BaseDebt);
        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("orphan-owned-project", "Orphan.Tests", "Orphan")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void RegisteredCrossCuttingRoleIsExcludedFromOwnership()
    {
        var protectedBase = Snapshot(ProjectWithDefaultProperties(
            CanonicalHarnessPath,
            "StrataLint.ArchitectureTests",
            xunit: true));
        var unchanged = TestProjectTopologyPolicy.Evaluate(protectedBase, protectedBase);

        Assert.True(unchanged.IsAccepted, unchanged.Message);
        Assert.Empty(unchanged.BaseDebt);

        var secondArchitectureProject = Snapshot(
            protectedBase.Projects[0],
            OwnedTest(
                "Second.ArchitectureTests",
                "Second.ArchitectureTests"));
        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, secondArchitectureProject);

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt(
                "orphan-owned-project",
                "Second.ArchitectureTests",
                "Absent")],
            result.IntroducedDebt.ToArray());
    }

    /// <summary>
    /// 脚本测试 harness 与 architecture harness 同类:横跨生产项目、不拥有其中任何一个,
    /// 故不参与 `X` ↔ `X.Tests` 的拥有关系。它按**精确路径**具名排除,与既有 architecture
    /// harness 同一纪律 —— 不改成「凡不叫 X.Tests 者皆横跨」的命名规则,因为那会削弱
    /// `RegisteredCrossCuttingRoleIsExcludedFromOwnership` 有意钉住的守卫:
    /// 任何**未具名**的第三个横跨项目仍须判 orphan 债务。
    /// </summary>
    [Fact]
    public void RegisteredScriptHarnessIsCrossCuttingButOwnedTestStillHasDebt()
    {
        var protectedBase = Snapshot(ProjectWithDefaultProperties(
            "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj",
            "StrataLint.ScriptTests",
            xunit: true));
        var unchanged = TestProjectTopologyPolicy.Evaluate(protectedBase, protectedBase);

        Assert.True(unchanged.IsAccepted, unchanged.Message);
        Assert.Empty(unchanged.BaseDebt);

        var unnamedSecondScriptProject = Snapshot(
            protectedBase.Projects[0],
            OwnedTest("Second.ScriptTests", "Second.ScriptTests"));
        var result = TestProjectTopologyPolicy.Evaluate(
            protectedBase,
            unnamedSecondScriptProject);

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("orphan-owned-project", "Second.ScriptTests", "Absent")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void RegisteredCompileFailProofDoesNotBecomeAnOwnedTestProject()
    {
        var current = Snapshot(
            Production("StrataLint.Engine", "StrataLint.Engine"),
            ProjectWithDefaultProperties(
                "tools/tests/CompileFailProof/CompileFailProof.csproj",
                "StrataLint.CompileFailProof",
                xunit: false,
                "../../StrataLint.Engine/StrataLint.Engine.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(current, current);

        Assert.True(result.IsAccepted, result.Message);
        Assert.Equal(
            [Debt(
                "missing-owned-project",
                "StrataLint.Engine",
                "StrataLint.Engine.Tests")],
            result.BaseDebt.ToArray());
        Assert.DoesNotContain(
            result.BaseDebt,
            static debt => debt.Subject.Contains("CompileFailProof", StringComparison.Ordinal));
    }

    [Fact]
    public void RegisteredCliIdentityOwnsStrataLintTests()
    {
        var current = Snapshot(
            Production("StrataLint.Cli", "StrataLint", projectStem: "StrataLint.Cli"),
            OwnedTest(
                "StrataLint.Tests",
                "StrataLint.Tests",
                "../../StrataLint.Cli/StrataLint.Cli.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(current, current);

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.BaseDebt);
    }

    [Fact]
    public void OwnedPairHasExactlyItsExpectedDirectProductionReference()
    {
        var current = Snapshot(
            Production("Paired", "Paired"),
            OwnedTest(
                "Paired.Tests",
                "Paired.Tests",
                "../../Paired/Paired.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(current, current);

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.BaseDebt);
    }

    [Fact]
    public void RegisteredTestRoleIgnoresXunitPackageSpelling()
    {
        var upperCasePackage = OwnedTest(
            "Literal.Tests",
            "Literal.Tests",
            "../../Literal/Literal.csproj") with
        {
            Content = OwnedTest(
                    "Literal.Tests",
                    "Literal.Tests",
                    "../../Literal/Literal.csproj")
                .Content.Replace("Include=\"xunit\"", "Include=\"XUnit\"", StringComparison.Ordinal),
        };
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(Production("Literal", "Literal"), upperCasePackage));

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.IntroducedDebt);
    }

    [Fact]
    public void RegisteredAssemblyIdentitySurvivesAbsentAssemblyName()
    {
        var production = Production("Fallback", "Fallback") with
        {
            Content = Production("Fallback", "Fallback").Content.Replace(
                "<AssemblyName>Fallback</AssemblyName>",
                string.Empty,
                StringComparison.Ordinal),
        };
        var current = Snapshot(
            production,
            OwnedTest(
                "Fallback.Tests",
                "Fallback.Tests",
                "../../Fallback/Fallback.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(current, current);

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.BaseDebt);
    }

    [Fact]
    public void DuplicateOwnedIdentityDoesNotSatisfyUniqueOwnedProject()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(
                Production("Shared", "Shared"),
                OwnedTest(
                    "First.Tests",
                    "Shared.Tests",
                    "../../Shared/Shared.csproj"),
                OwnedTest(
                    "Second.Tests",
                    "Shared.Tests",
                    "../../Shared/Shared.csproj")));

        Assert.False(result.IsAccepted);
        Assert.Contains(
            Debt("missing-owned-project", "Shared", "Shared.Tests"),
            result.IntroducedDebt);
        Assert.Single(result.IntroducedDebt);
    }

    [Fact]
    public void EveryDebtKindIsCalculatedFromRegisteredTopology()
    {
        var duplicate = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("One", "Shared"),
            Production("Two", "Shared")));
        var missingReference = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("NoRef", "NoRef"),
            OwnedTest("NoRef.Tests", "NoRef.Tests")));
        var orphan = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            OwnedTest("Orphan.Tests", "Orphan.Tests")));
        var extraReference = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest(
                "Alpha.Tests",
                "Alpha.Tests",
                "../../Alpha/Alpha.csproj",
                "../../Beta/Beta.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", "../../Beta/Beta.csproj")));
        var ownedTestReference = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest(
                "Alpha.Tests",
                "Alpha.Tests",
                "../../Alpha/Alpha.csproj",
                "../Beta.Tests/Beta.Tests.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", "../../Beta/Beta.csproj")));

        var kinds = duplicate
            .Concat(missingReference)
            .Concat(orphan)
            .Concat(extraReference)
            .Concat(ownedTestReference)
            .Select(static debt => debt.Kind)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
        [
            "duplicate-production-identity",
            "extra-production-reference",
            "missing-expected-production-reference",
            "missing-owned-project",
            "orphan-owned-project",
            "owned-test-to-owned-test-reference",
        ],
            kinds);
    }

    [Fact]
    public void OwnerAssembliesComeFromOwnedProjectRegistrations()
    {
        var assemblies = TestProjectTopologyPolicy.CalculateOwnerAssemblies(Snapshot(
            OwnedTest("Zulu.Tests", "Zulu.Tests"),
            OwnedTest("Alpha.Tests", "Alpha.Tests"),
            OwnedTest("ZuluDuplicate.Tests", "Zulu.Tests"),
            ProjectWithDefaultProperties(
                CanonicalHarnessPath,
                "StrataLint.ArchitectureTests",
                xunit: true),
            ProjectWithDefaultProperties(
                "tools/tests/CompileFailProof/CompileFailProof.csproj",
                "CompileFailProof",
                xunit: false)));

        Assert.Equal(["Alpha.Tests", "Zulu.Tests"], assemblies.ToArray());
    }

    [Fact]
    public void RegisteredAssemblyIdentityMatchingIsCaseInsensitive()
    {
        var assemblies = TestProjectTopologyPolicy.CalculateOwnerAssemblies(Snapshot(
            Production("CaseInsensitive", "CaseInsensitive"),
            OwnedTest(
                "CaseInsensitive.Tests",
                "caseinsensitive.tests",
                "../../CaseInsensitive/CaseInsensitive.csproj")));

        Assert.Equal(["caseinsensitive.tests"], assemblies.ToArray());
        Assert.Empty(TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("CaseInsensitive", "CaseInsensitive"),
            OwnedTest(
                "CaseInsensitive.Tests",
                "caseinsensitive.tests",
                "../../CaseInsensitive/CaseInsensitive.csproj"))));

        var packageNearMiss = OwnedTest(
                "CaseInsensitiveNearMiss.Tests",
                "caseinsensitive.tests",
                "../../CaseInsensitive/CaseInsensitive.csproj")
            with
            {
                Content = OwnedTest(
                        "CaseInsensitiveNearMiss.Tests",
                        "caseinsensitive.tests",
                        "../../CaseInsensitive/CaseInsensitive.csproj")
                    .Content.Replace(
                        "Include=\"xunit\"",
                        "Include=\"XUnit\"",
                        StringComparison.Ordinal),
            };

        Assert.Equal(["caseinsensitive.tests"], TestProjectTopologyPolicy.CalculateOwnerAssemblies(Snapshot(
            Production("CaseInsensitive", "CaseInsensitive"), packageNearMiss)).ToArray());
    }

    [Fact]
    public void CurrentRepositoryTopologyContainsKnownDebtAndOwnedPairs()
    {
        var root = RepositoryLayout.FindRoot();
        var candidate = TestProjectTopologyPolicy.ReadTrackedProjects(root);
        var debt = TestProjectTopologyPolicy.CalculateDebt(candidate);
        Assert.All(
            debt,
            static debt => Assert.Contains(
                debt.Kind,
                new[]
                {
                    "duplicate-production-identity",
                    "extra-production-reference",
                    "missing-expected-production-reference",
                    "missing-owned-project",
                    "orphan-owned-project",
                    "owned-test-to-owned-test-reference",
                }));
        AssertHasDebtFreePair(candidate, debt);
    }

    [Fact]
    public void CanonicalSolutionIncludesTruthOwnedTestProjectExactlyOnce()
    {
        var solutionLines = File.ReadAllLines(Path.Combine(
            RepositoryLayout.FindRoot(),
            "tools",
            "StrataLint.sln"));
        var matchingProjects = solutionLines.Where(static line => line.StartsWith(
                "Project(",
                StringComparison.Ordinal)
            && line.Contains(
                "\"Trureturing.Truth.Tests\", \"tests\\Trureturing.Truth.Tests\\Trureturing.Truth.Tests.csproj\",",
                StringComparison.Ordinal));

        Assert.Single(matchingProjects);
    }

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
        var role = path == CanonicalHarnessPath || path == "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj"
            ? "cross-cutting-test" : path == "tools/TestSupport/StrataLint.TestSupport/StrataLint.TestSupport.csproj"
            ? "test-support" : path == "tools/tests/CompileFailProof/CompileFailProof.csproj"
            ? "compile-fail-proof" : xunit ? "owned-test" : "production";
        var ownerAssembly = assembly.EndsWith(".Tests", StringComparison.OrdinalIgnoreCase) ? assembly[..^6] : "Absent";
        var ownerPath = references.Select(reference => new Uri(new Uri("https://fixture.invalid/" + path), reference).AbsolutePath.TrimStart('/'))
            .FirstOrDefault(reference => reference.EndsWith("/" + ownerAssembly + ".csproj", StringComparison.OrdinalIgnoreCase))
            ?? (ownerAssembly == "StrataLint" ? "tools/StrataLint.Cli/StrataLint.Cli.csproj" : $"tools/{ownerAssembly}/{ownerAssembly}.csproj");
        var registration = new EngineeringProjectRegistration(path, assembly, role, xunit, [], [],
            references.Select(reference => new Uri(new Uri("https://fixture.invalid/" + path), reference).AbsolutePath.TrimStart('/')).ToArray(),
            role == "owned-test" ? new EngineeringProjectOwner(ownerPath, ownerAssembly) : null,
            role == "production" ? assembly + ".Tests" : null, xunit ? path : null, "Fixture", [], []);
        return new TestProjectTopologyProject(path, content, registration);
    }

    private static TestProjectTopologyDebt Debt(
        string kind,
        string subject,
        string related) => new(kind, subject, related);

    private static void AssertHasDebtFreePair(
        TestProjectTopologySnapshot snapshot,
        IReadOnlyList<TestProjectTopologyDebt> debt)
    {
        var pairs = snapshot.Projects.Where(project => project.Registration.Role == "owned-test")
            .Select(project => (Test: project.Registration.Assembly, Owner: project.Registration.Owner!.Assembly));
        Assert.Contains(pairs, pair => !debt.Any(item =>
            StringComparer.OrdinalIgnoreCase.Equals(item.Subject, pair.Test)
            || StringComparer.OrdinalIgnoreCase.Equals(item.Subject, pair.Owner)
            || StringComparer.OrdinalIgnoreCase.Equals(item.Related, pair.Test)
            || StringComparer.OrdinalIgnoreCase.Equals(item.Related, pair.Owner)));
    }
}
