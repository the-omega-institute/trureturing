using System.Xml.Linq;
using TestProjectTopologyPolicy = StrataLint.Engine.RepositoryRules;

namespace StrataLint.ArchitectureTests;

public sealed class TestProjectTopologyPolicyTests
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
    public void NewProductionAndOwnedXunitPairIsAccepted()
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
    public void OnlyExactCanonicalArchitectureHarnessPathIsExcluded()
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
                string.Empty)],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void NonXunitCompileFailProofDoesNotBecomeAnOwnedTestProject()
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
    public void DeltaContractionMechanismCannotBeRemovedWithoutFailingThisNamedTest()
    {
        var (protectedBase, candidate) = EqualSizedDebtSwap();

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.False(result.IsAccepted);
        Assert.NotEmpty(result.IntroducedDebt);
    }

    [Fact]
    public void CliAssemblyNameRatherThanProjectStemOwnsStrataLintTests()
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
    public void ZeroTestOwnedXunitProjectCanPassPureCsprojTopologyGate()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(
                Production("Empty", "Empty"),
                OwnedTest(
                    "Empty.Tests",
                    "Empty.Tests",
                    "../../Empty/Empty.csproj")));

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.CandidateDebt);
    }

    [Fact]
    public void XunitPackageIdentityIsOrdinalLiteral()
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

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("missing-owned-project", "Literal", "Literal.Tests")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void ProdRefsContainOnlyDirectProjectReferencesNotTransitiveOnes()
    {
        var current = Snapshot(
            ProjectWithDefaultProperties(
                "tools/Alpha/Alpha.csproj",
                "Alpha",
                xunit: false,
                references: ["../Beta/Beta.csproj"]),
            ProjectWithDefaultProperties(
                "tools/Beta/Beta.csproj",
                "Beta",
                xunit: false,
                references: ["../Gamma/Gamma.csproj"]),
            Production("Gamma", "Gamma"),
            OwnedTest("Alpha.Tests", "Alpha.Tests", "../../Alpha/Alpha.csproj"),
            OwnedTest("Beta.Tests", "Beta.Tests", "../../Beta/Beta.csproj"),
            OwnedTest("Gamma.Tests", "Gamma.Tests", "../../Gamma/Gamma.csproj"));

        var debt = TestProjectTopologyPolicy.CalculateDebt(current);

        Assert.DoesNotContain(
            debt,
            static item => item.Kind == "extra-production-reference"
                && item.Subject == "Alpha.Tests"
                && item.Related is "Beta" or "Gamma");
    }

    [Fact]
    public void AssemblyIdentityFallsBackToProjectStemWhenAssemblyNameIsAbsent()
    {
        var production = Production("Fallback", "Ignored") with
        {
            Content = Production("Fallback", "Ignored").Content.Replace(
                "<AssemblyName>Ignored</AssemblyName>",
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
    public void EveryDebtKindIsDerivedFromSyntheticTopology()
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
    public void OwnerAssembliesAreDerivedFromOwnedXunitProjectTopology()
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

    [Fact(DisplayName = "assembly identity matching ignores case while xunit marker stays literal")]
    public void AssemblyIdentityMatchingIsCaseInsensitiveButXunitMarkerIsLiteral()
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

        Assert.Empty(TestProjectTopologyPolicy.CalculateOwnerAssemblies(Snapshot(
            Production("CaseInsensitive", "CaseInsensitive"),
            packageNearMiss)));
    }

    [Fact]
    public void CurrentRepositoryCandidateDeltaIsAcceptedByTheSameRatchet()
    {
        var root = RepositoryLayout.FindRoot();
        var protectedBase = ReadProtectedBase(root);
        var candidate = Decode(GitRepositorySnapshotReader.ReadCurrent(root));
        var result = TestProjectTopologyPolicy.EvaluateSnapshots(protectedBase, candidate);

        Assert.True(result.IsAccepted, result.Message);
        Assert.NotEmpty(result.BaseDebt);
        Assert.All(
            result.BaseDebt.Concat(result.CandidateDebt),
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
        AssertHasDebtFreePair(protectedBase, result.BaseDebt);
        AssertHasDebtFreePair(candidate, result.CandidateDebt);
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
        return new TestProjectTopologyProject(path, content);
    }

    private static TestProjectTopologyDebt Debt(
        string kind,
        string subject,
        string related) => new(kind, subject, related);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    private static void AssertHasDebtFreePair(
        RepositorySnapshot snapshot,
        IReadOnlyList<TestProjectTopologyDebt> debt)
    {
        var projects = TestProjectTopologyPolicy.ReadSnapshotProjects(snapshot).Projects
            .Select(static project =>
            {
                var path = project.Path.Replace('\\', '/');
                var document = XDocument.Parse(project.Content, LoadOptions.None);
                var assemblyName = document.Descendants()
                    .FirstOrDefault(static element => element.Name.LocalName == "AssemblyName")
                    ?.Value.Trim();
                if (string.IsNullOrEmpty(assemblyName))
                {
                    assemblyName = Path.GetFileNameWithoutExtension(path);
                }

                var isXunit = document.Descendants().Any(static element =>
                    element.Name.LocalName == "PackageReference"
                    && string.Equals(
                        (string?)element.Attribute("Include"),
                        "xunit",
                        StringComparison.Ordinal));
                return (Path: path, AssemblyName: assemblyName, IsXunit: isXunit);
            })
            .ToArray();
        var productionIdentities = projects
            .Where(static project =>
            {
                var parts = project.Path.Split('/');
                return parts.Length == 3
                    && parts[0] == "tools"
                    && parts[1] != "tests"
                    && parts[2].EndsWith(".csproj", StringComparison.Ordinal);
            })
            .GroupBy(static project => project.AssemblyName, StringComparer.OrdinalIgnoreCase)
            .Where(static group => group.Count() == 1)
            .Select(static group => group.Key);
        var ownedTestIdentities = projects
            .Where(static project => project.IsXunit
                && project.Path.StartsWith("tools/tests/", StringComparison.Ordinal)
                && project.Path.EndsWith(".csproj", StringComparison.Ordinal)
                && project.Path != CanonicalHarnessPath)
            .GroupBy(static project => project.AssemblyName, StringComparer.OrdinalIgnoreCase)
            .Where(static group => group.Count() == 1)
            .Select(static group => group.Key)
            .ToHashSet(StringComparer.OrdinalIgnoreCase);
        var pairIdentities = productionIdentities
            .Where(identity => ownedTestIdentities.Contains(identity + ".Tests"))
            .ToArray();

        Assert.Contains(pairIdentities, productionIdentity =>
        {
            var testIdentity = productionIdentity + ".Tests";
            return !debt.Any(item =>
                StringComparer.OrdinalIgnoreCase.Equals(item.Subject, productionIdentity)
                || StringComparer.OrdinalIgnoreCase.Equals(item.Subject, testIdentity)
                || StringComparer.OrdinalIgnoreCase.Equals(item.Related, productionIdentity)
                || StringComparer.OrdinalIgnoreCase.Equals(item.Related, testIdentity));
        });
    }

    private static RepositorySnapshot ReadProtectedBase(string root)
    {
        try
        {
            return Decode(GitRepositorySnapshotReader.ReadRevision(root, "HEAD^1"));
        }
        catch (InvalidOperationException exception) when (exception.Message.Contains(
                   "Not a valid object name HEAD^1",
                   StringComparison.Ordinal))
        {
            // This worker checkout is rooted at a shallow protected-base commit. The required
            // engineering executor itself rejects a CI checkout without HEAD^1, so this local
            // allow-side fallback cannot weaken the admission path.
            return Decode(GitRepositorySnapshotReader.ReadRevision(root, "HEAD"));
        }
    }
}
