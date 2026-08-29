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
    public void NewProductionAndOwnedRunnableXunitPairIsAccepted()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(
                Production("NewProduct", "NewProduct"),
                OwnedTest(
                    "NewProduct.Tests",
                    "NewProduct.Tests",
                    runnable: true,
                    "../../NewProduct/NewProduct.csproj")));

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.CandidateDebt);
    }

    [Fact]
    public void OwnedTestWithSecondProductionReferenceIsRejected()
    {
        var protectedBase = Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest("Alpha.Tests", "Alpha.Tests", true, "../../Alpha/Alpha.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", true, "../../Beta/Beta.csproj"));
        var candidate = Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest(
                "Alpha.Tests",
                "Alpha.Tests",
                runnable: true,
                "../../Alpha/Alpha.csproj",
                "../../Beta/Beta.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", true, "../../Beta/Beta.csproj"));

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
            OwnedTest("Clean.Tests", "Clean.Tests", true, "../../Clean/Clean.csproj"));
        var candidate = Snapshot(
            Production("Legacy", "Legacy"),
            Production(
                "Clean",
                "Clean",
                extraProperty: "<Description>clean edit</Description>"),
            OwnedTest("Clean.Tests", "Clean.Tests", true, "../../Clean/Clean.csproj"));

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
                runnable: true,
                "../../Legacy/Legacy.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(protectedBase, candidate);

        Assert.True(result.IsAccepted, result.Message);
        Assert.True(result.RequiresStrictReduction);
        Assert.Single(result.BaseDebt);
        Assert.Empty(result.CandidateDebt);
    }

    [Fact]
    public void EmptyBaseDebtAutomaticallyRejectsAnyHeadDebtWithoutModeSwitch()
    {
        var protectedBase = Snapshot(
            Production("Clean", "Clean"),
            OwnedTest("Clean.Tests", "Clean.Tests", true, "../../Clean/Clean.csproj"));
        var candidate = Snapshot(
            Production("Clean", "Clean"),
            OwnedTest("Clean.Tests", "Clean.Tests", true, "../../Clean/Clean.csproj"),
            OwnedTest("Orphan.Tests", "Orphan.Tests", runnable: true));

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
        var protectedBase = Snapshot(Project(
            CanonicalHarnessPath,
            "StrataLint.ArchitectureTests",
            xunit: true,
            runnable: false));
        var unchanged = TestProjectTopologyPolicy.Evaluate(protectedBase, protectedBase);

        Assert.True(unchanged.IsAccepted, unchanged.Message);
        Assert.Empty(unchanged.BaseDebt);

        var secondArchitectureProject = Snapshot(
            protectedBase.Projects[0],
            OwnedTest(
                "Second.ArchitectureTests",
                "Second.ArchitectureTests",
                runnable: true));
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
            Project(
                "tools/tests/CompileFailProof/CompileFailProof.csproj",
                "StrataLint.CompileFailProof",
                xunit: false,
                runnable: false,
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
                runnable: true,
                "../../StrataLint.Cli/StrataLint.Cli.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(current, current);

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.BaseDebt);
    }

    [Fact]
    public void ScribePairHasExactlyItsExpectedDirectProductionReference()
    {
        var current = Snapshot(
            Production("StrataLint.Scribe", "StrataLint.Scribe"),
            OwnedTest(
                "StrataLint.Scribe.Tests",
                "StrataLint.Scribe.Tests",
                runnable: true,
                "../../StrataLint.Scribe/StrataLint.Scribe.csproj"));

        var result = TestProjectTopologyPolicy.Evaluate(current, current);

        Assert.True(result.IsAccepted, result.Message);
        Assert.Empty(result.BaseDebt);
    }

    [Fact]
    public void OwnedXunitProjectWithoutRunnableTestIdentityIsRejected()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(
                Production("Empty", "Empty"),
                OwnedTest(
                    "Empty.Tests",
                    "Empty.Tests",
                    runnable: false,
                    "../../Empty/Empty.csproj")));

        Assert.False(result.IsAccepted);
        Assert.Equal(
            [Debt("missing-owned-project", "Empty", "Empty.Tests")],
            result.IntroducedDebt.ToArray());
    }

    [Fact]
    public void DuplicateOwnedIdentityCannotHideBehindOneRunnableProject()
    {
        var result = TestProjectTopologyPolicy.Evaluate(
            Snapshot(),
            Snapshot(
                Production("Shared", "Shared"),
                OwnedTest(
                    "First.Tests",
                    "Shared.Tests",
                    runnable: true,
                    "../../Shared/Shared.csproj"),
                OwnedTest(
                    "Second.Tests",
                    "Shared.Tests",
                    runnable: false,
                    "../../Shared/Shared.csproj")));

        Assert.False(result.IsAccepted);
        Assert.Contains(
            Debt("missing-owned-project", "Shared", "Shared.Tests"),
            result.IntroducedDebt);
    }

    [Fact]
    public void EveryDebtKindIsDerivedFromSyntheticTopology()
    {
        var duplicate = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("One", "Shared"),
            Production("Two", "Shared")));
        var missingReference = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("NoRef", "NoRef"),
            OwnedTest("NoRef.Tests", "NoRef.Tests", runnable: true)));
        var orphan = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            OwnedTest("Orphan.Tests", "Orphan.Tests", runnable: true)));
        var extraReference = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest(
                "Alpha.Tests",
                "Alpha.Tests",
                runnable: true,
                "../../Alpha/Alpha.csproj",
                "../../Beta/Beta.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", true, "../../Beta/Beta.csproj")));
        var ownedTestReference = TestProjectTopologyPolicy.CalculateDebt(Snapshot(
            Production("Alpha", "Alpha"),
            OwnedTest(
                "Alpha.Tests",
                "Alpha.Tests",
                runnable: true,
                "../../Alpha/Alpha.csproj",
                "../Beta.Tests/Beta.Tests.csproj"),
            Production("Beta", "Beta"),
            OwnedTest("Beta.Tests", "Beta.Tests", true, "../../Beta/Beta.csproj")));

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
    public void CurrentRepositoryCandidateDeltaIsAcceptedByTheSameRatchet()
    {
        var root = RepositoryLayout.FindRoot();
        var protectedBase = ReadProtectedBase(root);
        var candidate = Decode(GitRepositorySnapshotReader.ReadCurrent(root));
        var protectedBaseMap = ScribeTestMapDeriver.DeriveSnapshot(protectedBase);
        var candidateMap = ScribeTestMapDeriver.DeriveSnapshot(candidate);
        var protectedBaseTopology = TestProjectTopologyPolicy.ReadSnapshotProjects(
            protectedBase,
            RunnableProjects(protectedBaseMap));
        var candidateTopology = TestProjectTopologyPolicy.ReadSnapshotProjects(
            candidate,
            RunnableProjects(candidateMap));

        var result = TestProjectTopologyPolicy.Evaluate(
            protectedBaseTopology,
            candidateTopology);

        Assert.True(result.IsAccepted, result.Message);
    }

    private static (TestProjectTopologySnapshot ProtectedBase, TestProjectTopologySnapshot Candidate)
        EqualSizedDebtSwap()
    {
        var protectedBase = Snapshot(
            Production("Legacy", "Legacy"),
            OwnedTest(
                "Legacy.Tests",
                "Legacy.Tests",
                runnable: false,
                "../../Legacy/Legacy.csproj"));
        var candidate = Snapshot(
            Production("Legacy", "Legacy"),
            OwnedTest(
                "Legacy.Tests",
                "Legacy.Tests",
                runnable: true,
                "../../Legacy/Legacy.csproj"),
            OwnedTest("Rogue.Tests", "Rogue.Tests", runnable: true));
        return (protectedBase, candidate);
    }

    private static TestProjectTopologySnapshot Snapshot(
        params TestProjectTopologyProject[] projects) => new(projects);

    private static TestProjectTopologyProject Production(
        string directory,
        string assembly,
        string? projectStem = null,
        string extraProperty = "") => Project(
        $"tools/{directory}/{projectStem ?? directory}.csproj",
        assembly,
        xunit: false,
        runnable: false,
        extraProperty: extraProperty);

    private static TestProjectTopologyProject OwnedTest(
        string directory,
        string assembly,
        bool runnable,
        params string[] references) => Project(
        $"tools/tests/{directory}/{directory}.csproj",
        assembly,
        xunit: true,
        runnable: runnable,
        references: references);

    private static TestProjectTopologyProject Project(
        string path,
        string assembly,
        bool xunit,
        bool runnable,
        params string[] references) => Project(
        path,
        assembly,
        xunit,
        runnable,
        extraProperty: string.Empty,
        references);

    private static TestProjectTopologyProject Project(
        string path,
        string assembly,
        bool xunit,
        bool runnable,
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
        return new TestProjectTopologyProject(path, content, runnable);
    }

    private static TestProjectTopologyDebt Debt(
        string kind,
        string subject,
        string related) => new(kind, subject, related);

    private static IReadOnlySet<string> RunnableProjects(ScribeTestMap map) => map.Methods
        .Where(static method => !method.IsStaticallySkipped)
        .Select(method => map.CompileProjectBySourcePath[method.SourcePath])
        .ToHashSet(StringComparer.Ordinal);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

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
