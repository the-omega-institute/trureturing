using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class ScribeTestMapDeriverTests
{
    private const string SdkProject = "<Project Sdk=\"Microsoft.NET.Sdk\" />";

    private static readonly IReadOnlySet<string> CompileFailProofProjectExemptionRemovalOnlyBaseline =
        new HashSet<string>(StringComparer.Ordinal)
        {
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            "tools/tests/CompileFailProof/CompileFailProof.csproj",
        };

    [Fact]
    public void RepositoryMapHasNoUnknownGrowthAndEveryPathIsDeclared()
    {
        var map = ScribeTestMapDeriver.DeriveRepository(RepositoryLayout.FindRoot());

        Assert.Equal(280, ScribeUnknownDebtPolicy.UnknownDebtLimit);
        Assert.Equal(281, ScribeUnknownDebtPolicy.UnknownDebtToleranceLimit);
        Assert.Empty(ScribeUnknownDebtPolicy.InspectCurrent(map));
        var retiredLedgerMethod = Assert.Single(
            map.Methods,
            static method => method.Id ==
                "TruthExportCommandTests.ExportEqualsStrictActiveSetDroppingRevokedNodes");
        Assert.False(
            retiredLedgerMethod.IsUnknown,
            $"{retiredLedgerMethod.Id}: {string.Join(',', retiredLedgerMethod.UnknownReasons)}");
        Assert.All(
            map.Methods.SelectMany(static method => method.Paths),
            path => Assert.True(
                ScribeTestMapDeriver.IsDeclaredPathAllowed(path),
                $"undeclared repository read path: {path}"));
    }

    [Fact]
    public void BlueprintScribeDefinitionsAreAttributedToStrataLintScribeByMsBuildCompileItems()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var map = ScribeTestMapDeriver.DeriveRepository(repositoryRoot);
        var blueprint = map.CompileProjectBySourcePath
            .Where(static pair => pair.Key.StartsWith("Blueprint/", StringComparison.Ordinal)
                && pair.Key.EndsWith(".scribe.cs", StringComparison.Ordinal))
            .OrderBy(static pair => pair.Key, StringComparer.Ordinal)
            .ToArray();
        var tracked = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Select(static file => file.RelativePath)
            .Where(static path => path.StartsWith("Blueprint/", StringComparison.Ordinal)
                && path.EndsWith(".scribe.cs", StringComparison.Ordinal))
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(tracked, blueprint.Select(static pair => pair.Key));
        Assert.All(
            blueprint,
            pair => Assert.Equal(
                "tools/StrataLint.Scribe/StrataLint.Scribe.csproj",
                pair.Value));
    }

    [Fact]
    public void CrossDirectoryCompileOwnershipIsAdmittedWithoutFinding()
    {
        var snapshot = Snapshot(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject),
            ("src/App/App.csproj", """
                <Project Sdk="Microsoft.NET.Sdk">
                  <ItemGroup><Compile Include="../../shared/**/*.cs" /></ItemGroup>
                </Project>
                """),
            ("shared/Linked.cs", "class Linked { }"));

        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot);

        Assert.True(map.CompileProjectBySourcePath.TryGetValue("shared/Linked.cs", out var owner));
        Assert.Equal("src/App/App.csproj", owner);
        Assert.Empty(ScribeUnknownDebtPolicy.InspectCurrent(map));
    }

    [Fact]
    public void AmbiguousCompileOwnershipProducesBlockingFinding()
    {
        const string linkedProject = """
            <Project Sdk="Microsoft.NET.Sdk">
              <ItemGroup><Compile Include="../../shared/**/*.cs" /></ItemGroup>
            </Project>
            """;
        using var repository = CreateTrackedRepository(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject),
            ("src/A/A.csproj", linkedProject),
            ("src/B/B.csproj", linkedProject),
            ("shared/Linked.cs", "class Linked { }"));

        var finding = Assert.Single(
            ScribeUnknownDebtPolicy.InspectCurrent(
                ScribeTestMapDeriver.DeriveRepository(repository.Path)),
            static candidate => candidate.Path == "shared/Linked.cs");

        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Contains("ambiguous", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void FullRepositoryOrphanCheckRejectsSourceAbsentFromCompileItems()
    {
        var snapshot = ManagedSnapshot(
            ("Blueprint/D5/S0/Sample.scribe.cs", "class SampleDefinition { }"));

        var finding = Assert.Single(ScribeUnknownDebtPolicy.InspectCurrent(
            ScribeTestMapDeriver.DeriveSnapshot(snapshot)));

        Assert.Equal("Blueprint/D5/S0/Sample.scribe.cs", finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Contains("MSBuild Compile items", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MsBuildCompileQueryFailureProducesBlockingFinding()
    {
        using var repository = CreateTrackedRepository(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject));

        var map = ScribeTestMapDeriver.DeriveRepository(
            repository.Path,
            Path.Combine(repository.Path, "missing-dotnet"));
        var finding = Assert.Single(
            map.CompileQueryFindings,
            static candidate => candidate.Path.EndsWith(
                "BannedApiCompileFailProof.csproj",
                StringComparison.Ordinal));

        Assert.All(
            map.CompileQueryFindings,
            static candidate => Assert.Contains("failed closed", candidate.Message, StringComparison.Ordinal));
        Assert.Contains(
            ScribeUnknownDebtPolicy.InspectCurrent(map),
            candidate => candidate.Path == finding.Path
                && candidate.Effect == AdmissionEffect.Block);
    }

    [Fact]
    public void MsBuildCompileQueryFailureDoesNotProduceOrphanFindings()
    {
        const string sourcePath = "tools/tests/CompileFailProof/MissingCapability.cs";
        using var repository = CreateTrackedRepository(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject),
            (sourcePath, "class MissingCapability { }"));

        var map = ScribeTestMapDeriver.DeriveRepository(
            repository.Path,
            Path.Combine(repository.Path, "missing-dotnet"));
        var findings = ScribeUnknownDebtPolicy.InspectCurrent(map);

        Assert.NotEmpty(map.CompileQueryFindings);
        Assert.Contains(findings, static finding => finding.Message.Contains(
            "MSBuild Compile query failed closed",
            StringComparison.Ordinal));
        Assert.DoesNotContain(sourcePath, map.OrphanManagedSourcePaths);
        Assert.DoesNotContain(findings, finding => finding.Path == sourcePath);
    }

    [Fact]
    public void MsBuildCompileQueryTimeoutProducesBlockingFinding()
    {
        using var repository = CreateTrackedRepository(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject));

        var map = ScribeTestMapDeriver.DeriveRepository(
            repository.Path,
            timeout: TestBudgets.ZeroDuration);
        var finding = Assert.Single(map.CompileQueryFindings);

        Assert.Contains("timed out", finding.Message, StringComparison.Ordinal);
        Assert.Contains(
            ScribeUnknownDebtPolicy.InspectCurrent(map),
            candidate => candidate.Path == finding.Path
                && candidate.Effect == AdmissionEffect.Block);
    }

    [Fact]
    public void UnknownDebtPartitionsAreDerivedFromXunitProjectInputs()
    {
        const string xunitProject =
            "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>";
        const string compileProof = "<Project Sdk=\"Microsoft.NET.Sdk\" />";

        var partitions = ScribeTestMapDeriver.DeriveProjectPartitions(
        [
            ("tools/tests/Alpha.Tests/Alpha.Tests.csproj", xunitProject),
            ("tools/tests/NewPartition.Tests/NewPartition.Tests.csproj", xunitProject),
            ("tools/tests/CompileProof/CompileProof.csproj", compileProof),
        ]);

        Assert.Equal(
            ["tools/tests/Alpha.Tests", "tools/tests/NewPartition.Tests"],
            partitions.Select(static partition => partition.Key));
    }

    [Fact]
    public void EvaluateRejectsManagedProjectWithoutDirectXunitReference()
    {
        var snapshot = ManagedSnapshot(
            ("tools/tests/Missing.Tests/Missing.Tests.csproj", SdkProject),
            ("tools/tests/Missing.Tests/DebtTests.cs", UnknownSource("DebtTests", "ReadsVariable")));

        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot);
        var finding = Assert.Single(ScribeUnknownDebtPolicy.Evaluate(map, map));
        var inspectionFinding = Assert.Single(ScribeUnknownDebtPolicy.InspectCurrent(map));

        Assert.Empty(map.Methods);
        Assert.Equal(finding, inspectionFinding);
        Assert.Equal("tools/tests/Missing.Tests/Missing.Tests.csproj", finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Contains("neither", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredCompileFailProofProjectsAreAdmittedWithoutFinding()
    {
        var snapshot = Snapshot(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject));

        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot);

        Assert.Empty(ScribeUnknownDebtPolicy.Evaluate(map, map));
    }

    [Fact]
    public void CompileFailProofProjectExemptionBaselineAllowsOnlyRemoval()
    {
        Assert.Empty(ScribeTestMapDeriver.CompileFailProofProjectExemptions
            .Except(CompileFailProofProjectExemptionRemovalOnlyBaseline, StringComparer.Ordinal));
        Assert.Equal(
            ["tools/tests/NewCompileFailProof/NewCompileFailProof.csproj"],
            ScribeTestMapDeriver.CompileFailProofProjectExemptions
                .Append("tools/tests/NewCompileFailProof/NewCompileFailProof.csproj")
                .Except(CompileFailProofProjectExemptionRemovalOnlyBaseline, StringComparer.Ordinal));
    }

    [Fact]
    public void EvaluateRejectsManagedSourceWithoutAnyProject()
    {
        var snapshot = ManagedSnapshot(
            ("tools/tests/Missing.Tests/DebtTests.cs", UnknownSource("DebtTests", "ReadsVariable")));

        var map = ScribeTestMapDeriver.DeriveSnapshot(snapshot);
        var finding = Assert.Single(ScribeUnknownDebtPolicy.InspectCurrent(map));

        Assert.Empty(map.Methods);
        Assert.Equal("tools/tests/Missing.Tests/DebtTests.cs", finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Contains("absent from every tracked project", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EvaluateRejectsDanglingCompileFailProofProjectExemption()
    {
        var snapshot = Snapshot(
            ("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", "class BannedApiViolations { }"),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/MissingCapability.cs", "class MissingCapability { }"));

        var findings = ScribeUnknownDebtPolicy.InspectCurrent(
            ScribeTestMapDeriver.DeriveSnapshot(snapshot));
        var finding = Assert.Single(findings, static candidate =>
            candidate.Message.Contains("declared compile-fail proof exemption", StringComparison.Ordinal));

        Assert.Equal(
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
    }

    [Fact]
    public void DeriveRepositoryPropagatesUnclassifiedManagedProjectsToBlockingFindings()
    {
        using var repository = CreateTrackedRepository(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject),
            ("tools/tests/Missing.Tests/Missing.Tests.csproj", SdkProject),
            ("tools/tests/Missing.Tests/DebtTests.cs", UnknownSource("DebtTests", "ReadsVariable")));

        var map = ScribeTestMapDeriver.DeriveRepository(repository.Path);
        var finding = Assert.Single(ScribeUnknownDebtPolicy.InspectCurrent(map));

        Assert.Equal("tools/tests/Missing.Tests/Missing.Tests.csproj", finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
    }

    [Fact]
    public void DeriveRepositoryPropagatesOrphanManagedSourcesToBlockingFindings()
    {
        using var repository = CreateTrackedRepository(
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject),
            ("tools/tests/Missing.Tests/DebtTests.cs", UnknownSource("DebtTests", "ReadsVariable")));

        var map = ScribeTestMapDeriver.DeriveRepository(repository.Path);
        var finding = Assert.Single(ScribeUnknownDebtPolicy.InspectCurrent(map));

        Assert.Equal("tools/tests/Missing.Tests/DebtTests.cs", finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
    }

    [Fact]
    public void DeriveRepositoryPropagatesDanglingCompileFailProofExemptionsToBlockingFindings()
    {
        using var repository = CreateTrackedRepository(
            ("tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs", "class BannedApiViolations { }"),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject));

        var findings = ScribeUnknownDebtPolicy.InspectCurrent(
            ScribeTestMapDeriver.DeriveRepository(repository.Path));
        var finding = Assert.Single(findings, static candidate =>
            candidate.Message.Contains("declared compile-fail proof exemption", StringComparison.Ordinal));

        Assert.Equal(
            "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj",
            finding.Path);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
    }

    [Fact]
    public void RepositoryMapHasNoDanglingCompileFailProofProjectExemptions()
    {
        var findings = ScribeUnknownDebtPolicy
            .InspectCurrent(ScribeTestMapDeriver.DeriveRepository(RepositoryLayout.FindRoot()))
            .Where(static finding => finding.Message.Contains(
                "declared compile-fail proof exemption",
                StringComparison.Ordinal));

        Assert.Empty(findings);
    }

    [Fact]
    public void DeriveSnapshotDiscoversXunitProjectsAcrossTheWholeRepository()
    {
        const string xunitProject =
            "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup><PackageReference Include=\"xunit\" /></ItemGroup></Project>";
        var snapshot = Snapshot(
            ("experiments/External.Tests/External.Tests.csproj", xunitProject),
            ("experiments/External.Tests/ExternalTests.cs", "class ExternalTests { [Fact] public void Runs() { } }"));

        var method = Assert.Single(ScribeTestMapDeriver.DeriveSnapshot(snapshot).Methods);

        Assert.Equal("experiments/External.Tests", method.PartitionKey);
        Assert.Equal("experiments/External.Tests/ExternalTests.cs", method.SourcePath);
    }

    [Fact]
    public void UnknownDebtBaselineSchemaV1GroupsMethodsByDerivedPartitionKey()
    {
        const string source = """
            class DebtTests {
              [Fact] public void ReadsVariable() {
                var path = GetPath();
                File.ReadAllText(path);
              }
            }
            """;
        var map = ScribeTestMapDeriver.DeriveSources(
        [
            new("tools/tests/Alpha.Tests/DebtTests.cs", source, "tools/tests/Alpha.Tests"),
            new("tools/tests/Beta.Tests/DebtTests.cs", source, "tools/tests/Beta.Tests"),
        ],
        []);

        var baseline = ScribeUnknownDebtBaselineV1.Create(map);

        Assert.Equal(ScribeUnknownDebtBaselineV1.CurrentSchemaVersion, baseline.SchemaVersion);
        Assert.Equal(2, baseline.UnknownCount);
        Assert.Equal(
            ["tools/tests/Alpha.Tests", "tools/tests/Beta.Tests"],
            baseline.Partitions.Keys);
    }

    [Fact]
    public void UnknownDebtPastToleranceIsDetectedRepositoryWide()
    {
        var methods = string.Join('\n', Enumerable.Range(
                0,
                ScribeUnknownDebtPolicy.UnknownDebtToleranceLimit + 1)
            .Select(static index =>
                $"[Fact] public void Debt{index:000}() {{ var path = GetPath(); File.ReadAllText(path); }}"));
        var map = ScribeTestMapDeriver.DeriveSources(
        [
            new(
                "tools/tests/Synthetic.Tests/DebtTests.cs",
                $"class DebtTests {{\n{methods}\n}}",
                "tools/tests/Synthetic.Tests"),
        ],
        []);

        var finding = Assert.Single(ScribeUnknownDebtPolicy.InspectCurrent(map));

        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Contains("repository tolerance 281", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnknownDebtIdentityIncludesPartitionKey()
    {
        var forkPoint = UnknownMap(
            "tools/tests/Alpha.Tests",
            "tools/tests/Shared/DebtTests.cs",
            "DebtTests",
            "ReadsVariable");
        var current = UnknownMap(
            "tools/tests/Beta.Tests",
            "tools/tests/Shared/DebtTests.cs",
            "DebtTests",
            "ReadsVariable");

        AssertIntroducedUnknown(current, forkPoint, "tools/tests/Beta.Tests::DebtTests.ReadsVariable");
    }

    [Fact]
    public void UnknownDebtIdentityIncludesSourcePath()
    {
        var forkPoint = UnknownMap(
            "tools/tests/Alpha.Tests",
            "tools/tests/Alpha.Tests/PreviousDebtTests.cs",
            "DebtTests",
            "ReadsVariable");
        var current = UnknownMap(
            "tools/tests/Alpha.Tests",
            "tools/tests/Alpha.Tests/CurrentDebtTests.cs",
            "DebtTests",
            "ReadsVariable");

        AssertIntroducedUnknown(current, forkPoint, "tools/tests/Alpha.Tests::DebtTests.ReadsVariable");
    }

    [Fact]
    public void UnknownDebtIdentityIncludesTypeAndMethod()
    {
        var forkPoint = UnknownMap(
            "tools/tests/Alpha.Tests",
            "tools/tests/Alpha.Tests/DebtTests.cs",
            "PreviousDebtTests",
            "ReadsVariable");
        var current = UnknownMap(
            "tools/tests/Alpha.Tests",
            "tools/tests/Alpha.Tests/DebtTests.cs",
            "CurrentDebtTests",
            "ReadsVariable");

        AssertIntroducedUnknown(current, forkPoint, "tools/tests/Alpha.Tests::CurrentDebtTests.ReadsVariable");
    }

    [Fact]
    public void UnknownDebtAtToleranceWithoutIntroductionIsObserved()
    {
        var methods = string.Join('\n', Enumerable.Range(
                0,
                ScribeUnknownDebtPolicy.UnknownDebtToleranceLimit)
            .Select(static index =>
                $"[Fact] public void Debt{index:000}() {{ var path = GetPath(); File.ReadAllText(path); }}"));
        var map = ScribeTestMapDeriver.DeriveSources(
        [
            new(
                "tools/tests/Synthetic.Tests/DebtTests.cs",
                $"class DebtTests {{\n{methods}\n}}",
                "tools/tests/Synthetic.Tests"),
        ],
        []);

        var finding = Assert.Single(ScribeUnknownDebtPolicy.Evaluate(map, map));

        Assert.Equal(AdmissionEffect.Observe, finding.Effect);
        Assert.Contains("this change introduced none", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DiscoveryMarkerFollowsRepositoryAccessorSource()
    {
        var map = DeriveDiscoveryWithAccessorMarker("File.Exists(Path.Combine(root, \"PROJECT.md\"))");

        Assert.Equal(["PROJECT.md"], Assert.Single(map.Methods).Paths);
    }

    [Fact]
    public void UnparseableDiscoveryMarkerIsUnknown()
    {
        var map = DeriveDiscoveryWithAccessorMarker("File.Exists(Path.Combine(root, markerPath))");

        var method = Assert.Single(map.Methods);
        Assert.True(method.IsUnknown);
    }

    [Fact]
    public void SensitivityFollowsRepositoryPathLiteralInSource()
    {
        var first = Derive("Golden/one.json");
        var second = Derive("Golden/two.json");

        Assert.Equal(["CLAUDE.md", "Golden/one.json"], first.Methods.Single().Paths);
        Assert.Equal(["CLAUDE.md", "Golden/two.json"], second.Methods.Single().Paths);
    }

    [Fact]
    public void VariablePathIsUnknown()
    {
        const string source = """
            class VariableTests {
              [Fact] public void ReadsVariable() {
                var path = GetPath();
                RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                  .ReadAllText(RepositoryRelativePath.Create(path));
              }
              private string GetPath() => "CLAUDE.md";
            }
            """;

        var map = DeriveSources([new("VariableTests.cs", source)]);

        var method = Assert.Single(map.Methods);
        Assert.Equal(TestMapUnknownReason.VariablePath, Assert.Single(method.UnknownReasons));
    }

    [Fact]
    public void RepositoryLayoutCombineDerivesItsLiteralPath()
    {
        const string source = """
            class WorkflowTests {
              [Fact] public void ReadsWorkflow() => File.ReadAllText(
                Path.Combine(RepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));
            }
            """;

        var map = DeriveSources([new("WorkflowTests.cs", source)]);

        var method = Assert.Single(map.Methods);
        Assert.Equal([".github/workflows/ci.yml"], method.Paths);
        Assert.False(method.IsUnknown);
    }

    [Fact]
    public void DiscoveryDirectoryContributesBothMarkersToPaths()
    {
        const string source = """
            class DirectoryTests {
              [Fact] public void Discovers() => RepositoryAccessor.Discover(RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);
            }
            """;
        var map = DeriveSources([new("DirectoryTests.cs", source)]);

        Assert.Equal(["Blueprint", "global.json"], Assert.Single(map.Methods).Paths);
    }

    [Fact]
    public void ReachableHelpersContributePathsAndUnknownReasons()
    {
        const string source = """
            class SampleTests {
              [Fact] public void A() => Read("A.json");
              [Fact] public void B() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).ReadAllBytes(RepositoryRelativePath.Create("B.json"));
              [Theory] public void C() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).FileExists(RepositoryRelativePath.Create("C.json"));
              [Fact] public void D() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).CopyTo(RepositoryRelativePath.Create("D.json"), null);
              [Fact] public void E() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).EnumerateFiles(RepositoryRelativePath.Create("E"), "*.json");
              private void Read(string ignored) => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).ReadAllText(RepositoryRelativePath.Create("A.json"));
            }
            """;

        var map = DeriveSources([new("SampleTests.cs", source)]);

        Assert.Equal(["A.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".A", StringComparison.Ordinal)).Paths);
        Assert.Equal(["B.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".B", StringComparison.Ordinal)).Paths);
        Assert.Equal(["C.json", "CLAUDE.md"], map.Methods.Single(method => method.Id.EndsWith(".C", StringComparison.Ordinal)).Paths);
        Assert.Equal(["CLAUDE.md", "D.json"], map.Methods.Single(method => method.Id.EndsWith(".D", StringComparison.Ordinal)).Paths);
        var enumerating = map.Methods.Single(method => method.Id.EndsWith(".E", StringComparison.Ordinal));
        Assert.Equal(["CLAUDE.md", "E"], enumerating.Paths);
        Assert.Equal(TestMapUnknownReason.DirectoryEnumeration, Assert.Single(enumerating.UnknownReasons));
    }

    private static ScribeTestMap Derive(string path)
    {
        var source = $$"""
            class LiteralTests {
              [Fact] public void ReadsLiteral() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                .ReadAllText(RepositoryRelativePath.Create("{{path}}"));
            }
            """;
        return DeriveSources([new("LiteralTests.cs", source)]);
    }

    private static ScribeTestMap UnknownMap(
        string partition,
        string sourcePath,
        string typeName,
        string methodName) => ScribeTestMapDeriver.DeriveSources(
        [new(sourcePath, UnknownSource(typeName, methodName), partition)],
        []);

    private static string UnknownSource(string typeName, string methodName) => $$"""
        class {{typeName}} {
          [Fact] public void {{methodName}}() {
            var path = GetPath();
            File.ReadAllText(path);
          }
        }
        """;

    private static void AssertIntroducedUnknown(
        ScribeTestMap current,
        ScribeTestMap forkPoint,
        string displayIdentity)
    {
        var finding = Assert.Single(ScribeUnknownDebtPolicy.Evaluate(current, forkPoint));
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Contains(displayIdentity, finding.Message, StringComparison.Ordinal);
    }

    private static RepositorySnapshot Snapshot(params (string Path, string Content)[] files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static file =>
            RawRepositoryEntry.FromText(file.Path, file.Content)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static RepositorySnapshot ManagedSnapshot(params (string Path, string Content)[] files) =>
        Snapshot(files.Concat(
        [
            ("tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj", SdkProject),
            ("tools/tests/CompileFailProof/CompileFailProof.csproj", SdkProject),
        ]).ToArray());

    private static TemporaryRepository CreateTrackedRepository(
        params (string Path, string Content)[] files)
    {
        var repository = new TemporaryRepository();
        foreach (var file in files)
        {
            var fullPath = Path.Combine(
                repository.Path,
                file.Path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllText(fullPath, file.Content);
        }

        Assert.Equal(0, RunGit(repository.Path, "init").ExitCode);
        Assert.Equal(0, RunGit(repository.Path, "add", "--all").ExitCode);
        return repository;
    }

    private static ProcessOutput RunGit(string repositoryRoot, params string[] arguments) =>
        TestProcessRunner.Run(
            "git",
            arguments,
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

    private sealed class TemporaryRepository : IDisposable
    {
        internal TemporaryRepository()
        {
            Path = System.IO.Path.Combine(
                System.IO.Path.GetTempPath(),
                $"stratalint-test-map-{Guid.NewGuid():N}");
            Directory.CreateDirectory(Path);
        }

        internal string Path { get; }

        public void Dispose() => Directory.Delete(Path, recursive: true);
    }

    private static ScribeTestMap DeriveDiscoveryWithAccessorMarker(string markerExpression)
    {
        const string testSource = """
            class DiscoveryTests {
              [Fact] public void Discovers() => RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound);
            }
            """;
        var accessorSource = $$"""
            class RepositoryAccessor {
              private static bool Matches(string root, RepositoryRootCriterion criterion) => criterion switch {
                RepositoryRootCriterion.ClaudeDirectoryNotFound => {{markerExpression}},
                _ => false,
              };
            }
            """;

        return ScribeTestMapDeriver.DeriveSources(
            [new("DiscoveryTests.cs", testSource), new("Support/RepositoryAccessor.cs", accessorSource)],
            []);
    }

    private static ScribeTestMap DeriveSources(IEnumerable<TestMapSource> sources)
    {
        const string accessorSource = """
            class RepositoryAccessor {
              private static bool Matches(string root, RepositoryRootCriterion criterion) => criterion switch {
                RepositoryRootCriterion.ClaudeDirectoryNotFound => File.Exists(Path.Combine(root, "CLAUDE.md")),
                RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound =>
                  File.Exists(Path.Combine(root, "global.json")) && Directory.Exists(Path.Combine(root, "Blueprint")),
                _ => false,
              };
            }
            """;
        return ScribeTestMapDeriver.DeriveSources(
            sources.Append(new("Support/RepositoryAccessor.cs", accessorSource)),
            []);
    }
}
