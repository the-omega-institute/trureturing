using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineFixtureRegistrationCapacityTests
{
    private const string SourcePath =
        "tools/tests/StrataLint.ArchitectureTests/CanonicalSources/FileMap/FileMapPolicyTests.AdmissionPlane.cs";
    private const string ProjectPath =
        "tools/tests/StrataLint.ArchitectureTests/StrataLint.ArchitectureTests.csproj";

    [Fact]
    public void Sl003AcceptsFixtureRegistrationAndItsActualRegressionTests()
    {
        var result = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), Fixture().Build());

        Assert.True(result.Diagnostics.IsEmpty,
            string.Join('\n', result.Diagnostics.Select(static diagnostic => diagnostic.Render())));
    }

    [Fact]
    public void Sl003StillRejectsLineCapacityWithFixtureRegistrationDelta()
    {
        var fixture = Fixture();
        fixture.Files[SourcePath] += string.Concat(Enumerable.Repeat("// padding\n",
            RepositoryRules.ArtifactHardLineLimit));

        var result = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build());

        var finding = Assert.Single(result.Diagnostics, diagnostic =>
            diagnostic.Path == SourcePath && diagnostic.Message == "artifact exceeds 800 lines");
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
    }

    [Fact]
    public void Sl003StillRejectsDirectoryRatchetGrowthWithFixtureRegistrationDelta()
    {
        var fixture = Fixture();
        const string directory = "tools/tests/StrataLint.ArchitectureTests/CapacityControl";
        for (var index = 0; index < RepositoryRules.DirectoryFileLimit; index++)
        {
            var path = $"{directory}/Existing{index}.cs";
            fixture.Files[path] = fixture.Baseline[path] = "// existing\n";
        }
        var added = $"{directory}/Added.cs";
        fixture.Files[added] = "// added\n";
        fixture.Changes.Add(added);

        var result = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(3), fixture.Build());

        var finding = Assert.Single(result.Diagnostics, diagnostic => diagnostic.Path == directory);
        Assert.StartsWith("directory contains", finding.Message);
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
    }

    private static RuleFixture Fixture()
    {
        var fixture = new RuleFixture();
        fixture.Files[ProjectPath] = fixture.Baseline[ProjectPath] = """
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>
              <ItemGroup><PackageReference Include="xunit" Version="2.9.3" /></ItemGroup>
            </Project>
            """;
        fixture.Baseline[SourcePath] = BaselinePrefix + ExistingCases;
        fixture.Files[SourcePath] = CandidatePrefix + AddedCases + ExistingCases;
        const string usings = "tools/tests/StrataLint.ArchitectureTests/Usings.cs";
        fixture.Files[usings] = fixture.Baseline[usings] =
            "global using StrataLint.Engine;\nglobal using Xunit;\nglobal using StrataLint.TestSupport;\n";
        fixture.Files["Meta/FILEMAP.toml"] = FixtureRegistration;
        fixture.Baseline["Meta/FILEMAP.toml"] = FixtureRegistration.Replace(
            "admission_plane = \"judge\"", "admission_plane = \"content\"", StringComparison.Ordinal);
        const string registry = "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml";
        fixture.Files[registry] = fixture.Baseline[registry] = TestRegistry.Canonical;
        fixture.Changes.Clear();
        fixture.Changes.AddRange(["Meta/FILEMAP.toml", SourcePath]);
        return fixture;
    }

    // Fixed PR7101 source delta: a069b85b -> 041dee3f. These strings are input data
    // for the candidate rule; they do not classify or recognize test methods.
    private const string BaselinePrefix =
        "using StrataLint.Cli;\n\nnamespace StrataLint.ArchitectureTests;\n\npublic sealed partial class FileMapPolicyTests\n{\n";

    private const string CandidatePrefix =
        "using StrataLint.Cli;\nusing StrataLint.Engine;\nusing StrataLint.Scribe;\n\nnamespace StrataLint.ArchitectureTests;\n\npublic sealed partial class FileMapPolicyTests\n{\n";

    private const string AddedCases = """"
            [Fact]
            public void RegisteredTestPolicyFixtureIsJudgeData()
            {
                const string path = "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml";
                var root = RepositoryLayout.FindRoot();
                Assert.True(File.Exists(Path.Combine(root, path)));
                var manifest = FileMapLoader.LoadRepository(root);

                var entry = Assert.Single(manifest.Match(path));

                Assert.Equal(path, entry.Pattern);
                Assert.Equal(FileMapKind.Data, entry.Kind);
                Assert.Equal(["TestRegistry"], entry.ConsumedBy.ToArray());
                Assert.Equal(["TestRegistry"], entry.VerifiedBy.ToArray());
                Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
                Assert.Empty(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));
            }

            [Fact]
            public void RegisteredTestPolicyFixtureAndJudgePathAreJudgeOnly()
            {
                var root = RepositoryLayout.FindRoot();
                string[] paths =
                [
                    "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml",
                    "tools/StrataLint.Engine/RepositoryIo/AdmissionPlanePolicy.cs",
                ];
                Assert.All(paths, path => Assert.True(File.Exists(Path.Combine(root, path))));

                var decision = AdmissionPlanePolicy.Evaluate(
                    File.ReadAllBytes(Path.Combine(root, FileMapLoader.RelativePath)),
                    paths);

                Assert.Equal(AdmissionPlaneClassification.JudgeOnly, decision.Classification);
                Assert.True(decision.IsAdmissible);
                Assert.Empty(decision.Code);
            }

            [Fact]
            public void RegisteredLeanContentAndJudgePathRemainMixedAndRejected()
            {
                var root = RepositoryLayout.FindRoot();
                string[] paths =
                [
                    "D5/S0/Carrier/Ring.lean",
                    "tools/StrataLint.Engine/RepositoryIo/AdmissionPlanePolicy.cs",
                ];
                Assert.All(paths, path => Assert.True(File.Exists(Path.Combine(root, path))));

                var decision = AdmissionPlanePolicy.Evaluate(
                    File.ReadAllBytes(Path.Combine(root, FileMapLoader.RelativePath)),
                    paths);

                Assert.Equal(AdmissionPlaneClassification.Mixed, decision.Classification);
                Assert.False(decision.IsAdmissible);
                Assert.Equal("ADMISSION-PLANE-MIXED", decision.Code);
            }

        """" + "\n";

    private const string ExistingCases = """"
            [Fact]
            public void AdmissionPlaneIsAcceptedByTheStrictLoader()
            {
                var exception = Record.Exception(() => Parse(AdmissionEntry(
                    "tools/example.cs",
                    "program",
                    "judge")));

                Assert.Null(exception);
            }

            [Fact]
            public void AdmissionPlaneIsRequiredByTheStrictLoader()
            {
                var entryWithoutAdmissionPlane = Entry(
                    "tools/example.cs",
                    "program",
                    "none",
                    "dotnet",
                    "dotnet-test").Replace(
                        "admission_plane = \"judge\"\n",
                        string.Empty,
                        StringComparison.Ordinal);

                var exception = Assert.ThrowsAny<FormatException>(() => Parse(entryWithoutAdmissionPlane));

                Assert.Contains(
                    "FILEMAP-ADMISSION-PLANE-MISSING",
                    exception.Message,
                    StringComparison.Ordinal);
            }

            [Fact]
            public void UnknownAdmissionPlaneIsRejectedByTheStrictLoader()
            {
                var exception = Assert.ThrowsAny<FormatException>(() => Parse(AdmissionEntry(
                    "tools/example.cs",
                    "program",
                    "unknown")));

                Assert.Contains(
                    "FILEMAP-ADMISSION-PLANE-INVALID",
                    exception.Message,
                    StringComparison.Ordinal);
            }

            [Fact]
            public void NonStringAdmissionPlaneIsRejectedByTheStrictLoader()
            {
                var source = AdmissionEntry("tools/example.cs", "program", "judge").Replace(
                    "admission_plane = \"judge\"",
                    "admission_plane = 1",
                    StringComparison.Ordinal);

                var exception = Assert.ThrowsAny<FormatException>(() => Parse(source));

                Assert.Contains(
                    "FILEMAP-ADMISSION-PLANE-INVALID",
                    exception.Message,
                    StringComparison.Ordinal);
            }

            [Fact]
            public void FileMapPolicySourceMustBeInTheJudgeAdmissionPlane()
            {
                const string path = "Meta/FILEMAP.toml";
                var manifest = Parse(AdmissionEntry(path, "data", "content"));

                var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

                Assert.Equal("FILEMAP-ADMISSION-PLANE-INVALID", finding.Code);
                Assert.Equal(path, finding.Path);
            }

            [Fact]
            public void ContentAdmissionPlaneIsAcceptedForContentData()
            {
                const string path = "README.md";
                var manifest = Parse(AdmissionEntry(path, "data", "content"));

                Assert.Empty(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));
            }

            private static string AdmissionEntry(
                string pattern,
                string kind,
                string admissionPlane) => $$"""
                [[files]]
                pattern = "{{pattern}}"
                kind = "{{kind}}"
                admission_plane = "{{admissionPlane}}"
                produced_by = "none"
                consumed_by = ["{{(kind == "program" ? "dotnet" : "reader")}}"]
                verified_by = ["{{(kind == "program" ? "dotnet-test" : "SnapshotDecoder")}}"]
                runtime_disposition = "committed-source"
                artifact_id = "none"
                """ + "\n";
        }
        """" + "\n";

    private const string FixtureRegistration = """"
        [[files]]
        pattern = "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml"
        kind = "data"
        admission_plane = "judge"
        produced_by = "none"
        consumed_by = ["TestRegistry"]
        verified_by = ["TestRegistry"]
        artifact_id = "none"
        runtime_disposition = "committed-source"
        """" + "\n";

}
