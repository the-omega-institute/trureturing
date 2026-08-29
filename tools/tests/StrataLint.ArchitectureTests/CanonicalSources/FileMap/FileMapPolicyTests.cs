using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void MissionHasARegisteredGoldenDataResidence()
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());

        var entry = Assert.Single(manifest.Match(MissionFileLoader.RelativePath));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal("MissionFileLoader", Assert.Single(entry.ConsumedBy));
        Assert.Equal("MissionFileLoader", Assert.Single(entry.VerifiedBy));
    }

    [Fact]
    public void EngineeringTestRetirementDeclarationsHaveARegisteredSchemaVerifier()
    {
        const string pattern = "Golden/EngineeringTestRetirements/*.json";
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var entry = Assert.Single(manifest.Match(
            "Golden/EngineeringTestRetirements/example.json"));

        Assert.Equal(pattern, entry.Pattern);
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(["EngineeringTestRetirementLoader"], entry.ConsumedBy.ToArray());
        Assert.Equal(["EngineeringTestRetirementLoader"], entry.VerifiedBy.ToArray());
        Assert.DoesNotContain(
            FileMapPolicy.InspectRepository(root),
            finding => finding.Path == pattern);
    }

    [Fact]
    public void ComputationalProjectionsHaveCanonicalFileMapEntries()
    {
        var expectedPaths = new HashSet<string>(
            [
                ScribeEmitter.AttestationRelativePath,
                "Generated/truth-graph.v1.json",
            ],
            StringComparer.Ordinal);
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var artifacts = GeneratedArtifactInventory.All
            .Where(artifact => expectedPaths.Contains(artifact.Path))
            .ToArray();

        Assert.Equal(expectedPaths.Count, artifacts.Length);
        Assert.All(artifacts, artifact =>
        {
            var entry = Assert.Single(manifest.Match(artifact.Path));
            Assert.Equal(FileMapKind.Generated, entry.Kind);
            Assert.Equal(artifact.Producer, entry.ProducedBy);
            Assert.Contains(artifact.Producer, entry.VerifiedBy, StringComparer.Ordinal);
        });
        const string pattern = "Blueprint/**/*.md";
        var entry = Assert.Single(manifest.Match("Blueprint/D5/S0/Carrier/Ring.md"));

        Assert.Equal(pattern, entry.Pattern);
        Assert.Equal(FileMapKind.Generated, entry.Kind);
        Assert.Equal("ScribeEmitter", entry.ProducedBy);
        Assert.Equal(
            ["ScribeEmitter", "reader"],
            entry.ConsumedBy.ToArray());
        Assert.Equal(["ScribeEmitter"], entry.VerifiedBy.ToArray());
        Assert.Contains(
            GeneratedArtifactInventory.All,
            artifact => entry.Matches(artifact.Path));
        Assert.DoesNotContain(
            FileMapPolicy.InspectRepository(root),
            finding => finding.Path == pattern);
    }

    [Fact]
    public void AgentReportsAreAdmittedByRepositoryPathPolicy()
    {
        // Agent-written reports have generated names, cannot be enumerated in
        // registry.yaml governance_documents, so RepositoryPathPolicy admits the
        // docs/reports/ prefix and SL-000 must not reject them.
        const string value = "docs/reports/diag-lane-a/synthetic-open-report.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void CodexSkillPackagesAreAdmittedByRepositoryPathPolicy()
    {
        // A Codex skill package is a directory containing SKILL.md, whose file
        // names cannot be enumerated individually in registry.yaml.
        const string value = ".codex/skills/synthetic-skill/SKILL.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void CodexArtifactsOutsideSkillsAreRefusedByRepositoryPathPolicy()
    {
        const string value = ".codex/settings.toml";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, registry.Policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal("unknown top-level artifact", issue.Message);
    }

    [Fact]
    public void SkillPackagesAreAdmittedByRepositoryPathPolicy()
    {
        // A skill package is a directory holding SKILL.md, whose file names cannot be enumerated in registry.yaml.
        const string value = "skills/synthetic-skill/SKILL.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
    }

    [Fact]
    public void SkillsPrefixWithoutSeparatorIsRefusedByRepositoryPathPolicy()
    {
        const string value = "skills.md";
        var registry = SyntheticRegistry();
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, registry.Policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal("unknown top-level artifact", issue.Message);
    }

    [Fact]
    public void LibrarySplitBucketsAreClassifiedAsData()
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());

        Assert.Equal(
            FileMapKind.Data,
            Assert.Single(manifest.Match("Library/Weil/sample2026paper.md")).Kind);
    }

    [Fact]
    public void ResidenceMarkerOutsideTheProtectedSurfaceIsRejected()
    {
        const string path = "Data/known.toml";
        var manifest = Parse(ResidenceEntry(path));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-RESIDENCE-MARKER", finding.Code);
    }

    [Fact]
    public void ProjectionFixtureDirectoryRejectsNonDataEntries()
    {
        const string path = "Golden/Projection/x.json";
        var manifest = Parse(Entry(path, "program", "none", "reader", "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-DIRECTORY-KIND", finding.Code);
    }

    [Fact]
    public void UnclassifiedFileIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry("D5/**/*.lean", "truth", "none", "lake", "lean-build"));

        var finding = Assert.Single(FileMapPolicy.InspectCoverage(
            manifest,
            ["D5/S0/Ring.lean", "README.md"]));

        Assert.Equal("FILEMAP-UNCLASSIFIED", finding.Code);
        Assert.Equal("README.md", finding.Path);
    }

    [Fact]
    public void OverlappingPatternsAreRejectedByTheRedFixture()
    {
        var manifest = Parse(
            Entry("D5/**/*.lean", "truth", "none", "lake", "lean-build"),
            Entry("D5/S0/**/*.lean", "truth", "none", "lake", "lean-build"));

        var finding = Assert.Single(FileMapPolicy.InspectCoverage(
            manifest,
            ["D5/S0/Ring.lean"]));

        Assert.Equal("FILEMAP-AMBIGUOUS", finding.Code);
        Assert.Contains("D5/**/*.lean", finding.Message, StringComparison.Ordinal);
        Assert.Contains("D5/S0/**/*.lean", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EmptyCommittedPatternIsRejectedByTheRedFixture()
    {
        const string pattern = "Data/retired/*.json";
        var manifest = Parse(Entry(pattern, "data", "none", "reader", "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectPatternPopulation(manifest, []));

        Assert.Equal("FILEMAP-PATTERN-EMPTY", finding.Code);
        Assert.Equal(pattern, finding.Path);
    }

    [Fact]
    public void PopulatedCommittedPatternIsAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Data/current/*.json",
            "data",
            "none",
            "reader",
            "SnapshotDecoder"));

        Assert.Empty(FileMapPolicy.InspectPatternPopulation(
            manifest,
            ["Data/current/object.json"]));
    }

    [Fact]
    public void EmptyRunLocalPatternIsAcceptedByTheExemptFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/retired.json",
            "generated",
            "SyntheticEmitter",
            "reader",
            "SyntheticEmitter",
            "run-local",
            "A-SYNTHETIC-RETIRED"));

        Assert.Empty(FileMapPolicy.InspectPatternPopulation(manifest, []));
    }

    [Fact]
    public void DanglingGeneratedAndDataActorsAreRejectedByTheRedFixture()
    {
        const string pattern = "Generated/output.json";
        var manifest = Parse(Entry(
            pattern,
            "generated",
            "MissingEmitter",
            "reader",
            "MissingEmitter"));

        var findings = FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal),
            "fixture-root");

        Assert.Equal(2, findings.Count);
        Assert.All(findings, finding =>
        {
            Assert.Equal("FILEMAP-ACTOR-DANGLING", finding.Code);
            Assert.Contains("MissingEmitter", finding.Message, StringComparison.Ordinal);
        });
        var declaredTypes = new HashSet<string>(StringComparer.Ordinal) { "ScribeEmitter" };
        var danglingProducer = Assert.Single(FileMapPolicy.InspectDeclaredActors(
            Parse(Entry(pattern, "data", "MissingEmitter", "reader", "ScribeEmitter")),
            declaredTypes,
            "fixture-root"));
        var danglingConsumer = Assert.Single(FileMapPolicy.InspectDeclaredActors(
            Parse(Entry(pattern, "data", "none", "DigestionStatusEvaluator", "ScribeEmitter")),
            declaredTypes,
            "fixture-root"));

        Assert.Contains("produced_by names MissingEmitter", danglingProducer.Message, StringComparison.Ordinal);
        Assert.Contains(
            "consumed_by names DigestionStatusEvaluator",
            danglingConsumer.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredGeneratedActorIsAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "FixtureEmitter",
            "reader",
            "FixtureEmitter"));

        Assert.Empty(FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal) { "FixtureEmitter" },
            "fixture-root"));
    }

    [Theory]
    [InlineData("ledger")]
    [InlineData("truth")]
    public void DanglingLedgerAndTruthActorsAreRejectedByTheRedFixture(string kind)
    {
        var manifest = Parse(Entry(
            $"Synthetic/{kind}.txt",
            kind,
            "none",
            "MissingConsumer",
            "MissingVerifier"));

        var findings = FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal),
            "fixture-root");

        Assert.Collection(
            findings,
            finding =>
            {
                Assert.Equal("FILEMAP-ACTOR-DANGLING", finding.Code);
                Assert.Contains("consumed_by names MissingConsumer", finding.Message, StringComparison.Ordinal);
            },
            finding =>
            {
                Assert.Equal("FILEMAP-ACTOR-DANGLING", finding.Code);
                Assert.Contains("verified_by names MissingVerifier", finding.Message, StringComparison.Ordinal);
            });
    }

    [Fact]
    public void LedgerVerifierNamedByARuleIdIsAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Synthetic/ledger.md",
            "ledger",
            "none",
            "reader",
            "SL-008"));

        Assert.Empty(FileMapPolicy.InspectDeclaredActors(
            manifest,
            new HashSet<string>(StringComparer.Ordinal),
            "fixture-root"));
    }

    [Fact]
    public void RegistryAndTrackedRootDriftIsRejectedByTheRedFixture()
    {
        var finding = Assert.Single(FileMapPolicy.InspectRegistryRootAlignment(
            ["README.md"],
            ["Makefile", "README.md"]));

        Assert.Equal("FILEMAP-REGISTRY-ALIGNMENT", finding.Code);
        Assert.Contains("Makefile", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void MatchingRegistryAndTrackedRootsAreAcceptedByTheGreenFixture()
    {
        Assert.Empty(FileMapPolicy.InspectRegistryRootAlignment(
            ["Makefile", "README.md"],
            ["README.md", "Makefile"]));
    }

    [Fact]
    public void MissingReviewScaffoldIgnoreIsRejectedByTheRedFixture()
    {
        var finding = Assert.Single(FileMapPolicy.InspectGitIgnore(
            ["/Generated/echo-residuals/", ".caller-review-prompt.md", ".echo-review.md"]));

        Assert.Equal("FILEMAP-GITIGNORE", finding.Code);
        Assert.Equal(".gitignore", finding.Path);
        Assert.Contains(".sshx-*", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CompleteReviewScaffoldIgnoresAreAcceptedByTheGreenFixture()
    {
        Assert.Empty(FileMapPolicy.InspectGitIgnore(
            ["/Generated/echo-residuals/", ".sshx-*", ".echo-review.md", ".caller-review-prompt.md"]));
    }

    [Fact]
    public void EchoResidualRegistryAndBroadFileMapPatternAreRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Generated/**/*.md",
            "generated",
            "EchoVerifyCommand",
            "reader",
            "EchoVerifyCommand"));

        var findings = FileMapPolicy.InspectProjectionRegistrations(
            manifest,
            ["Generated/echo-residuals/source.md"]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-PROJECTION-SHARD");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-PROJECTION-REGISTRY");
    }

    [Fact]
    public void EchoResidualLiteralFileMapPatternAndAbsentRegistryEntryAreAcceptedByTheGreenFixture()
    {
        var manifest = Parse(Entry(
            "Generated/echo-residuals/*.md",
            "generated",
            "EchoVerifyCommand",
            "reader",
            "EchoVerifyCommand").Replace(
                "runtime_disposition = \"committed-source\"",
                "runtime_disposition = \"run-local\"",
                StringComparison.Ordinal));

        Assert.Empty(FileMapPolicy.InspectProjectionRegistrations(manifest, []));
    }

    [Fact]
    public void DataWithoutAnExistingLoaderIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Data/**/*.toml",
            "data",
            "none",
            "MissingLoader",
            "MissingLoader"));

        var finding = Assert.Single(FileMapPolicy.InspectDataVerifiers(
            manifest,
            new HashSet<string>(StringComparer.Ordinal)));

        Assert.Equal("FILEMAP-DATA-VERIFIER", finding.Code);
    }

    // 存量证据:#1116 删掉 emit-check 之后,`Library/*/*.md` 仍写着它,而
    // InspectDataVerifiers 的 `.Any(...)` 因同条目还留着 LibraryNoteCatalog 而放行。
    [Fact]
    public void DataVerifierNameThatIsNeitherALoaderNorARuleIdIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DataEntryVerifiedBy(
            "Library/*/*.md",
            "LibraryNoteCatalog",
            "emit-check"));

        var finding = Assert.Single(FileMapPolicy.InspectDataVerifierNames(
            manifest,
            new HashSet<string>(StringComparer.Ordinal) { "LibraryNoteCatalog" }));

        Assert.Equal("FILEMAP-DATA-VERIFIER-DANGLING", finding.Code);
        Assert.Contains("emit-check", finding.Message, StringComparison.Ordinal);
    }

    // 反证:规则号是刻意的非类型名,不得被这条新检查误伤。
    [Fact]
    public void DataVerifierNamedByARuleIdIsAccepted()
    {
        var manifest = Parse(DataEntryVerifiedBy(
            "Library/**/*.yaml",
            "SL-017",
            "YamlSubsetParser"));

        Assert.Empty(FileMapPolicy.InspectDataVerifierNames(
            manifest,
            new HashSet<string>(StringComparer.Ordinal) { "YamlSubsetParser" }));
    }

    [Fact]
    public void GeneratedFileWithoutProducerInventoryIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter",
            "committed-source",
            "A-OUTPUT"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void DataKeyedGeneratedGlobWithoutProducerInventoryIsAccepted()
    {
        var manifest = Parse(Entry(
            "Generated/partitions/*.json",
            "generated",
            "PartitionEmitter",
            "reader",
            "PartitionEmitter"));

        var findings = FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/partitions/source-a.json"],
            []);

        Assert.Empty(findings);
    }

    [Fact]
    public void GeneratedGlobWithArtifactIdStillRequiresProducerInventory()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/partitions/*.json",
            "generated",
            "PartitionEmitter",
            "reader",
            "PartitionEmitter",
            "committed-source",
            "A-PARTITION"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/partitions/source-a.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void GeneratedLiteralWithoutArtifactIdStillRequiresProducerInventory()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void InventoryBackedAggregateRemainsAccepted()
    {
        var aggregateManifest = Parse(DispositionEntry(
            "Generated/summary.json",
            "generated",
            "SummaryEmitter",
            "reader",
            "SummaryEmitter",
            "committed-source",
            "A-SUMMARY"));
        var aggregate = new GeneratedArtifactIdentity(
            "Generated/summary.json",
            "SummaryEmitter",
            "A-SUMMARY");

        Assert.Empty(FileMapPolicy.InspectGeneratedInventory(
            aggregateManifest,
            [aggregate.Path],
            [aggregate]));
    }

    [Fact]
    public void GeneratedDeclarationWithoutProducerIsRejectedByTheRedFixture()
    {
        var source = Entry(
            "Generated/output.json",
            "generated",
            "none",
            "reader",
            "MissingProducer");

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("produced_by must name a producer", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratedProducerMismatchIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "JsonEmitter"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json",
            "OtherEmitter");

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            [inventory]));

        Assert.Equal("FILEMAP-GENERATED-PRODUCER", finding.Code);
    }

    [Theory]
    [InlineData("Generated/manual.md", "data", "FILEMAP-DIRECTORY-KIND")]
    [InlineData("tools/cases.toml", "data", "FILEMAP-DATA-RESIDENCE")]
    public void ClassDirectoryMixingIsRejectedByTheRedFixture(
        string path,
        string kind,
        string expectedCode)
    {
        var manifest = Parse(Entry(path, kind, "none", "reader", "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal(expectedCode, finding.Code);
    }

    [Fact]
    public void DataAndLeanGeneratedDependenciesAreRejectedByTheRedFixture()
    {
        var manifest = Parse(
            Entry("Data/**/*.toml", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "JsonEmitter"),
            Entry("Generated/**/*.lean", "generated", "LeanEmitter", "lake", "LeanEmitter"),
            Entry("Main.lean", "truth", "none", "lake", "lean-build"));
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Data/input.toml"] = "projection = \"Generated/output.json\"\n",
            ["Generated/output.json"] = "{}\n",
            ["Generated/Proof.lean"] = "def generated : Nat := 0\n",
            ["Main.lean"] = "import Generated.Proof\n",
        };

        var findings = FileMapPolicy.InspectDependencies(manifest, files);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-DATA-GENERATED-DEPENDENCY");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-LEAN-GENERATED-IMPORT");
    }

    private static FileMapManifest Parse(params string[] entries) => Parse(0, entries);

    private static RegistryLoadOutcome.Accepted SyntheticRegistry(string? governanceDocument = null)
    {
        var governanceDocuments = new[]
        {
            "Generated/FILEMAP.md",
            "Generated/truth-graph.v1.json",
            "Meta/Digestion/atomizers.toml",
            "Meta/FILEMAP.toml",
            "docs/CONTRIBUTING.md",
            "docs/GOVERNANCE.md",
            "docs/develop/spec/golden-ledger-repo-spec.md",
            "tools/Generated/scribe-emissions.v1.json",
        }.Append(governanceDocument)
            .Where(static path => path is not null)
            .Order(StringComparer.Ordinal)
            .Select(static path => $"  - \"{path}\"");
        var registry = """
            schema_version: 1
            root_files:
              - "README.md"
            governance_documents:
            """ + "\n" + string.Join('\n', governanceDocuments) + """

            agent_files:
              - "CONTEXT.md"
            artifact_kinds:
              json:
                profile: structured-json
                selectors:
                  - "result"
                path_selectors:
                  - "formal"
            """ + "\n";
        const string domains = """
            domains:
              Carrier:
                stratum: S0
                definition: Synthetic carrier domain.
            """ + "\n";
        return RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(domains)));
    }

    private static FileMapManifest Parse(int knownViolationCount, params string[] entries) =>
        FileMapLoader.Parse(
            Encoding.UTF8.GetBytes(
                $$"""
                schema_version = 2

                [residence_policy]
                case_id = "RESIDENCE-EPOCH"
                desired = "data-must-live-outside-tools"
                known_violation_count = {{knownViolationCount}}
                status = "known-violations-frozen-under-monitoring"

                """ + string.Join("\n", entries)),
            "fixture.toml");

    private static string ResidenceEntry(string pattern) =>
        Entry(pattern, "data", "none", "reader", "SnapshotDecoder")
        + "residence_violation = true\n";

    private static string DataEntryVerifiedBy(string pattern, params string[] verifiedBy) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "data"
        produced_by = "none"
        consumed_by = ["reader"]
        verified_by = [{{string.Join(", ", verifiedBy.Select(static name => $"\"{name}\""))}}]
        runtime_disposition = "committed-source"
        artifact_id = "none"
        """ + "\n";

    private static string Entry(
        string pattern,
        string kind,
        string producedBy,
        string consumedBy,
        string verifiedBy) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "{{kind}}"
        produced_by = "{{producedBy}}"
        consumed_by = ["{{consumedBy}}"]
        verified_by = ["{{verifiedBy}}"]
        runtime_disposition = "{{(kind == "ledger" ? "committed-ledger" : "committed-source")}}"
        artifact_id = "none"
        """ + "\n";

    private static string DispositionEntry(
        string pattern,
        string kind,
        string producedBy,
        string consumedBy,
        string verifiedBy,
        string runtimeDisposition,
        string artifactId) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "{{kind}}"
        produced_by = "{{producedBy}}"
        consumed_by = ["{{consumedBy}}"]
        verified_by = ["{{verifiedBy}}"]
        runtime_disposition = "{{runtimeDisposition}}"
        artifact_id = "{{artifactId}}"
        mode = "100644"
        history_requirement = "not-required"
        """ + "\n";
}
