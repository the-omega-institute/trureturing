using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed class FileMapPolicyTests
{
    [Fact]
    public void RepositoryFilesConformToTheCanonicalFileMap()
    {
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var inventory = manifest.Entries
            .Where(static entry => entry.Kind is FileMapKind.Generated
                && entry.RuntimeDisposition == "run-local")
            .Select(static entry => new RunArtifactInventoryItem(
                entry.ArtifactId, entry.Pattern, entry.Mode!))
            .ToArray();
        var outputRoot = Path.Combine(Path.GetTempPath(), "filemap-receipt-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(outputRoot);
        try
        {
            var request = RunHandleJson.Write(new Dictionary<string, object?>
            {
                ["schema"] = "run-request-v1",
                ["run_id"] = "00000000000000000000000000000000",
                ["source_tree_sha256"] = new string('a', 64),
                ["base_tree_sha256"] = new string('b', 64),
                ["producer_build_sha256"] = new string('c', 64),
                ["source_date_epoch"] = 0,
                ["expected_artifact_inventory_sha256"] = RunHandleDigests.Inventory(inventory),
            });
            Assert.Equal(0, RunHandleProducer.Produce(root, outputRoot, request, inventory).ExitCode);

            var findings = FileMapPolicy.InspectRepository(root, outputRoot);

            Assert.True(
                findings.Count == 0,
                string.Join(
                    Environment.NewLine,
                    findings.Select(static finding =>
                        $"{finding.Code} {finding.Path}: {finding.Message}")));
        }
        finally
        {
            Directory.Delete(outputRoot, recursive: true);
        }
    }

    [Fact]
    public void ReviewScaffoldPatternsRemainInTheRepositoryGitignore()
    {
        var root = RepositoryLayout.FindRoot();
        var lines = File.ReadAllLines(Path.Combine(root, ".gitignore"));

        Assert.Contains(".caller-review-prompt.md", lines, StringComparer.Ordinal);
        Assert.Contains(".echo-review.md", lines, StringComparer.Ordinal);
        Assert.Contains(".sshx-*", lines, StringComparer.Ordinal);
    }

    [Fact]
    public void PraContractCutsAllReceiptBackedAggregates()
    {
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var tracked = GitIndexRepositoryFiles.Enumerate(root)
            .Select(static file => file.RelativePath)
            .ToHashSet(StringComparer.Ordinal);
        var ignores = File.ReadAllLines(Path.Combine(root, ".gitignore"))
            .ToHashSet(StringComparer.Ordinal);
        var cut = new[]
        {
            "Generated/DAG.md",
            "Generated/FILEMAP.md",
            "Generated/echo-residual-summary.md",
            "Generated/truth-graph.v1.json",
            "Evidence/D5/values.json",
            "Meta/StrataLint/Generated/anchor-catalog.v1.json",
            "Meta/StrataLint/Generated/scribe-emissions.v1.json",
        };

        Assert.All(cut, path =>
        {
            Assert.Equal("run-local", Assert.Single(manifest.Match(path)).RuntimeDisposition);
            Assert.DoesNotContain(path, tracked);
            Assert.Contains('/' + path, ignores);
        });
    }

    [Fact]
    public void ResidenceEpochIsClosedWithNoProtectedSurfaceData()
    {
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);

        var actual = FileMapPolicy.ResidenceViolations(root);

        Assert.Empty(actual);
        Assert.Equal("RESIDENCE-EPOCH", manifest.ResidencePolicy.CaseId);
        Assert.Equal("data-must-live-outside-Meta/StrataLint", manifest.ResidencePolicy.Desired);
        Assert.Equal(0, manifest.ResidencePolicy.KnownViolationCount);
        Assert.Equal("closed", manifest.ResidencePolicy.Status);
        Assert.Equal(FileMapKind.Data, Assert.Single(manifest.Match("Golden/fixture-registry.yaml")).Kind);
    }

    [Fact]
    public void ComputationalProjectionRegistrationsAgreeAcrossCanonicalSources()
    {
        var expectedPaths = new HashSet<string>(
            [
                ScribeEmitter.AttestationRelativePath,
                "Generated/truth-graph.v1.json",
                CanonicalAnchorCatalogWriter.RelativePath,
            ],
            StringComparer.Ordinal);
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var artifacts = GeneratedArtifactInventory.All
            .Where(artifact => expectedPaths.Contains(artifact.Path))
            .ToArray();

        Assert.Equal(expectedPaths.Count, artifacts.Length);
        Assert.All(artifacts, artifact =>
        {
            var entry = Assert.Single(manifest.Match(artifact.Path));
            Assert.Equal(FileMapKind.Generated, entry.Kind);
            Assert.Equal(artifact.Producer, entry.ProducedBy);
            Assert.Contains(artifact.VerifiedBy, entry.VerifiedBy, StringComparer.Ordinal);
        });

        var topLevelProjectionPaths = expectedPaths
            .Where(static path => path.StartsWith("Generated/", StringComparison.Ordinal))
            .Select(RepoPath.CreateKnown)
            .ToArray();
        Assert.All(topLevelProjectionPaths, path =>
            Assert.Contains(path, registry.Policy.GovernanceDocuments));

        var anchorCatalog = Assert.Single(
            artifacts,
            static artifact => Path.GetFileName(artifact.Path) == "anchor-catalog.v1.json");
        Assert.DoesNotContain(
            RepoPath.CreateKnown(anchorCatalog.Path),
            registry.Policy.GovernanceDocuments);
        var tower = File.ReadAllText(Path.Combine(root, "Meta", "StrataLint", "TOWER.yaml"));
        Assert.Contains("      - " + anchorCatalog.Path, tower, StringComparison.Ordinal);
    }

    [Fact]
    public void PerformanceBudgetsHaveARegisteredGoldenDataResidence()
    {
        const string value = "Golden/perf-budgets.toml";
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        var entry = Assert.Single(manifest.Match(value));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal("PerfBudgetLoader", Assert.Single(entry.ConsumedBy));
        Assert.Equal("PerfBudgetLoader", Assert.Single(entry.VerifiedBy));
        Assert.Contains(path, registry.Policy.GovernanceDocuments);
        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
        Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create([value])));
    }

    [Fact]
    public void DevloopPlanDocumentsAreAdmittedByRepositoryPathPolicy()
    {
        // Self-driving devloop plan documents are emitted under docs/devloop/plans/
        // with dynamically generated names (one per prove-task), so they cannot be
        // enumerated individually in registry.yaml governance_documents. The
        // RepositoryPathPolicy admits the whole docs/devloop/ prefix; SL-000 must
        // not reject dynamically generated plans as unknown top-level artifacts.
        const string value = "docs/devloop/plans/synthetic-prove-task-plan.md";
        var root = RepositoryLayout.FindRoot();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                File.ReadAllBytes(Path.Combine(root, "Meta", "registry.yaml")),
                File.ReadAllBytes(Path.Combine(root, "Meta", "domains.yaml"))));
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, registry.Policy));
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
    public void LibrarySplitLedgerIsClassifiedAsLedger()
    {
        var manifest = FileMapLoader.LoadRepository(RepositoryLayout.FindRoot());

        Assert.Equal(
            FileMapKind.Ledger,
            Assert.Single(manifest.Match("Library/MAP.md")).Kind);
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
    public void ExactProtectedResidenceCountIsAccepted()
    {
        const string path = "Meta/StrataLint/Golden/cases/known.toml";
        var manifest = Parse(1, ResidenceEntry(path));

        Assert.Empty(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));
    }

    [Fact]
    public void AdditionalProtectedResidenceViolationIsRejected()
    {
        var manifest = Parse(
            1,
            ResidenceEntry("Meta/StrataLint/Golden/cases/**/*.toml"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(
            manifest,
            [
                "Meta/StrataLint/Golden/cases/known.toml",
                "Meta/StrataLint/Golden/cases/new.toml",
            ]));

        Assert.Equal("FILEMAP-RESIDENCE-DRIFT", finding.Code);
    }

    [Fact]
    public void MissingProtectedResidenceViolationIsRejected()
    {
        const string path = "Meta/StrataLint/Golden/cases/known.toml";
        var manifest = Parse(2, ResidenceEntry(path));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-RESIDENCE-DRIFT", finding.Code);
    }

    [Fact]
    public void ResidenceInventoryIncludesOnlyMarkedProtectedData()
    {
        const string externalPath = "Data/known.toml";
        const string unmarkedPath = "Meta/StrataLint/Golden/other.toml";
        const string markedPath = "Meta/StrataLint/Golden/values.toml";
        var manifest = Parse(
            ResidenceEntry(externalPath),
            Entry(unmarkedPath, "data", "none", "reader", "SnapshotDecoder"),
            ResidenceEntry(markedPath));

        var violations = FileMapPolicy.ResidenceViolations(
            manifest,
            [externalPath, markedPath, unmarkedPath]);

        Assert.Equal([markedPath], violations);
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
    public void RegistryAndTrackedRootDriftIsRejectedByTheRedFixture()
    {
        var finding = Assert.Single(FileMapPolicy.InspectRegistryRootAlignment(
            ["README.md"],
            ["Makefile", "README.md"]));

        Assert.Equal("FILEMAP-REGISTRY-ALIGNMENT", finding.Code);
        Assert.Contains("Makefile", finding.Message, StringComparison.Ordinal);
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

    [Fact]
    public void GeneratedFileWithoutProducerInventoryIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "emit-check"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void GeneratedDeclarationWithoutProducerIsRejectedByTheRedFixture()
    {
        var source = Entry(
            "Generated/output.json",
            "generated",
            "none",
            "reader",
            "emit-check");

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
            "emit-check"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json",
            "OtherEmitter",
            "emit-check");

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            [inventory]));

        Assert.Equal("FILEMAP-GENERATED-PRODUCER", finding.Code);
    }

    [Fact]
    public void UntrackedRunLocalWithoutReceiptRemainsStale()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "emit-check",
            "run-local",
            "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "emit-check", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void UntrackedRunLocalWithStaleReceiptRemainsStale()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "emit-check",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "emit-check", "A-OUTPUT");
        var receipt = new RunLocalArtifactReceipt(
            "A-OUTPUT", "Generated/output.json", "100644", new string('a', 64),
            "artifact-byte-verifier-v1", false);

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory], [receipt]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void UntrackedRunLocalWithVerifiedMatchingReceiptIsExempt()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "emit-check",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "emit-check", "A-OUTPUT");
        var receipt = new RunLocalArtifactReceipt(
            "A-OUTPUT", "Generated/output.json", "100644", new string('a', 64),
            "artifact-byte-verifier-v1", true);

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory], [receipt]);

        Assert.DoesNotContain(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void UntrackedRunLocalWithWrongProducerIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "WrongEmitter", "reader", "emit-check",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "emit-check", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-PRODUCER");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void UntrackedRunLocalWithBroadGlobIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/*.json", "generated", "JsonEmitter", "reader", "emit-check",
            "run-local", "A-OUTPUT"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json", "JsonEmitter", "emit-check", "A-OUTPUT");

        var findings = FileMapPolicy.InspectGeneratedInventory(manifest, [], [inventory]);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-LITERAL");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-GENERATED-STALE-INVENTORY");
    }

    [Fact]
    public void RunLocalEntryMissingRequiredFieldIsRejectedByTheRedFixture()
    {
        var source = DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "emit-check",
            "run-local", "A-OUTPUT").Replace("mode = \"100644\"\n", string.Empty, StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("mode", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommittedGeneratedEntryMissingModeIsRejectedByTheRedFixture()
    {
        var source = DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "emit-check",
            "committed-source", "A-OUTPUT").Replace("mode = \"100644\"\n", string.Empty, StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("mode", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WrongDeclaredCommittedModeIsRejectedByTheRedFixture()
    {
        var manifest = Parse(DispositionEntry(
            "Generated/output.json", "generated", "JsonEmitter", "reader", "emit-check",
            "committed-source", "A-OUTPUT").Replace("100644", "100755", StringComparison.Ordinal));

        var finding = Assert.Single(FileMapPolicy.InspectDeclaredModes(
            manifest,
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["Generated/output.json"] = "100644",
            }));

        Assert.Equal("FILEMAP-GENERATED-MODE", finding.Code);
    }

    [Theory]
    [InlineData("Generated/manual.md", "data", "FILEMAP-DIRECTORY-KIND")]
    [InlineData("Meta/StrataLint/cases.toml", "data", "FILEMAP-DATA-RESIDENCE")]
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
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "emit-check"),
            Entry("Generated/**/*.lean", "generated", "LeanEmitter", "lake", "emit-check"),
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

    private static FileMapManifest Parse(int knownViolationCount, params string[] entries) =>
        FileMapLoader.Parse(
            Encoding.UTF8.GetBytes(
                $$"""
                schema_version = 2

                [residence_policy]
                case_id = "RESIDENCE-EPOCH"
                desired = "data-must-live-outside-Meta/StrataLint"
                known_violation_count = {{knownViolationCount}}
                status = "known-violations-frozen-under-monitoring"

                """ + string.Join("\n", entries)),
            "fixture.toml");

    private static string ResidenceEntry(string pattern) =>
        Entry(pattern, "data", "none", "reader", "SnapshotDecoder")
        + "residence_violation = true\n";

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
        authority = "self"
        runtime_disposition = "committed-source"
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
        authority = "self"
        runtime_disposition = "{{runtimeDisposition}}"
        artifact_id = "{{artifactId}}"
        mode = "100644"
        history_requirement = "not-required"
        """ + "\n";
}
