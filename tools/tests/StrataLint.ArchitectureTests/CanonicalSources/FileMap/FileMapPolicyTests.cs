using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void LeanReportConfigurationIsAdmittedWithItsRuntimeVerifier()
    {
        const string path = "lean-report-inputs.json";
        var root = RepositoryLayout.FindRoot();
        var policy = Assert.IsType<PolicyLoadOutcome.Accepted>(
            RepositoryPolicyLoader.LoadRepository(root));
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), policy.Policy));
        var manifest = FileMapLoader.LoadRepository(root);
        var entry = Assert.Single(manifest.Match(path));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Equal("LeanReportSelection", Assert.Single(entry.VerifiedBy));
        Assert.Contains("lean-report", entry.Require);
        Assert.DoesNotContain(FileMapPolicy.InspectRepository(root), finding =>
            finding.Path == path && finding.Code is "FILEMAP-DATA-VERIFIER" or "FILEMAP-DATA-VERIFIER-DANGLING");
    }

    [Fact]
    public void CanonicalFileMapPolicyReloadsWithArtifactKindsAndExactRootCoverage()
    {
        var root = RepositoryLayout.FindRoot();
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.LoadRepository(root)).Policy;
        var reloaded = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            policy.CanonicalFileMapBytes.AsSpan(),
            policy.CanonicalDomainsBytes.AsSpan())).Policy;

        Assert.Equal(policy.FileMapSha256, reloaded.FileMapSha256);
        Assert.Equal(policy.CanonicalFileMapBytes.ToArray(), reloaded.CanonicalFileMapBytes.ToArray());
        Assert.Equal(
            ["csv", "json", "md", "py", "txt", "yaml", "yml"],
            policy.ArtifactKinds.Keys.Select(static key => key.Value).Order(StringComparer.Ordinal).ToArray());
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("LICENSE"), policy));
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("unregistered.json"), policy));
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown("agents/unregistered.md"), policy));
    }

    [Fact]
    public void CommonExecutionManifestsHaveRegisteredDataVerifiers()
    {
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        string[] paths = ["Meta/ci-checks.json", "Meta/engineering-projects.json"];
        Assert.All(paths, path =>
        {
            var entry = Assert.Single(manifest.Match(path));
            Assert.Equal(FileMapKind.Data, entry.Kind);
            Assert.Contains("CommonExecutionEvidence", entry.VerifiedBy);
        });

        var findings = FileMapPolicy.InspectRepository(root);

        Assert.DoesNotContain(findings, finding =>
            paths.Contains(finding.Path, StringComparer.Ordinal)
            && finding.Code is "FILEMAP-DATA-VERIFIER" or "FILEMAP-DATA-VERIFIER-DANGLING");
    }

    [Theory]
    [InlineData("lean-report")]
    [InlineData("scribe-content")]
    public void ReportProducerScopesHaveRegisteredDataVerifier(string scope)
    {
        var root = RepositoryLayout.FindRoot();
        var manifest = FileMapLoader.LoadRepository(root);
        var entry = Assert.Single(manifest.Match($"Meta/ReportProducers/{scope}.json"));

        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Equal("CommonExecutionEvidence", Assert.Single(entry.VerifiedBy));
        Assert.Equal("committed-source", entry.RuntimeDisposition);
    }

    [Theory]
    [InlineData("lean-report")]
    [InlineData("scribe-content")]
    public void ReportConsumerScopesAreAdmittedByRegisteredRepositoryPolicy(string scope)
    {
        var root = RepositoryLayout.FindRoot();
        var policy = Assert.IsType<PolicyLoadOutcome.Accepted>(
            RepositoryPolicyLoader.LoadRepository(root));
        var path = $"Meta/ReportConsumers/{scope}.json";

        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), policy.Policy));
        var entry = Assert.Single(FileMapLoader.LoadRepository(root).Match(path));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Equal("CommonExecutionEvidence", Assert.Single(entry.VerifiedBy));
    }

    [Theory]
    [InlineData("Meta/ReportConsumers/unregistered.json")]
    [InlineData("Meta/ReportConsumers/nested/lean-report.json")]
    [InlineData("Meta/unregistered.json")]
    public void UnregisteredMetaArtifactsRemainRejected(string path)
    {
        var root = RepositoryLayout.FindRoot();
        var policy = Assert.IsType<PolicyLoadOutcome.Accepted>(
            RepositoryPolicyLoader.LoadRepository(root));

        var issue = RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), policy.Policy);

        Assert.NotNull(issue);
        Assert.Equal("SL-000", issue!.RuleId.Value);
        Assert.Contains("matches=0", issue.Message, StringComparison.Ordinal);
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
        // 文档已迁出本程序集(住 StrataLint.Scribe.Documents),而本测试判的是 FILEMAP 声明
        // 与发射器产物身份的一致性,不判语料内容。故喂一条与下方 manifest.Match 同一字面的
        // 文档路径即可:六个固定工件与文档集无关,Blueprint/**/*.md 那条只需一个同形路径。
        var inventory = GeneratedArtifactInventory.Create(
            ["Blueprint/D5/S0/Carrier/Ring.md"]);
        var artifacts = inventory
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
            inventory,
            artifact => entry.Matches(artifact.Path));
        var findings = FileMapPolicy.InspectRepository(root);
        Assert.DoesNotContain(findings, finding => finding.Path == pattern);
        Assert.DoesNotContain(findings, finding => finding.Code == "FILEMAP-PATTERN-EMPTY");
    }

    [Fact]
    public void AgentReportsAreAdmittedByRepositoryPathPolicy()
    {
        // Agent-written reports have generated names, cannot be enumerated in
        // FILEMAP uses a family registration because report names are generated.
        const string value = "docs/reports/diag-lane-a/synthetic-open-report.md";
        var policy = SyntheticPolicy("docs/reports/**/*.md");
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, policy.Policy));
    }

    [Fact]
    public void DevelopmentSpecDocumentsAreAdmittedByRepositoryPathPolicy()
    {
        // An explicitly registered source family admits its canonical children.
        const string value = "docs/develop/spec/synthetic-unregistered-spec.md";
        var policy = SyntheticPolicy();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, policy.Policy));
    }

    [Fact]
    public void DevelopmentDirectoriesOutsideSpecAndTheoryAreRefusedByRepositoryPathPolicy()
    {
        // Reverse nail: the admitted prefix is docs/develop/spec/, not the
        // broader docs/develop/. A sibling directory must still be refused,
        // so widening the prefix by mistake turns this test red.
        const string value = "docs/develop/scratch/synthetic-note.md";
        var policy = SyntheticPolicy();
        var path = RepoPath.CreateKnown(value);

        var issue = RepositoryPathPolicy.Validate(path, policy.Policy);

        Assert.NotNull(issue);
        Assert.Contains("matches=0", issue!.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CodexSkillPackagesAreAdmittedByRepositoryPathPolicy()
    {
        // A Codex skill package is a directory containing SKILL.md, whose file
        // the registered FILEMAP prefix covers each package.
        const string value = ".codex/skills/synthetic-skill/SKILL.md";
        var policy = SyntheticPolicy();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, policy.Policy));
    }

    [Fact]
    public void CodexArtifactsOutsideSkillsAreRefusedByRepositoryPathPolicy()
    {
        const string value = ".codex/settings.toml";
        var policy = SyntheticPolicy();
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, policy.Policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Contains("matches=0", issue.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SkillPackagesAreAdmittedByRepositoryPathPolicy()
    {
        // A skill package is a directory holding SKILL.md, governed by the FILEMAP package pattern.
        const string value = "skills/synthetic-skill/SKILL.md";
        var policy = SyntheticPolicy();
        var path = RepoPath.CreateKnown(value);

        Assert.Null(RepositoryPathPolicy.Validate(path, policy.Policy));
    }

    [Fact]
    public void SkillsPrefixWithoutSeparatorIsRefusedByRepositoryPathPolicy()
    {
        const string value = "skills.md";
        var policy = SyntheticPolicy();
        var path = RepoPath.CreateKnown(value);

        var issue = Assert.IsType<RepositoryPathIssue>(
            RepositoryPathPolicy.Validate(path, policy.Policy));
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Contains("matches=0", issue.Message, StringComparison.Ordinal);
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

    [Theory]
    [InlineData("docs/reports/**", "docs/reports/meaningful.md")]
    [InlineData("docs/reports/experiment/**", "docs/reports/experiment/nested/results.json")]
    [InlineData("docs/reports/**/*.py", "docs/reports/probe.py")]
    [InlineData("docs/reports/**/*.py", "docs/reports/experiment/nested/probe.py")]
    public void ReportCoveredByADirectoryPatternIsAcceptedByTheGreenFixture(string pattern, string path)
    {
        var manifest = Parse(Entry(
            pattern,
            "data",
            "none",
            "agent",
            "SnapshotDecoder"));

        Assert.Empty(FileMapPolicy.InspectCoverage(manifest, [path]));
    }

    [Fact]
    public void ReportWithoutAFileMapEntryIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "README.md",
            "data",
            "none",
            "reader",
            "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectCoverage(
            manifest,
            ["docs/reports/unregistered.md"]));

        Assert.Equal("FILEMAP-REPORT-UNREGISTERED", finding.Code);
        Assert.Equal("docs/reports/unregistered.md", finding.Path);
    }

    [Fact]
    public void ReportWithAnExactFileMapEntryIsAcceptedByTheGreenFixture()
    {
        var path = "docs/reports/meaningful.md";
        var manifest = Parse(Entry(
            path,
            "data",
            "none",
            "agent",
            "SnapshotDecoder"));

        Assert.Empty(FileMapPolicy.InspectCoverage(manifest, [path]));
    }

    [Fact]
    public void ReportCanBeRegisteredBeforeItsContentIsAdded()
    {
        const string path = "docs/reports/experiment/results.json";
        var entry = Entry(path, "data", "none", "agent", "SnapshotDecoder")
            .Replace("admission_plane = \"judge\"", "admission_plane = \"content\"", StringComparison.Ordinal);
        var manifest = Parse(entry);

        // SL-029 requires the registration PR to precede the content PR.
        Assert.Empty(FileMapPolicy.InspectPatternPopulation(manifest, []));
        Assert.Empty(FileMapPolicy.InspectCoverage(manifest, [path]));
        var decision = AdmissionPlanePolicy.Evaluate(
            RawRepositorySnapshot.Create([RawRepositoryEntry.FromText(
                AdmissionPlanePolicy.FileMapPath, "schema_version = 3\n" + entry)]),
            RawRepositorySnapshot.Create([]),
            RawChangeSet.Create([path]));
        Assert.True(decision.IsAdmissible);
        Assert.Equal(AdmissionPlaneClassification.ContentOnly, decision.Classification);
    }

    [Fact]
    public void ReportDirectoryPatternCanBeRegisteredBeforeContentIsAdded()
    {
        var manifest = Parse(Entry("docs/reports/experiment/*", "data", "none", "agent", "SnapshotDecoder"));

        Assert.Empty(FileMapPolicy.InspectPatternPopulation(manifest, []));
        Assert.Empty(FileMapPolicy.InspectCoverage(manifest, ["docs/reports/experiment/result.json"]));
        var finding = Assert.Single(FileMapPolicy.InspectCoverage(manifest, ["docs/reports/other/result.json"]));
        Assert.Equal("FILEMAP-REPORT-UNREGISTERED", finding.Code);
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
    public void EmptyFrozenStatePatternIsRejectedLikeAnyOtherCommittedPattern()
    {
        var manifest = Parse(Entry(
            "Golden/Frozen/state/**/*.json",
            "data",
            "FrozenStateWriter",
            "FrozenStateCatalog",
            "FrozenStateRecordLoader"));

        var finding = Assert.Single(FileMapPolicy.InspectPatternPopulation(manifest, []));
        Assert.Equal("FILEMAP-PATTERN-EMPTY", finding.Code);
        Assert.Equal("Golden/Frozen/state/**/*.json", finding.Path);
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
    public void MissingRegisteredLiteralHasAFileMapReferenceDiagnostic()
    {
        var manifest = Parse(Entry("Makefile", "program", "none", "reader", "repository-policy"));
        var finding = Assert.Single(FileMapPolicy.InspectPatternPopulation(manifest, ["README.md"]));
        Assert.Equal("FILEMAP-PATTERN-EMPTY", finding.Code);
        Assert.Equal("Makefile", finding.Path);
    }

    [Fact]
    public void RegisteredPresentRootHasNoMembershipOrReferenceDiagnostic()
    {
        var manifest = Parse(Entry("README.md", "program", "none", "reader", "repository-policy"));
        Assert.Empty(FileMapPolicy.InspectCoverage(manifest, ["README.md"]));
        Assert.Empty(FileMapPolicy.InspectPatternPopulation(manifest, ["README.md"]));
    }
}
