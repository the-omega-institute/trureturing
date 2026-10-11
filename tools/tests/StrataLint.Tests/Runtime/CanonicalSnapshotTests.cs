using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed class CanonicalSnapshotTests
{
    [Theory]
    [InlineData(RuleFixture.FixtureBackfillAtomPath)]
    [InlineData(RuleFixture.FixtureBackfillSourcePath)]
    [InlineData(RuleFixture.FixtureCasPath)]
    [InlineData("docs/develop/theory/unrelated.yaml")]
    public void AuxiliaryDigestionInputDoesNotBlockLeanAdmission(string path)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[path] = "failure: [invalid\n";
        fixture.Files[RuleFixture.RingPath] += "-- candidate content\n";
        fixture.Files[RuleFixture.RingPath] = UtilityAdmissionTestSupport.WithUtility(
            fixture.Files[RuleFixture.RingPath], "none");
        var changes = RawChangeSet.Create([RuleFixture.RingPath]);
        var context = fixture.Build(changes);
        var outcome = AdmissionPipeline.Evaluate(context.Current, context.Baseline,
            context.Policy, context.Lean, changes,
            Assert.IsType<BootstrapOutcome.Clear>(BootstrapGate.Evaluate(changes)).Capability);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
    }

    [Fact]
    public void NonDigestionMalformedYamlStillBlocksAdmission()
    {
        var fixture = new RuleFixture();
        fixture.Files["tools/TOWER.yaml"] = "failure: [invalid\n";
        var context = fixture.Build();
        var result = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.Execute(context)).Capability;

        Assert.Contains(result.Diagnostics, diagnostic => diagnostic.RuleId == RuleId.CreateKnown(19)
            && diagnostic.AdmissionEffect is AdmissionEffect.Block);
    }

    [Fact]
    public void AutomaticDigestionAuditIsAbsentFromAdmissionCatalog()
    {
        Assert.DoesNotContain(RuleCatalog.Default.Descriptors,
            descriptor => descriptor.Id == RuleId.CreateKnown(16));
    }

    [Theory]
    [InlineData(RuleFixture.FixtureBackfillAtomPath)]
    [InlineData(RuleFixture.FixtureBackfillSourcePath)]
    [InlineData(RuleFixture.FixtureCasPath)]
    [InlineData("docs/develop/theory/unrelated.md")]
    public void AdmissionIdentityOmitsUnreadAuxiliaryBodies(string auxiliaryPath)
    {
        var fixture = new RuleFixture();
        fixture.Files[auxiliaryPath] = "first auxiliary bytes\n";
        var first = ProjectedSnapshot(fixture, auxiliaryPath);
        fixture.Files[auxiliaryPath] = "different auxiliary bytes\n";
        var second = ProjectedSnapshot(fixture, auxiliaryPath);
        var policy = fixture.Build().Policy;

        var firstIdentity = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(first, policy)).Capability;
        var secondIdentity = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(second, policy)).Capability;

        Assert.Equal(firstIdentity.Sha256, secondIdentity.Sha256);
        Assert.DoesNotContain(Convert.ToHexStringLower(Encoding.UTF8.GetBytes(auxiliaryPath)),
            Encoding.UTF8.GetString(firstIdentity.Bytes.AsSpan()), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false, RuleFixture.FixtureBackfillAtomPath)]
    [InlineData(false, RuleFixture.FixtureBackfillSourcePath)]
    [InlineData(true, RuleFixture.FixtureBackfillAtomPath)]
    [InlineData(true, RuleFixture.FixtureBackfillSourcePath)]
    public void AdmissionIdentityBindsSelectedUtilityInputs(bool firstFreeze, string changedInput)
    {
        var fixture = UtilityAdmissionTestSupport.AtomUtilityFixture(targetStatementId: null);
        var policy = fixture.Build().Policy;
        const string unrelated = "Meta/Digestion/backfill/unrelated/partial-open/"
            + "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc.yaml";
        fixture.Files[unrelated] = "failure: [invalid\n";
        var changedPath = firstFreeze
            ? UtilityAdmissionTestSupport.AddCandidateState(fixture)
            : RuleFixture.RingPath;
        var changes = RawChangeSet.Create([changedPath]);

        CanonicalFixedPoint Identity()
        {
            IRepositoryGateway repository = new FakeRepositoryGateway(changes,
                UtilityAdmissionTestSupport.Raw(fixture.Files), UtilityAdmissionTestSupport.Raw(fixture.Baseline));
            var raw = AdmissionRepositoryInputs.ReadDeltaInputs(repository,
                AdmissionRepositoryInputs.ReadCurrent(repository),
                AdmissionRepositoryInputs.ReadBaseline(repository, "baseline"), changes);
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
            Assert.True(snapshot.Files[RepoPath.CreateKnown(RuleFixture.FixtureBackfillAtomPath)].ContentWasRead);
            Assert.True(snapshot.Files[RepoPath.CreateKnown(RuleFixture.FixtureBackfillSourcePath)].ContentWasRead);
            Assert.False(snapshot.Files[RepoPath.CreateKnown(unrelated)].ContentWasRead);
            return Assert.IsType<CanonicalizationOutcome.Accepted>(
                RepositoryCanonicalizer.Validate(snapshot, policy)).Capability;
        }

        var first = Identity();
        fixture.Files[changedInput] += "\n";
        var second = Identity();

        Assert.NotEqual(first.Sha256, second.Sha256);
    }

    [Fact]
    public void AdmissionIdentityRejectsUnreadRequiredLeanBody()
    {
        var fixture = new RuleFixture();
        var outcome = RepositoryCanonicalizer.Validate(
            ProjectedSnapshot(fixture, RuleFixture.RingPath), fixture.Build().Policy);

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("Required admission input was not read", failure.Message, StringComparison.Ordinal);
    }

    private static RepositorySnapshot ProjectedSnapshot(RuleFixture fixture, string unreadPath) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create(
            fixture.Files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value) is { } entry
                && pair.Key == unreadPath
                    ? entry with { Bytes = [], ContentWasRead = false }
                    : RawRepositoryEntry.FromText(pair.Key, pair.Value))))).Snapshot;

    [Fact]
    public void WholeRepositorySnapshotHasOneStableCanonicalFixedPoint()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build();
        var policy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.Load(
                Encoding.UTF8.GetBytes(TestFileMap.Canonical),
                Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;

        var first = RepositoryCanonicalizer.Validate(context.Current, policy);
        var second = RepositoryCanonicalizer.Validate(context.Current, policy);

        var accepted = Assert.IsType<CanonicalizationOutcome.Accepted>(first);
        var acceptedAgain = Assert.IsType<CanonicalizationOutcome.Accepted>(second);
        Assert.Empty(typeof(CanonicalFixedPoint).GetConstructors());
        Assert.Equal(accepted.Capability.Bytes.ToArray(), acceptedAgain.Capability.Bytes.ToArray());
        Assert.Equal(accepted.Capability.Sha256, acceptedAgain.Capability.Sha256);
        Assert.Equal(policy.FileMapSha256, accepted.Capability.FileMapSha256);
    }

    [Fact]
    public void NoncanonicalStructuredArtifactCannotProduceCapability()
    {
        const string path = "Evidence/D5/S0/Carrier/Result.run.json";
        var fixture = new RuleFixture();
        fixture.Files[path] = "{\"alpha\":1, \"omega\":2}\n";
        var changes = RawChangeSet.Create([path]);
        var context = fixture.Build(changes);
        var policy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.Load(
                Encoding.UTF8.GetBytes(TestFileMap.Canonical),
                Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;

        var outcome = RepositoryCanonicalizer.Validate(context.Current, policy, changes);

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("canonical", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EquivalentFileMapFormattingRetainsCanonicalPolicyIdentity()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/FILEMAP.toml"] = TestFileMap.Canonical.Replace(
            "schema_version = 6", "schema_version=6", StringComparison.Ordinal);
        var context = fixture.Build();
        var policy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.Load(
                Encoding.UTF8.GetBytes(TestFileMap.Canonical),
                Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;

        var outcome = RepositoryCanonicalizer.Validate(
            context.Current,
            policy,
            RawChangeSet.Create(["Meta/FILEMAP.toml"]));

        Assert.IsType<CanonicalizationOutcome.Accepted>(outcome);
    }

    [Fact]
    public void FileMapWriteGateRejectsPolicySemanticMismatch()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/FILEMAP.toml"] = TestFileMap.Canonical.Replace(
            "profile = \"structured-json\"", "profile = \"opaque-text\"", StringComparison.Ordinal);
        var context = fixture.Build();
        var policy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.Load(
                Encoding.UTF8.GetBytes(TestFileMap.Canonical),
                Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;

        var outcome = RepositoryCanonicalizer.Validate(
            context.Current,
            policy,
            RawChangeSet.Create(["Meta/FILEMAP.toml"]));

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("FILEMAP policy differs", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DomainWriteGateRejectsNoncanonicalPolicyBytes()
    {
        var fixture = new RuleFixture();
        fixture.Files["Meta/domains.yaml"] = TestFileMap.Domains.Replace(
            "stratum: S0", "stratum: \"S0\"", StringComparison.Ordinal);
        var context = fixture.Build();
        var policy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.Load(
                Encoding.UTF8.GetBytes(TestFileMap.Canonical),
                Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;

        var outcome = RepositoryCanonicalizer.Validate(
            context.Current,
            policy,
            RawChangeSet.Create(["Meta/domains.yaml"]));

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("domain bytes", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void TrustedPolicyBytesAreNotReplayedForAnUnrelatedCandidateDelta(bool mutateFileMap)
    {
        var fixture = new RuleFixture();
        if (mutateFileMap)
        {
            fixture.Files["Meta/FILEMAP.toml"] = TestFileMap.Canonical.Replace(
                "schema_version = 6",
                "schema_version=5",
                StringComparison.Ordinal);
        }
        else
        {
            fixture.Files["Meta/domains.yaml"] = TestFileMap.Domains.Replace(
                "stratum: S0",
                "stratum: \"S0\"",
                StringComparison.Ordinal);
        }

        var context = fixture.Build();
        var policy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.Load(
                Encoding.UTF8.GetBytes(TestFileMap.Canonical),
                Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;

        var outcome = RepositoryCanonicalizer.Validate(
            context.Current,
            policy,
            RawChangeSet.Create(["notes/unrelated.txt"]));

        Assert.IsType<CanonicalizationOutcome.Accepted>(outcome);
    }

    [Fact]
    public void UnchangedNoncanonicalStructuredArtifactDoesNotReplayItsFixedPoint()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Evidence/D5/S0/Carrier/Result.run.json"] = "{\"alpha\":1, \"omega\":2}\n";
        var changes = RawChangeSet.Create(["notes/unrelated.txt"]);
        var context = fixture.Build(changes);
        var policy = PolicyLoadAssert.Accepted(
            RepositoryPolicyLoader.Load(
                Encoding.UTF8.GetBytes(TestFileMap.Canonical),
                Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;
        var metaClear = Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(changes)).Capability;

        var outcome = AdmissionPipeline.Evaluate(
            context.Current,
            context.Baseline,
            policy,
            context.Lean,
            changes,
            metaClear);

        Assert.True(
            outcome is AdmissionOutcome.Admitted,
            outcome is AdmissionOutcome.RuleRejected rejected
                ? string.Join('\n', rejected.Diagnostics.Select(static item => item.Render()))
                : outcome is AdmissionOutcome.InfrastructureFailure failure
                    ? failure.Message
                    : outcome.GetType().Name);
    }

    [Fact]
    public void CanonicalSnapshotWriterEmitsTheCanonicalDocumentBytes()
    {
        Assert.True(RepoPath.TryCreate("scratch/note.txt", out var path));
        var fileMapSha256 = new string('a', 64);
        var fileSha256 = new string('b', 64);
        var entries = ImmutableArray.Create(new SnapshotEntry(path, 3, fileSha256));
        var expected = Encoding.UTF8.GetBytes(
            "schema_version: 3\n"
            + "input_scope: admission-inputs\n"
            + $"filemap_sha256: {fileMapSha256}\n"
            + "files:\n"
            + "  - path_utf8_hex: 736372617463682f6e6f74652e747874\n"
            + "    length: 3\n"
            + $"    sha256: {fileSha256}\n");

        var actual = CanonicalSnapshotWriter.Write(fileMapSha256, entries);

        Assert.Equal(expected, actual.ToArray());
    }

    [Fact]
    public void YamlSubsetParserRoundTripsInlineEmptyList()
    {
        var parsed = YamlSubsetParser.Parse("sources:\n  - source_id: fresh\n    entries: []\n");
        var root = Assert.IsType<Dictionary<string, object?>>(parsed);
        var sources = Assert.IsType<List<object?>>(root["sources"]);
        var source = Assert.IsType<Dictionary<string, object?>>(sources[0]);
        var entries = Assert.IsType<List<object?>>(source["entries"]);
        Assert.Empty(entries);
    }

    [Fact]
    public void YamlSubsetParserDecodesCanonicalDoubleQuotedEscapes()
    {
        var parsed = Assert.IsType<Dictionary<string, object?>>(
            YamlSubsetParser.Parse("value: \"atom's \\\"quoted\\\" path\\\\leaf\"\n"));

        Assert.Equal("atom's \"quoted\" path\\leaf", parsed["value"]);
    }

}
