using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed class CanonicalSnapshotTests
{
    [Fact]
    public void RealRepositoryRegistryHasCanonicalSnapshotFixedPoint()
    {
        var root = TestRepositoryLayout.FindRoot();
        var registry = File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml"));
        var domains = File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"));
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(registry, domains)).Policy;
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([
                new RawRepositoryEntry("Meta/registry.yaml", ImmutableArray.CreateRange(registry)),
                new RawRepositoryEntry("Meta/domains.yaml", ImmutableArray.CreateRange(domains)),
            ]))).Snapshot;

        // No path admission or changed-path filter participates in this byte contract.
        var outcome = RepositoryCanonicalizer.Validate(snapshot, policy);
        Assert.True(outcome is CanonicalizationOutcome.Accepted,
            outcome is CanonicalizationOutcome.InfrastructureFailure failure ? failure.Message : outcome.ToString());
        var first = Assert.IsType<CanonicalizationOutcome.Accepted>(outcome);
        var reloaded = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            policy.CanonicalRegistryBytes.AsSpan(), policy.CanonicalDomainsBytes.AsSpan())).Policy;
        var second = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(snapshot, reloaded));

        Assert.Equal(registry, reloaded.CanonicalRegistryBytes.ToArray());
        Assert.Equal(domains, reloaded.CanonicalDomainsBytes.ToArray());
        Assert.Equal(first.Capability.Bytes.ToArray(), second.Capability.Bytes.ToArray());
        Assert.Equal(first.Capability.Sha256, second.Capability.Sha256);
    }

    [Fact]
    public void WholeRepositorySnapshotHasOneStableCanonicalFixedPoint()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build();
        var policy = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;

        var first = RepositoryCanonicalizer.Validate(context.Current, policy);
        var second = RepositoryCanonicalizer.Validate(context.Current, policy);

        var accepted = Assert.IsType<CanonicalizationOutcome.Accepted>(first);
        var acceptedAgain = Assert.IsType<CanonicalizationOutcome.Accepted>(second);
        Assert.Empty(typeof(CanonicalFixedPoint).GetConstructors());
        Assert.Equal(accepted.Capability.Bytes.ToArray(), acceptedAgain.Capability.Bytes.ToArray());
        Assert.Equal(accepted.Capability.Sha256, acceptedAgain.Capability.Sha256);
        Assert.Equal(policy.RegistrySha256, accepted.Capability.RegistrySha256);
    }

    [Fact]
    public void NoncanonicalStructuredArtifactCannotProduceCapability()
    {
        const string path = "Evidence/D5/S0/Carrier/Result.run.json";
        var fixture = new RuleFixture();
        fixture.Files[path] = "{\"alpha\":1, \"omega\":2}\n";
        var changes = RawChangeSet.Create([path]);
        var context = fixture.Build(changes);
        var policy = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;

        var outcome = RepositoryCanonicalizer.Validate(context.Current, policy, changes);

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("canonical", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void CanonicalSnapshotWriteGateRejectsNoncanonicalPolicyBytes(bool mutateRegistry)
    {
        var fixture = new RuleFixture();
        if (mutateRegistry)
        {
            fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical.Replace(
                "schema_version: 1",
                "schema_version: \"1\"",
                StringComparison.Ordinal);
        }
        else
        {
            fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains.Replace(
                "stratum: S0",
                "stratum: \"S0\"",
                StringComparison.Ordinal);
        }
        var context = fixture.Build();
        var policy = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;

        var changedPath = mutateRegistry ? "Meta/registry.yaml" : "Meta/domains.yaml";
        var outcome = RepositoryCanonicalizer.Validate(
            context.Current,
            policy,
            RawChangeSet.Create([changedPath]));

        var failure = Assert.IsType<CanonicalizationOutcome.InfrastructureFailure>(outcome);
        Assert.Contains(
            mutateRegistry ? "registry bytes" : "domain bytes",
            failure.Message,
            StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void TrustedPolicyBytesAreNotReplayedForAnUnrelatedCandidateDelta(bool mutateRegistry)
    {
        var fixture = new RuleFixture();
        if (mutateRegistry)
        {
            fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical.Replace(
                "schema_version: 1",
                "schema_version: \"1\"",
                StringComparison.Ordinal);
        }
        else
        {
            fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains.Replace(
                "stratum: S0",
                "stratum: \"S0\"",
                StringComparison.Ordinal);
        }

        var context = fixture.Build();
        var policy = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;

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
        var policy = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
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
        var registrySha256 = new string('a', 64);
        var fileSha256 = new string('b', 64);
        var entries = ImmutableArray.Create(new SnapshotEntry(path, 3, fileSha256));
        var expected = Encoding.UTF8.GetBytes(
            "schema_version: 1\n"
            + $"registry_sha256: {registrySha256}\n"
            + "files:\n"
            + "  - path_utf8_hex: 736372617463682f6e6f74652e747874\n"
            + "    length: 3\n"
            + $"    sha256: {fileSha256}\n");

        var actual = CanonicalSnapshotWriter.Write(registrySha256, entries);

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
