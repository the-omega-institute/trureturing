using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Policy.Tests;

public sealed class RegisteredPolicyTests
{
    [Theory]
    [InlineData("Meta/judge-seed.json")]
    [InlineData("Meta/package-materials.json")]
    public void RealRepositoryMetadataRegistrationsAreAdmissible(string value)
    {
        var path = RepoPath.CreateKnown(value);
        var policy = RealRepositoryPolicy();

        Assert.Null(RepositoryPathPolicy.Validate(path, policy));
        Assert.Contains(path, policy.GovernanceDocuments);
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
    }

    [Theory]
    [InlineData("Meta/unregistered.json")]
    [InlineData("Meta/judge-seed-extra.json")]
    [InlineData("Meta/package-materials-extra.json")]
    public void RealRepositoryMetadataRegistrationRejectsUnregisteredNeighbors(string value)
    {
        var path = RepoPath.CreateKnown(value);
        var policy = RealRepositoryPolicy();

        var issue = Assert.IsType<RepositoryPathIssue>(RepositoryPathPolicy.Validate(path, policy));

        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal(value, issue.Path);
        Assert.Equal("unknown Meta artifact", issue.Message);
        Assert.DoesNotContain(path, policy.GovernanceDocuments);
    }

    private static ValidatedPolicy RealRepositoryPolicy()
    {
        var root = TestRepositoryLayout.FindRoot();
        return RegistryLoadAssert.Accepted(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml")))).Policy;
    }

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

    [Theory]
    [InlineData("Meta/judge-seed.json", true)]
    [InlineData("Meta/package-materials.json", true)]
    [InlineData("Meta/unregistered.json", false)]
    public void CurrentChecksRealRepositoryMetadataRegistrationWithoutHistory(string path, bool registered)
    {
        var registry = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/registry.yaml"));
        var domains = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/domains.yaml"));
        var material = registered
            ? TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(path))
            : "{}\n";
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([
                RawRepositoryEntry.FromText("Meta/registry.yaml", registry),
                RawRepositoryEntry.FromText("Meta/domains.yaml", domains),
                RawRepositoryEntry.FromText(path, material),
            ]))).Snapshot;
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry), Encoding.UTF8.GetBytes(domains))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(
            snapshot, LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()))).Capability;

        var current = CurrentRuleContext.Create(snapshot, policy, lean);
        var outcome = AdmissionPipeline.CheckCurrent(current);
        Assert.True(outcome is RuleExecutionOutcome.Completed,
            outcome is RuleExecutionOutcome.InfrastructureFailure failure ? failure.Message : outcome.ToString());
        var result = Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
        Assert.Contains(RuleId.CreateKnown(15), result.ExecutedRules);
        var pathFindings = result.Diagnostics.Where(finding => finding.RuleId == RuleId.CreateKnown(0)).ToArray();

        if (registered)
        {
            Assert.Empty(pathFindings);
        }
        else
        {
            var finding = Assert.Single(pathFindings);
            Assert.Equal("SL-000", finding.RuleId.Value);
            Assert.Equal(path, finding.Path);
            Assert.Equal("unknown Meta artifact", finding.Message);
            Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
        }
    }

    [Fact]
    public void LeanReportConfigurationIsAdmittedWithItsRuntimeVerifier()
    {
        const string path = "lean-report-inputs.json";
        var root = TestRepositoryLayout.FindRoot();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"))));
        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), registry.Policy));
        var manifest = FileMapLoader.LoadRepository(root);
        var entry = Assert.Single(manifest.Match(path));
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Equal("LeanReportSelection", Assert.Single(entry.VerifiedBy));
        Assert.Contains("lean-report", entry.Require);
        Assert.DoesNotContain(FileMapPolicy.InspectRepository(root), finding =>
            finding.Path == path && finding.Code is "FILEMAP-DATA-VERIFIER" or "FILEMAP-DATA-VERIFIER-DANGLING");
    }

    [Theory]
    [InlineData("lean-report")]
    [InlineData("scribe-content")]
    public void ReportConsumerScopesAreAdmittedByRegisteredRepositoryPolicy(string scope)
    {
        var root = TestRepositoryLayout.FindRoot();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"))));
        var path = $"Meta/ReportConsumers/{scope}.json";

        Assert.Null(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), registry.Policy));
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
        var root = TestRepositoryLayout.FindRoot();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            File.ReadAllBytes(Path.Combine(root, "Meta/registry.yaml")),
            File.ReadAllBytes(Path.Combine(root, "Meta/domains.yaml"))));

        var issue = RepositoryPathPolicy.Validate(RepoPath.CreateKnown(path), registry.Policy);

        Assert.NotNull(issue);
        Assert.Equal("SL-000", issue.RuleId.Value);
        Assert.Equal("unknown Meta artifact", issue.Message);
    }

}
