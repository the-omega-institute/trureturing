using System.Text;
using StrataLint.Configuration;
using StrataLint.Engine;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.RepositoryConfiguration.Tests;

public sealed class CurrentMetadataRegistrationTests
{
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

}
