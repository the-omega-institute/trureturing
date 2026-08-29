using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class CapabilityConstructionTests
{
    private static readonly string[] CapabilityTypes =
    [
        "StrataLint.Engine.AcceptedLeanClosure",
        "StrataLint.Engine.AdmissionCertificate",
        "StrataLint.Engine.AdmissionOutcome+Admitted",
        "StrataLint.Engine.AdmissionOutcome+ProtectedSurfaceChange",
        "StrataLint.Engine.BootstrapOutcome+Clear",
        "StrataLint.Engine.CanonicalFixedPoint",
        "StrataLint.Engine.CanonicalizationOutcome+Accepted",
        "StrataLint.Engine.CompletedRuleSet",
        "StrataLint.Engine.FrozenLedgerConsistent",
        "StrataLint.Engine.FrozenLedgerValidationOutcome+Accepted",
        "StrataLint.Engine.FrozenMaterialCatalog",
        "StrataLint.Engine.FrozenMaterialOutcome+Accepted",
        "StrataLint.Engine.LeanValidationOutcome+Accepted",
        "StrataLint.Engine.MetaClear",
        "StrataLint.Engine.RegistryLoadOutcome+Accepted",
        "StrataLint.Engine.RevocationEvidenceValidationOutcome+Accepted",
        "StrataLint.Engine.RevocationPlan",
        "StrataLint.Engine.RevocationPlanOutcome+Accepted",
        "StrataLint.Engine.RevocationReceiptStoreOutcome+Accepted",
        "StrataLint.Engine.RuleExecutionOutcome+Completed",
        "StrataLint.Engine.TowerValidationOutcome+Accepted",
        "StrataLint.Engine.TrustedRevocationReceiptStore",
        "StrataLint.Engine.ValidatedManifest",
        "StrataLint.Engine.ValidatedPolicy",
        "StrataLint.Engine.ValidatedRevocationEvidence",
        "StrataLint.Engine.ValidatedTowerManifest",
    ];

    [Fact]
    public void EngineCapabilityTypesAreExplicitAndCannotBePubliclyConstructed()
    {
        var assembly = typeof(AdmissionPipeline).Assembly;
        Assert.Equal(CapabilityTypes, CapabilityPolicy.EnumerateNames(assembly));
        Assert.Empty(CapabilityPolicy.PubliclyConstructible(assembly.GetExportedTypes()));
    }

    [Fact]
    public void PublicCertificateConstructorIsRejectedByTheRedFixture()
    {
        var rejected = Assert.Single(
            CapabilityPolicy.PubliclyConstructible([typeof(LeakyCertificate)]));

        Assert.Equal(typeof(LeakyCertificate).FullName, rejected);
    }
}

public sealed class LeakyCertificate;
