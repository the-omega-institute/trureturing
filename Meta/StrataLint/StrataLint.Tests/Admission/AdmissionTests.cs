using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AdmissionTests
{
    [Fact]
    public void FivePrivateCapabilitiesAreRequiredForAdmission()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context));
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));

        var outcome = AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed.Capability,
            context.MetaEvaluation);

        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.NotEmpty(admitted.Certificate.Fingerprint);
        Assert.Empty(typeof(ValidatedPolicy).GetConstructors());
        Assert.Empty(typeof(CanonicalFixedPoint).GetConstructors());
        Assert.Empty(typeof(AcceptedLeanClosure).GetConstructors());
        Assert.Empty(typeof(CompletedRuleSet).GetConstructors());
        Assert.Empty(typeof(MetaClear).GetConstructors());
        Assert.Empty(typeof(AdmissionCertificate).GetConstructors());
    }

    [Fact]
    public void BlockingDiagnosticCannotProduceAdmissionCertificate()
    {
        var fixture = new RuleFixture();
        fixture.Apply("badge");
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context));
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));

        var outcome = AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed.Capability,
            context.MetaEvaluation);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == RuleId.CreateKnown(6));
    }

    [Fact]
    public void NonSl022TrustGateIsAContentViolation()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));
        var descriptor = RuleCatalog.Default.Descriptors[6];
        var completed = CompletedRuleSet.Create(
            ImmutableArray.Create(new Diagnostic(
                descriptor.Id,
                descriptor.Title,
                descriptor.DisplaySeverity,
                descriptor.AdmissionEffect,
                RuleFixture.BlueprintPath,
                "fixture trust gate")),
            ImmutableArray<DeferredRule>.Empty,
            ImmutableArray.Create(descriptor.Id));

        var outcome = AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed,
            context.MetaEvaluation);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == descriptor.Id);
    }

    [Fact]
    public void ProtectedProfileRejectsOtherTrustGateAndPreservesSl022()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));
        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(
            BootstrapGate.Evaluate(RawChangeSet.Create(new[]
            {
                RuleFixture.SyntheticProtectedPath,
            })));
        var trustGate = RuleCatalog.Default.Descriptors[6];
        var sl022 = Assert.Single(BootstrapGate.CreateSl022Diagnostics(verification.ChangeSet));
        Assert.Equal(
            "protected-surface change requires base-owned conservative-extension verification",
            sl022.Message);
        var completed = CompletedRuleSet.Create(
            ImmutableArray.Create(
                new Diagnostic(
                    trustGate.Id,
                    trustGate.Title,
                    trustGate.DisplaySeverity,
                    trustGate.AdmissionEffect,
                    RuleFixture.BlueprintPath,
                    "fixture trust gate"),
                sl022),
            ImmutableArray<DeferredRule>.Empty,
            ImmutableArray.Create(trustGate.Id, sl022.RuleId));

        var outcome = AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed,
            MetaEvaluationProfile.ForProtectedSurface(verification.ChangeSet));

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == trustGate.Id);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == RuleId.CreateKnown(22));
    }

    [Fact]
    public void ProtectedProfileFailsClosedWhenSl022EvidenceIsMissing()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));
        var verification = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(
            BootstrapGate.Evaluate(RawChangeSet.Create(new[]
            {
                RuleFixture.SyntheticProtectedPath,
            })));
        var completed = CompletedRuleSet.Create(
            ImmutableArray<Diagnostic>.Empty,
            ImmutableArray<DeferredRule>.Empty,
            ImmutableArray.Create(RuleId.CreateKnown(22)));

        var outcome = AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed,
            MetaEvaluationProfile.ForProtectedSurface(verification.ChangeSet));

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("SL-022 routing evidence failed closed", failure.Message, StringComparison.Ordinal);
    }
}
