using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AdmissionTests
{
    [Fact]
    public void CertificateRecordsExecutedSkippedAndDeferredRulesWithoutMasquerading()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.BlueprintPath]));
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));

        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed,
            context.MetaEvaluation));

        Assert.Equal(2, CertificateFormatVersion(admitted.Certificate));
        Assert.Equal(completed.ExecutedRules, admitted.Certificate.ExecutedRules);
        var completedSkipped = SkippedRules(completed);
        var certificateSkipped = SkippedRules(admitted.Certificate);
        Assert.Equal(completedSkipped, certificateSkipped);
        Assert.Equal(completed.DeferredRules, admitted.Certificate.DeferredRules);
        Assert.Empty(admitted.Certificate.ExecutedRules.Intersect(certificateSkipped));
        Assert.Empty(admitted.Certificate.ExecutedRules.Intersect(
            admitted.Certificate.DeferredRules.Select(static item => item.RuleId)));
        Assert.Empty(certificateSkipped.Intersect(
            admitted.Certificate.DeferredRules.Select(static item => item.RuleId)));
        Assert.Equal(
            RuleCatalog.Default.Descriptors
                .Select(static item => item.Id)
                .OrderBy(static item => item.Value, StringComparer.Ordinal),
            admitted.Certificate.ExecutedRules
                .Concat(certificateSkipped)
                .Concat(admitted.Certificate.DeferredRules.Select(static item => item.RuleId))
                .OrderBy(static item => item.Value, StringComparer.Ordinal));
    }

    [Fact]
    public void CertificateFingerprintBindsRuleDispositionAndFormatVersion()
    {
        var canonical = CanonicalForCertificate();
        var rule = RuleId.CreateKnown(1);
        var executed = CreateCompletedRuleSet([rule], []);
        var skipped = CreateCompletedRuleSet([], [rule]);

        var executedCertificate = AdmissionCertificate.Create(canonical, executed);
        var skippedCertificate = AdmissionCertificate.Create(canonical, skipped);

        Assert.NotEqual(executedCertificate.Fingerprint, skippedCertificate.Fingerprint);
        Assert.Equal(2, CertificateFormatVersion(executedCertificate));
        Assert.Equal(2, CertificateFormatVersion(skippedCertificate));
    }

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
        var descriptor = RuleCatalog.Default.Descriptors.Single(item =>
            item.Id == RuleId.CreateKnown(7));
        var completed = CompletedRuleSet.Create(
            ImmutableArray.Create(new Diagnostic(
                descriptor.Id,
                descriptor.Title,
                descriptor.DisplaySeverity,
                descriptor.AdmissionEffect,
                RuleFixture.BlueprintPath,
                "fixture trust gate")),
            ImmutableArray<DeferredRule>.Empty,
            ImmutableArray.Create(descriptor.Id),
            ImmutableArray<RuleId>.Empty);

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
        var trustGate = RuleCatalog.Default.Descriptors.Single(item =>
            item.Id == RuleId.CreateKnown(7));
        var sl022 = Assert.Single(BootstrapGate.CreateSl022Diagnostics(verification.ChangeSet));
        Assert.Equal(
            "protected-surface change detected (SL-022)",
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
            ImmutableArray.Create(trustGate.Id, sl022.RuleId),
            ImmutableArray<RuleId>.Empty);

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
            ImmutableArray.Create(RuleId.CreateKnown(22)),
            ImmutableArray<RuleId>.Empty);

        var outcome = AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed,
            MetaEvaluationProfile.ForProtectedSurface(verification.ChangeSet));

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("SL-022 routing evidence failed closed", failure.Message, StringComparison.Ordinal);
    }

    private static CanonicalFixedPoint CanonicalForCertificate()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        return Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy)).Capability;
    }

    private static CompletedRuleSet CreateCompletedRuleSet(
        ImmutableArray<RuleId> executedRules,
        ImmutableArray<RuleId> skippedRules)
    {
        var create = typeof(CompletedRuleSet).GetMethod(
            "Create",
            System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.NonPublic,
            binder: null,
            [
                typeof(ImmutableArray<Diagnostic>),
                typeof(ImmutableArray<DeferredRule>),
                typeof(ImmutableArray<RuleId>),
                typeof(ImmutableArray<RuleId>),
            ],
            modifiers: null);
        Assert.NotNull(create);
        return Assert.IsType<CompletedRuleSet>(create!.Invoke(
            null,
            [ImmutableArray<Diagnostic>.Empty, ImmutableArray<DeferredRule>.Empty, executedRules, skippedRules]));
    }

    private static int CertificateFormatVersion(AdmissionCertificate certificate)
    {
        var property = typeof(AdmissionCertificate).GetProperty("FormatVersion");
        Assert.NotNull(property);
        return Assert.IsType<int>(property!.GetValue(certificate));
    }

    private static ImmutableArray<RuleId> SkippedRules(object value)
    {
        var property = value.GetType().GetProperty("SkippedRules");
        Assert.NotNull(property);
        return Assert.IsType<ImmutableArray<RuleId>>(property!.GetValue(value));
    }
}
