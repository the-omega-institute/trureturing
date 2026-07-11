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
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
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
            context.MetaClear);

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
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
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
            context.MetaClear);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == RuleId.CreateKnown(6));
    }
}
