using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateDispatchTests
{
    private static string Inactive => Encoding.UTF8.GetString(InformationTemplateDebtStore.WriteActivation(
        new(InformationTemplateDebtStoreTests.Seed, false)).AsSpan());

    [Fact]
    public void declared_template_rule_required()
    {
        var fixture = new RuleFixture();
        fixture.Baseline[InformationTemplateDebtStore.ActivationPath] = Inactive;
        fixture.Files.Remove(InformationTemplateDebtStore.ActivationPath);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId,
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(InformationTemplateDebtStore.ActivationPath, RawChangeKind.Deleted)]))).Diagnostics;
        Assert.Contains(diagnostics, diagnostic => diagnostic.AdmissionEffect == AdmissionEffect.Block
            && diagnostic.Message == "DTR-Required activation mechanism deleted");
    }

    [Fact]
    public void dispatched_complete_rule_accepted()
    {
        var fixture = new RuleFixture();
        fixture.Files[InformationTemplateDebtStore.ActivationPath] = Inactive;
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId,
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(InformationTemplateDebtStore.ActivationPath, RawChangeKind.Added)]))).Diagnostics;
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.AdmissionEffect == AdmissionEffect.Block);
        Assert.Contains(diagnostics, diagnostic => diagnostic.AdmissionEffect == AdmissionEffect.Observe
            && diagnostic.Message == "DTR-Inactive installation; protected activation is absent");
    }

    [Fact]
    public void candidate_activation_cannot_install_an_active_mechanism()
    {
        var fixture = new RuleFixture();
        fixture.Files[InformationTemplateDebtStore.ActivationPath] = Inactive.Replace("false", "true", StringComparison.Ordinal);
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId,
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(InformationTemplateDebtStore.ActivationPath, RawChangeKind.Added)]))).Diagnostics;
        Assert.Contains(diagnostics, diagnostic => diagnostic.AdmissionEffect == AdmissionEffect.Block
            && diagnostic.Message.Contains("DTR-Activation: installation must be inactive and row-free", StringComparison.Ordinal));
    }
}
