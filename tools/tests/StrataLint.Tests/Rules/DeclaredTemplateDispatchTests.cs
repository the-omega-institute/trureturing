using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DeclaredTemplateDispatchTests
{
    [Fact]
    public void declared_template_rule_required()
    {
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId,
            DeclaredTemplateBindingRuleTests.Delta()).Diagnostics;
        Assert.Contains(diagnostics, diagnostic => diagnostic.AdmissionEffect == AdmissionEffect.Block
            && diagnostic.Message.StartsWith("DTR-Undeclared ", StringComparison.Ordinal));
    }

    [Fact]
    public void dispatched_validated_registration_observed()
    {
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId,
            DeclaredTemplateBindingRuleTests.Delta(declared: true, added: true)).Diagnostics;
        var finding = Assert.Single(diagnostics, diagnostic => diagnostic.Message.StartsWith("DTR-", StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Observe, finding.AdmissionEffect);
        Assert.StartsWith("DTR-Declared ", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void unchanged_registration_not_dispatched()
    {
        var diagnostics = RuleCatalog.Default.EvaluateSingle(UtilityAdmissionTestSupport.UtilityRuleId,
            DeclaredTemplateBindingRuleTests.Delta(changed: false, missing: true)).Diagnostics;
        Assert.DoesNotContain(diagnostics, diagnostic => diagnostic.Message.StartsWith("DTR-", StringComparison.Ordinal));
    }
}
