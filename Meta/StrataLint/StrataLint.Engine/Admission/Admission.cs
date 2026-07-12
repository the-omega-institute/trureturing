using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using Dunet;

namespace StrataLint.Engine;

public sealed class AdmissionCertificate
{
    private AdmissionCertificate(
        string fingerprint,
        string canonicalSha256,
        ImmutableArray<RuleId> executedRules,
        ImmutableArray<DeferredRule> deferredRules)
    {
        Fingerprint = fingerprint;
        CanonicalSha256 = canonicalSha256;
        ExecutedRules = executedRules;
        DeferredRules = deferredRules;
    }

    public string Fingerprint { get; }

    public string CanonicalSha256 { get; }

    public ImmutableArray<RuleId> ExecutedRules { get; }

    public ImmutableArray<DeferredRule> DeferredRules { get; }

    internal static AdmissionCertificate Create(
        CanonicalFixedPoint canonical,
        CompletedRuleSet rules)
    {
        var material = string.Join(
            '\n',
            new[] { canonical.Sha256 }
                .Concat(rules.ExecutedRules.Select(static item => item.Value))
                .Concat(rules.DeferredRules.Select(static item => $"{item.RuleId.Value}:{item.CaseId.Value}")))
            + "\n";
        var fingerprint = Convert.ToHexStringLower(
            SHA256.HashData(new UTF8Encoding(false, true).GetBytes(material)));
        return new AdmissionCertificate(
            fingerprint,
            canonical.Sha256,
            rules.ExecutedRules,
            rules.DeferredRules);
    }
}

[Union(EnableImplicitConversions = false)]
public partial record AdmissionOutcome
{
    public partial record Admitted
    {
        internal Admitted(AdmissionCertificate certificate) =>
            Certificate = certificate ?? throw new ArgumentNullException(nameof(certificate));

        public AdmissionCertificate Certificate { get; }
    }

    public partial record RuleRejected(ImmutableArray<Diagnostic> Diagnostics);

    public partial record InfrastructureFailure(string Message);

    public partial record HumanReviewRequired(ImmutableArray<Diagnostic> Diagnostics);
}

internal static class AdmissionEngine
{
    internal static AdmissionOutcome Decide(
        ValidatedPolicy policy,
        CanonicalFixedPoint canonical,
        AcceptedLeanClosure lean,
        CompletedRuleSet rules,
        MetaClear metaClear)
    {
        ArgumentNullException.ThrowIfNull(policy);
        ArgumentNullException.ThrowIfNull(canonical);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(rules);
        ArgumentNullException.ThrowIfNull(metaClear);

        var rejected = RejectIfNeeded(rules);
        if (rejected is not null)
        {
            return rejected;
        }

        return new AdmissionOutcome.Admitted(AdmissionCertificate.Create(canonical, rules));
    }

    internal static AdmissionOutcome? RejectIfNeeded(CompletedRuleSet rules)
    {
        var humanGates = rules.Diagnostics
            .Where(static item => item.AdmissionEffect is AdmissionEffect.HumanGate)
            .ToImmutableArray();
        if (humanGates.Length > 0)
        {
            return new AdmissionOutcome.HumanReviewRequired(humanGates);
        }

        var blocks = rules.Diagnostics
            .Where(static item => item.AdmissionEffect is AdmissionEffect.Block)
            .ToImmutableArray();
        if (blocks.Length > 0)
        {
            return new AdmissionOutcome.RuleRejected(blocks);
        }

        return null;
    }
}

public static class AdmissionPipeline
{
    public static AdmissionOutcome Evaluate(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        RawChangeSet changes,
        MetaClear metaClear)
    {
        var context = RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            lean,
            baselineLean,
            changes,
            metaClear);
        return RuleCatalog.Default.Execute(context) switch
        {
            RuleExecutionOutcome.Completed completed => Complete(
                current, policy, lean, completed.Capability, metaClear),
            RuleExecutionOutcome.InfrastructureFailure failure =>
                new AdmissionOutcome.InfrastructureFailure(failure.Message),
        };
    }

    private static AdmissionOutcome Complete(
        RepositorySnapshot current,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        CompletedRuleSet rules,
        MetaClear metaClear)
    {
        var rejected = AdmissionEngine.RejectIfNeeded(rules);
        if (rejected is not null)
        {
            return rejected;
        }

        return RepositoryCanonicalizer.Validate(current, policy) switch
        {
            CanonicalizationOutcome.Accepted accepted => AdmissionEngine.Decide(
                policy,
                accepted.Capability,
                lean,
                rules,
                metaClear),
            CanonicalizationOutcome.InfrastructureFailure failure =>
                new AdmissionOutcome.InfrastructureFailure(failure.Message),
        };
    }
}
