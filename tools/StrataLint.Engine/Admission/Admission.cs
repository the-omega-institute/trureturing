using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using Dunet;

namespace StrataLint.Engine;

public sealed class AdmissionCertificate
{
    public const int CurrentFormatVersion = 2;

    private AdmissionCertificate(
        string fingerprint,
        string canonicalSha256,
        ImmutableArray<RuleId> executedRules,
        ImmutableArray<RuleId> skippedRules,
        ImmutableArray<DeferredRule> deferredRules)
    {
        Fingerprint = fingerprint;
        CanonicalSha256 = canonicalSha256;
        ExecutedRules = executedRules;
        SkippedRules = skippedRules;
        DeferredRules = deferredRules;
    }

    public string Fingerprint { get; }

    public string CanonicalSha256 { get; }

    public int FormatVersion => CurrentFormatVersion;

    public ImmutableArray<RuleId> ExecutedRules { get; }

    public ImmutableArray<RuleId> SkippedRules { get; }

    public ImmutableArray<DeferredRule> DeferredRules { get; }

    internal static AdmissionCertificate Create(
        CanonicalFixedPoint canonical,
        CompletedRuleSet rules)
    {
        var material = string.Join(
            '\n',
            new[]
                {
                    $"admission-certificate-v{CurrentFormatVersion}",
                    $"canonical:{canonical.Sha256}",
                }
                .Concat(rules.ExecutedRules.Select(static item => $"executed:{item.Value}"))
                .Concat(rules.SkippedRules.Select(static item => $"skipped:{item.Value}"))
                .Concat(rules.DeferredRules.Select(static item =>
                    $"deferred:{item.RuleId.Value}:{item.CaseId.Value}")))
            + "\n";
        var fingerprint = Convert.ToHexStringLower(
            SHA256.HashData(new UTF8Encoding(false, true).GetBytes(material)));
        return new AdmissionCertificate(
            fingerprint,
            canonical.Sha256,
            rules.ExecutedRules,
            rules.SkippedRules,
            rules.DeferredRules);
    }
}

[Union(EnableImplicitConversions = false)]
public partial record AdmissionOutcome
{
    public partial record Admitted
    {
        internal Admitted(
            AdmissionCertificate certificate,
            ImmutableArray<Diagnostic> observations = default)
        {
            Certificate = certificate ?? throw new ArgumentNullException(nameof(certificate));
            Observations = observations.IsDefault ? [] : observations;
        }

        public AdmissionCertificate Certificate { get; }

        // 非阻断的观察项必须随准入一并交出。判词若产出却无人看得见,那是浮账——
        // CLAUDE.md 第 20 条红线明写「允许 open,不允许浮账」;一个没人看得见的 open
        // 与没有检测无异。此前 admitted 路径整个丢弃 Observe 判词,在 Observe 罕见时
        // 不显眼,而理论卷「尚未消化」改判 Observe 后它就成了承重缺口。
        public ImmutableArray<Diagnostic> Observations { get; }
    }

    public partial record RuleRejected(ImmutableArray<Diagnostic> Diagnostics);

    public partial record InfrastructureFailure(string Message);

    public partial record ProtectedSurfaceVerificationRequired(
        ImmutableArray<Diagnostic> Diagnostics);

    public partial record ProtectedSurfaceChange
    {
        internal ProtectedSurfaceChange(
            AdmissionCertificate contentCertificate,
            MetaChangeSet changeSet,
            ImmutableArray<Diagnostic> sl022Diagnostics,
            ImmutableArray<Diagnostic> observations)
        {
            ContentCertificate = contentCertificate
                ?? throw new ArgumentNullException(nameof(contentCertificate));
            ChangeSet = changeSet ?? throw new ArgumentNullException(nameof(changeSet));
            if (sl022Diagnostics.IsDefaultOrEmpty
                || sl022Diagnostics.Any(static diagnostic =>
                    diagnostic.RuleId != RuleId.CreateKnown(22)
                    || diagnostic.AdmissionEffect is not AdmissionEffect.HumanGate)
                || !ChangeSet.Paths
                    .Select(static path => path.Value)
                    .Order(StringComparer.Ordinal)
                    .SequenceEqual(
                        sl022Diagnostics.Select(static diagnostic => diagnostic.Path)
                            .Order(StringComparer.Ordinal),
                        StringComparer.Ordinal))
            {
                throw new ArgumentException(
                    "Protected-surface outcome requires exact SL-022 diagnostics for its meta change set.",
                    nameof(sl022Diagnostics));
            }

            Sl022Diagnostics = sl022Diagnostics;
            Observations = observations;
        }

        public AdmissionCertificate ContentCertificate { get; }

        public MetaChangeSet ChangeSet { get; }

        public ImmutableArray<Diagnostic> Sl022Diagnostics { get; }

        public ImmutableArray<Diagnostic> Observations { get; }
    }
}

internal static class AdmissionEngine
{
    internal static AdmissionOutcome Decide(
        ValidatedPolicy policy,
        CanonicalFixedPoint canonical,
        AcceptedLeanClosure lean,
        CompletedRuleSet rules,
        MetaEvaluationProfile metaEvaluation)
    {
        ArgumentNullException.ThrowIfNull(policy);
        ArgumentNullException.ThrowIfNull(canonical);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(rules);
        ArgumentNullException.ThrowIfNull(metaEvaluation);

        var rejected = RejectIfNeeded(rules, metaEvaluation);
        if (rejected is not null)
        {
            return rejected;
        }

        var certificate = AdmissionCertificate.Create(canonical, rules);
        var observations = rules.Diagnostics
            .Where(static diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Observe)
            .ToImmutableArray();
        if (metaEvaluation.ProtectedChangeSet is not { } protectedChanges)
        {
            return new AdmissionOutcome.Admitted(certificate, observations);
        }

        var sl022Diagnostics = rules.Diagnostics
            .Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(22))
            .ToImmutableArray();
        try
        {
            return new AdmissionOutcome.ProtectedSurfaceChange(
                certificate,
                protectedChanges,
                sl022Diagnostics,
                observations);
        }
        catch (ArgumentException exception)
        {
            return new AdmissionOutcome.InfrastructureFailure(
                $"SL-022 routing evidence failed closed: {exception.Message}");
        }
    }

    internal static AdmissionOutcome? RejectIfNeeded(
        CompletedRuleSet rules,
        MetaEvaluationProfile metaEvaluation)
    {
        ArgumentNullException.ThrowIfNull(rules);
        ArgumentNullException.ThrowIfNull(metaEvaluation);
        var contentViolations = rules.Diagnostics
            .Where(static item => item.AdmissionEffect is AdmissionEffect.Block or AdmissionEffect.HumanGate)
            .Where(item => metaEvaluation.ProtectedChangeSet is null
                || item.RuleId != RuleId.CreateKnown(22))
            .ToImmutableArray();
        if (contentViolations.Length == 0)
        {
            return null;
        }

        var violationsWithMetaEvidence = rules.Diagnostics
            .Where(static item => item.AdmissionEffect is AdmissionEffect.Block or AdmissionEffect.HumanGate)
            .ToImmutableArray();
        return new AdmissionOutcome.RuleRejected(violationsWithMetaEvidence);
    }
}

public static class AdmissionPipeline
{
    public static AdmissionOutcome Evaluate(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaClear metaClear)
        => Evaluate(
            current,
            baseline,
            policy,
            lean,
            changes,
            MetaEvaluationProfile.ForClear(metaClear),
            verifiedScribeEmissions: null);

    internal static AdmissionOutcome EvaluateWithScribe(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaClear metaClear,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        RepositorySnapshot? forkPoint = null,
        RuleEvaluationMeasure? measureRule = null)
        => Evaluate(
            current,
            baseline,
            policy,
            lean,
            changes,
            MetaEvaluationProfile.ForClear(metaClear),
            verifiedScribeEmissions,
            forkPoint,
            measureRule);

    internal static AdmissionOutcome EvaluateProtectedSurface(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaChangeSet protectedChanges,
        VerifiedScribeEmissions? verifiedScribeEmissions = null,
        RepositorySnapshot? forkPoint = null,
        RuleEvaluationMeasure? measureRule = null)
        => Evaluate(
            current,
            baseline,
            policy,
            lean,
            changes,
            MetaEvaluationProfile.ForProtectedSurface(protectedChanges),
            verifiedScribeEmissions,
            forkPoint,
            measureRule);

    private static AdmissionOutcome Evaluate(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaEvaluationProfile metaEvaluation,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        RepositorySnapshot? forkPoint = null,
        RuleEvaluationMeasure? measureRule = null)
    {
        var context = RuleEvaluationContext.Create(
            current,
            baseline,
            policy,
            lean,
            changes,
            metaEvaluation,
            verifiedScribeEmissions,
            forkPoint);
        return RuleCatalog.Default.Execute(context, measureRule) switch
        {
            RuleExecutionOutcome.Completed completed => Complete(
                current, policy, lean, completed.Capability, metaEvaluation, changes),
            RuleExecutionOutcome.InfrastructureFailure failure =>
                new AdmissionOutcome.InfrastructureFailure(failure.Message),
        };
    }

    private static AdmissionOutcome Complete(
        RepositorySnapshot current,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        CompletedRuleSet rules,
        MetaEvaluationProfile metaEvaluation,
        RawChangeSet changes)
    {
        var rejected = AdmissionEngine.RejectIfNeeded(rules, metaEvaluation);
        if (rejected is not null)
        {
            return rejected;
        }

        return RepositoryCanonicalizer.Validate(current, policy, changes) switch
        {
            CanonicalizationOutcome.Accepted accepted => AdmissionEngine.Decide(
                policy,
                accepted.Capability,
                lean,
                rules,
                metaEvaluation),
            CanonicalizationOutcome.InfrastructureFailure failure =>
                new AdmissionOutcome.InfrastructureFailure(failure.Message),
        };
    }
}
