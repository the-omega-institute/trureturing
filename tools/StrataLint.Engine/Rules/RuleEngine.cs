using System.Collections.Immutable;
using Dunet;

namespace StrataLint.Engine;

public sealed record Diagnostic(
    RuleId RuleId,
    string Title,
    DisplaySeverity DisplaySeverity,
    AdmissionEffect AdmissionEffect,
    string Path,
    string Message)
{
    public string Render() => $"{RuleId.Value} {Path}: {Message}";
}

public sealed record DeferredRule(RuleId RuleId, CaseId CaseId, string Title);

internal sealed record RuleFinding(string Path, string Message, AdmissionEffect? Effect = null);

internal interface IRepositoryRule
{
    bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context);

    ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context);
}

internal sealed class RuleApplicabilityContext
{
    private RuleApplicabilityContext(RepositorySnapshot current, ValidatedPolicy policy)
    {
        Current = current;
        Policy = policy;
    }

    internal RepositorySnapshot Current { get; }

    internal ValidatedPolicy Policy { get; }

    internal static RuleApplicabilityContext Create(
        RepositorySnapshot current,
        ValidatedPolicy policy) =>
        new(current, policy);
}

internal sealed record SingleRuleEvaluation(
    ImmutableArray<Diagnostic> Diagnostics,
    CaseId? DeferredCase);

public sealed class CompletedRuleSet
{
    private CompletedRuleSet(
        ImmutableArray<Diagnostic> diagnostics,
        ImmutableArray<DeferredRule> deferredRules,
        ImmutableArray<RuleId> executedRules)
    {
        Diagnostics = diagnostics;
        DeferredRules = deferredRules;
        ExecutedRules = executedRules;
    }

    public ImmutableArray<Diagnostic> Diagnostics { get; }

    public ImmutableArray<DeferredRule> DeferredRules { get; }

    public ImmutableArray<RuleId> ExecutedRules { get; }

    internal static CompletedRuleSet Create(
        ImmutableArray<Diagnostic> diagnostics,
        ImmutableArray<DeferredRule> deferredRules,
        ImmutableArray<RuleId> executedRules) =>
        new(diagnostics, deferredRules, executedRules);
}

[Union(EnableImplicitConversions = false)]
public partial record RuleExecutionOutcome
{
    public partial record Completed
    {
        internal Completed(CompletedRuleSet capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public CompletedRuleSet Capability { get; }
    }

    public partial record InfrastructureFailure(string Message);
}

internal sealed class RuleEvaluationContext
{
    private RuleEvaluationContext(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        RepositorySnapshot forkPoint,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaEvaluationProfile metaEvaluation,
        VerifiedScribeEmissions? verifiedScribeEmissions)
    {
        Current = current;
        Baseline = baseline;
        ForkPoint = forkPoint;
        Policy = policy;
        Lean = lean;
        Changes = changes;
        MetaEvaluation = metaEvaluation;
        VerifiedScribeEmissions = verifiedScribeEmissions;
    }

    internal RepositorySnapshot Current { get; }

    internal RepositorySnapshot Baseline { get; }

    // 「旧侧」有两个语义,不可共用一棵树:
    //   Baseline  —— 候选在扩展哪个**受保护状态**(= protected base);保守比较用它。
    //   ForkPoint —— 候选**自己出发的那一点**(= merge-base);append-only 保留性检查用它,
    //                问的是「候选有没有删掉它出发时就有的东西」。
    // 用 Baseline 回答第二个问题,会把 dev 在候选分叉之后追加的条目读成候选的删除
    // (PR #1150 实测:`Golden/Frozen/accepted/` 的 4 个证书;近 60 次合并中 63% 会追加)。
    // 默认等于 Baseline —— 那正是引入本字段之前的行为,故对既有调用点零语义变化。
    internal RepositorySnapshot ForkPoint { get; }

    internal ValidatedPolicy Policy { get; }

    internal AcceptedLeanClosure Lean { get; }

    internal RawChangeSet Changes { get; }

    internal MetaEvaluationProfile MetaEvaluation { get; }

    internal VerifiedScribeEmissions? VerifiedScribeEmissions { get; }

    internal static RuleEvaluationContext Create(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaClear metaClear,
        VerifiedScribeEmissions? verifiedScribeEmissions = null,
        RepositorySnapshot? forkPoint = null) =>
        Create(
            current,
            baseline,
            policy,
            lean,
            changes,
            MetaEvaluationProfile.ForClear(metaClear),
            verifiedScribeEmissions,
            forkPoint);

    internal static RuleEvaluationContext Create(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaEvaluationProfile metaEvaluation,
        VerifiedScribeEmissions? verifiedScribeEmissions = null,
        RepositorySnapshot? forkPoint = null) =>
        new(
            current,
            baseline,
            forkPoint ?? baseline,
            policy,
            lean,
            changes,
            metaEvaluation,
            verifiedScribeEmissions);
}

internal sealed class RepositoryRule(
    Func<RepositoryFile, RuleApplicabilityContext, bool> appliesTo,
    Func<RuleEvaluationContext, ImmutableArray<RuleFinding>> evaluate) : IRepositoryRule
{
    public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) =>
        appliesTo(artifact, context);

    public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
        evaluate(context);
}
