using System.Collections.Immutable;
using System.Reflection;
using Dunet;

namespace StrataLint.Engine;

internal static class BaseFactImpact
{
    internal static bool RuleImplementationChanged(RawChangeSet changes) =>
        changes.Paths.Any(static path =>
            StrataLintEngineBuildInputs.ContainsRuleImplementation(path.Value));

    internal static bool IsAffected(
        RawChangeSet changes,
        bool ruleImplementationChanged,
        string path) =>
        ruleImplementationChanged
        || changes.Paths.Any(change => string.Equals(change.Value, path, StringComparison.Ordinal));
}

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

internal delegate ImmutableArray<RuleFinding> RuleEvaluationMeasure(
    RuleId ruleId,
    AdmissionEffect admissionEffect,
    Func<ImmutableArray<RuleFinding>> evaluate);

internal enum FindingEdgeKind
{
    Local,
    Interaction,
}

internal sealed record FindingEdgeDescriptor(
    string Id,
    Type OwnerType,
    string MemberName,
    FindingEdgeKind Kind)
{
    internal string DisplayName => $"{OwnerType.FullName}.{MemberName}";

    internal static FindingEdgeDescriptor From(Delegate evaluator, FindingEdgeKind kind) =>
        From(evaluator.Method, kind);

    internal static FindingEdgeDescriptor From(
        Type ownerType,
        string memberName,
        FindingEdgeKind kind) =>
        new(
            FindingEdgeId.For(ownerType, memberName),
            ownerType,
            memberName,
            kind);

    internal static ImmutableArray<FindingEdgeDescriptor> Discover(Type ownerType) =>
        ownerType
            .GetMethods(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic)
            .Select(method => (method, attribute: method.GetCustomAttribute<FindingEdgeAttribute>()))
            .Where(static item => item.attribute is not null)
            .OrderBy(static item => item.method.Name, StringComparer.Ordinal)
            .Select(static item => From(item.method, item.attribute!.Kind))
            .ToImmutableArray();

    private static FindingEdgeDescriptor From(MethodInfo method, FindingEdgeKind kind) =>
        From(method.DeclaringType ?? throw new InvalidOperationException("Finding edge has no declaring type."), method.Name, kind);
}

[AttributeUsage(AttributeTargets.Method, AllowMultiple = false)]
internal sealed class FindingEdgeAttribute(FindingEdgeKind kind) : Attribute
{
    internal FindingEdgeKind Kind { get; } = kind;
}

[AttributeUsage(AttributeTargets.Class, AllowMultiple = false)]
internal sealed class FindingEdgeProviderAttribute(int ruleNumber) : Attribute
{
    internal int RuleNumber { get; } = ruleNumber;
}

internal static class FindingEdgeId
{
    internal static string For(Type ownerType, string memberName) =>
        $"{ownerType.FullName ?? ownerType.Name}.{memberName}";
}

internal sealed record RegisteredFindingEdge(
    RuleId RuleId,
    FindingEdgeDescriptor Edge)
{
    internal string DisplayName => $"{RuleId.Value}:{Edge.DisplayName}";
}

internal sealed record FindingEdgeDefinition(
    Func<RuleEvaluationContext, ImmutableArray<RuleFinding>> Evaluate,
    FindingEdgeKind Kind)
{
    internal FindingEdgeDescriptor Descriptor => FindingEdgeDescriptor.From(Evaluate, Kind);
}

internal interface IRepositoryRule
{
    ImmutableArray<FindingEdgeDescriptor> FindingEdges => [];

    bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context);

    bool IsAffectedBy(RuleEvaluationContext context) => true;

    ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context);

    ImmutableArray<RuleFinding> EvaluateCandidateDelta(RuleEvaluationContext context) =>
        Evaluate(context);
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
        ImmutableArray<RuleId> executedRules,
        ImmutableArray<RuleId> skippedRules)
    {
        Diagnostics = diagnostics;
        DeferredRules = deferredRules;
        ExecutedRules = executedRules;
        SkippedRules = skippedRules;
    }

    public ImmutableArray<Diagnostic> Diagnostics { get; }

    public ImmutableArray<DeferredRule> DeferredRules { get; }

    public ImmutableArray<RuleId> ExecutedRules { get; }

    public ImmutableArray<RuleId> SkippedRules { get; }

    internal static CompletedRuleSet Create(
        ImmutableArray<Diagnostic> diagnostics,
        ImmutableArray<DeferredRule> deferredRules,
        ImmutableArray<RuleId> executedRules,
        ImmutableArray<RuleId> skippedRules) =>
        new(diagnostics, deferredRules, executedRules, skippedRules);
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
        RuleImplementationChanged = BaseFactImpact.RuleImplementationChanged(changes);
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

    internal bool RuleImplementationChanged { get; }

    // A base fact is re-evaluated when it is in the candidate delta or when the
    // implementation closure changed and the new implementation must recheck stored facts.
    internal bool IsBaseFactAffected(string path) =>
        BaseFactImpact.IsAffected(Changes, RuleImplementationChanged, path);

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
    Func<RuleEvaluationContext, ImmutableArray<RuleFinding>> evaluate,
    Func<RuleEvaluationContext, bool>? isAffectedBy = null,
    Func<RuleEvaluationContext, ImmutableArray<RuleFinding>>? evaluateCandidateDelta = null,
    ImmutableArray<FindingEdgeDefinition> findingEdges = default) : IRepositoryRule
{
    private readonly ImmutableArray<FindingEdgeDefinition> edges =
        findingEdges.IsDefaultOrEmpty
            ? [new(evaluate, FindingEdgeKind.Local)]
            : findingEdges;

    public ImmutableArray<FindingEdgeDescriptor> FindingEdges =>
        edges.Select(static edge => edge.Descriptor).ToImmutableArray();

    public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) =>
        appliesTo(artifact, context);

    public bool IsAffectedBy(RuleEvaluationContext context) =>
        isAffectedBy?.Invoke(context) ?? true;

    public ImmutableArray<RuleFinding> Evaluate(RuleEvaluationContext context) =>
        evaluate(context);

    public ImmutableArray<RuleFinding> EvaluateCandidateDelta(RuleEvaluationContext context) =>
        (evaluateCandidateDelta ?? evaluate)(context);

    internal static RepositoryRule FromEdges(
        ImmutableArray<FindingEdgeDefinition> findingEdges,
        Func<RepositoryFile, RuleApplicabilityContext, bool> appliesTo,
        Func<RuleEvaluationContext, bool>? isAffectedBy = null) =>
        new(
            appliesTo,
            context => findingEdges
                .SelectMany(edge => edge.Evaluate(context))
                .ToImmutableArray(),
            isAffectedBy,
            context => findingEdges
                .SelectMany(edge => edge.Evaluate(context))
                .ToImmutableArray(),
            findingEdges);

    internal static RepositoryRule FromDiscoveredEdges(
        Type ownerType,
        Func<RepositoryFile, RuleApplicabilityContext, bool> appliesTo,
        Func<RuleEvaluationContext, bool>? isAffectedBy = null)
    {
        var findingEdges = FindingEdgeDescriptor.Discover(ownerType)
            .Select(edge => new FindingEdgeDefinition(
                (Func<RuleEvaluationContext, ImmutableArray<RuleFinding>>)ownerType
                    .GetMethod(edge.MemberName, BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic)!
                    .CreateDelegate(typeof(Func<RuleEvaluationContext, ImmutableArray<RuleFinding>>)),
                edge.Kind))
            .ToImmutableArray();
        if (findingEdges.IsDefaultOrEmpty)
        {
            throw new InvalidOperationException($"Finding-edge provider {ownerType.FullName} has no emit methods.");
        }

        return FromEdges(findingEdges, appliesTo, isAffectedBy);
    }
}
