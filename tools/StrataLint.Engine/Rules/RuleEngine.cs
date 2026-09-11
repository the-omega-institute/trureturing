using System.Collections.Immutable;
using System.Reflection;
using Dunet;

namespace StrataLint.Engine;

internal static class BaseFactImpact
{
    internal static bool RuleImplementationChanged(RawChangeSet changes, IReadOnlySet<string> registeredInputs) =>
        changes.Paths.Any(path =>
            StrataLintEngineBuildInputs.ContainsRuleImplementation(path.Value, registeredInputs));

    internal static bool IsAffected(
        RawChangeSet changes,
        bool ruleImplementationChanged,
        string path) =>
        ruleImplementationChanged
        || changes.ContainsPath(path);
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

internal delegate bool RuleApplicabilityMeasure(Func<bool> isAffectedBy);

internal delegate CanonicalizationOutcome CanonicalizationMeasure(
    Func<CanonicalizationOutcome> canonicalize);

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
    Func<CurrentRuleContext, ImmutableArray<RuleFinding>> Evaluate,
    FindingEdgeKind Kind)
{
    internal FindingEdgeDescriptor Descriptor => FindingEdgeDescriptor.From(Evaluate, Kind);
}

internal interface IRepositoryRule
{
    bool HasCurrentPredicate => true;
    bool HasDeltaPredicate => false;
    ImmutableArray<FindingEdgeDescriptor> FindingEdges => [];

    bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context);

    bool IsAffectedBy(DeltaRuleContext context) => true;

    ImmutableArray<RuleFinding> EvaluateCurrent(CurrentRuleContext context) => [];

    ImmutableArray<RuleFinding> EvaluateDelta(DeltaRuleContext context) => [];
}

public sealed class CurrentRuleContext
{
    private CurrentRuleContext(RepositorySnapshot current, ValidatedPolicy policy, AcceptedLeanClosure lean, VerifiedScribeEmissions? emissions)
    {
        Current = current;
        Policy = policy;
        Lean = lean;
        VerifiedScribeEmissions = emissions;
    }

    internal RepositorySnapshot Current { get; }
    internal ValidatedPolicy Policy { get; }
    internal AcceptedLeanClosure Lean { get; }
    internal VerifiedScribeEmissions? VerifiedScribeEmissions { get; }
    internal static CurrentRuleContext Create(RepositorySnapshot current, ValidatedPolicy policy, AcceptedLeanClosure lean, VerifiedScribeEmissions? emissions = null) =>
        new(current, policy, lean, emissions);
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

internal sealed record CandidateCommonResults(string Candidate, string Round);

public sealed class DeltaRuleContext
{
    private DeltaRuleContext(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaEvaluationProfile metaEvaluation,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        CandidateCommonResults? commonResults)
    {
        Current = current;
        Baseline = baseline;
        Policy = policy;
        Lean = lean;
        Changes = changes;
        BackfillCandidateDeltaSession = new BackfillCandidateDeltaSession(
            current,
            baseline,
            changes);
        RegisteredRuleBuildInputs = EngineeringProjectRegistry.ReadRuleBuildInputs(current);
        RuleImplementationChanged = BaseFactImpact.RuleImplementationChanged(changes, RegisteredRuleBuildInputs);
        MetaEvaluation = metaEvaluation;
        VerifiedScribeEmissions = verifiedScribeEmissions;
        CommonResults = commonResults;
    }

    internal IReadOnlySet<string> RegisteredRuleBuildInputs { get; }

    internal RepositorySnapshot Current { get; }

    internal CurrentRuleContext CurrentFacts => CurrentRuleContext.Create(Current, Policy, Lean, VerifiedScribeEmissions);

    // Base is read as data by the candidate judge.
    internal RepositorySnapshot Baseline { get; }

    internal CandidateCommonResults? CommonResults { get; }

    internal ValidatedPolicy Policy { get; }

    internal AcceptedLeanClosure Lean { get; }

    internal RawChangeSet Changes { get; }

    internal BackfillCandidateDeltaSession BackfillCandidateDeltaSession { get; }

    internal int BackfillCandidateDeltaLoadCount => BackfillCandidateDeltaSession.LoadCount;

    internal bool RuleImplementationChanged { get; }

    // A base fact is re-evaluated when it is in the candidate delta or when the
    // implementation closure changed and the new implementation must recheck stored facts.
    internal bool IsBaseFactAffected(string path) =>
        BaseFactImpact.IsAffected(Changes, RuleImplementationChanged, path);

    internal MetaEvaluationProfile MetaEvaluation { get; }

    internal VerifiedScribeEmissions? VerifiedScribeEmissions { get; }

    internal static DeltaRuleContext Create(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaClear metaClear,
        VerifiedScribeEmissions? verifiedScribeEmissions = null) =>
        Create(
            current,
            baseline,
            policy,
            lean,
            changes,
            MetaEvaluationProfile.ForClear(metaClear),
            verifiedScribeEmissions);

    internal static DeltaRuleContext Create(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        RawChangeSet changes,
        MetaEvaluationProfile metaEvaluation,
        VerifiedScribeEmissions? verifiedScribeEmissions = null,
        CandidateCommonResults? commonResults = null) =>
        new(
            current,
            baseline,
            policy,
            lean,
            changes,
            metaEvaluation,
            verifiedScribeEmissions,
            commonResults);
}

internal sealed class RepositoryRule(
    Func<RepositoryFile, RuleApplicabilityContext, bool> appliesTo,
    Func<CurrentRuleContext, ImmutableArray<RuleFinding>>? evaluate = null,
    Func<DeltaRuleContext, bool>? isAffectedBy = null,
    Func<DeltaRuleContext, ImmutableArray<RuleFinding>>? evaluateDelta = null,
    ImmutableArray<FindingEdgeDefinition> findingEdges = default) : IRepositoryRule
{
    public bool HasCurrentPredicate => evaluate is not null;
    public bool HasDeltaPredicate => evaluateDelta is not null;
    private readonly ImmutableArray<FindingEdgeDescriptor> edges =
        findingEdges.IsDefaultOrEmpty
            ? evaluate is not null ? [FindingEdgeDescriptor.From(evaluate, FindingEdgeKind.Local)]
                : evaluateDelta is not null ? [FindingEdgeDescriptor.From(evaluateDelta, FindingEdgeKind.Local)] : []
            : findingEdges.Select(static edge => edge.Descriptor).ToImmutableArray();

    public ImmutableArray<FindingEdgeDescriptor> FindingEdges =>
        edges;

    public bool AppliesTo(RepositoryFile artifact, RuleApplicabilityContext context) =>
        appliesTo(artifact, context);

    public bool IsAffectedBy(DeltaRuleContext context) =>
        isAffectedBy?.Invoke(context) ?? true;

    public ImmutableArray<RuleFinding> EvaluateCurrent(CurrentRuleContext context) =>
        evaluate?.Invoke(context) ?? [];

    public ImmutableArray<RuleFinding> EvaluateDelta(DeltaRuleContext context) =>
        evaluateDelta?.Invoke(context) ?? [];

    internal static RepositoryRule FromEdges(
        ImmutableArray<FindingEdgeDefinition> findingEdges,
        Func<RepositoryFile, RuleApplicabilityContext, bool> appliesTo,
        Func<DeltaRuleContext, bool>? isAffectedBy = null) =>
        new(
            appliesTo,
            context => findingEdges
                .SelectMany(edge => edge.Evaluate(context))
                .ToImmutableArray(),
            isAffectedBy,
            null,
            findingEdges);

    internal static RepositoryRule FromDiscoveredEdges(
        Type ownerType,
        Func<RepositoryFile, RuleApplicabilityContext, bool> appliesTo,
        Func<DeltaRuleContext, bool>? isAffectedBy = null)
    {
        var findingEdges = FindingEdgeDescriptor.Discover(ownerType)
            .Select(edge => new FindingEdgeDefinition(
                (Func<CurrentRuleContext, ImmutableArray<RuleFinding>>)ownerType
                    .GetMethod(edge.MemberName, BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic)!
                    .CreateDelegate(typeof(Func<CurrentRuleContext, ImmutableArray<RuleFinding>>)),
                edge.Kind))
            .ToImmutableArray();
        if (findingEdges.IsDefaultOrEmpty)
        {
            throw new InvalidOperationException($"Finding-edge provider {ownerType.FullName} has no emit methods.");
        }

        return FromEdges(findingEdges, appliesTo, isAffectedBy);
    }
}
