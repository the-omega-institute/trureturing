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
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        RawChangeSet changes,
        MetaClear metaClear)
    {
        Current = current;
        Baseline = baseline;
        Policy = policy;
        Lean = lean;
        BaselineLean = baselineLean;
        Changes = changes;
        MetaClear = metaClear;
    }

    internal RepositorySnapshot Current { get; }

    internal RepositorySnapshot Baseline { get; }

    internal ValidatedPolicy Policy { get; }

    internal AcceptedLeanClosure Lean { get; }

    internal AcceptedLeanClosure BaselineLean { get; }

    internal RawChangeSet Changes { get; }

    internal MetaClear MetaClear { get; }

    internal static RuleEvaluationContext Create(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        RawChangeSet changes,
        MetaClear metaClear) =>
        new(current, baseline, policy, lean, baselineLean, changes, metaClear);
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
