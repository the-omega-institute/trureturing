using System.Collections.Immutable;

namespace StrataLint.Engine;

public sealed record RuleDescriptor(
    RuleId Id,
    string Title,
    DisplaySeverity DisplaySeverity,
    string Category,
    AdmissionEffect AdmissionEffect,
    RuleLifecycle Lifecycle,
    CaseId? DeferredCase);

public sealed class RuleCatalog
{
    private static readonly Lazy<RuleCatalog> DefaultCatalog = new(CreateDefault);

    private readonly ImmutableArray<IRepositoryRule> rules;

    private RuleCatalog(
        ImmutableArray<RuleDescriptor> descriptors,
        ImmutableArray<IRepositoryRule> rules)
    {
        Descriptors = descriptors;
        this.rules = rules;
    }

    public static RuleCatalog Default => DefaultCatalog.Value;

    public ImmutableArray<RuleDescriptor> Descriptors { get; }

    internal static RuleCatalog CreateForTesting(
        ImmutableArray<RuleDescriptor> descriptors,
        ImmutableArray<IRepositoryRule> rules) =>
        new(descriptors, rules);

    internal SingleRuleEvaluation EvaluateSingle(RuleId id, RuleEvaluationContext context)
    {
        var index = -1;
        for (var candidate = 0; candidate < Descriptors.Length; candidate++)
        {
            if (Descriptors[candidate].Id == id)
            {
                index = candidate;
                break;
            }
        }
        if (index < 0)
        {
            throw new ArgumentOutOfRangeException(nameof(id));
        }

        var descriptor = Descriptors[index];
        if (descriptor.Lifecycle is RuleLifecycle.Deferred)
        {
            return new SingleRuleEvaluation(ImmutableArray<Diagnostic>.Empty, descriptor.DeferredCase);
        }

        return new SingleRuleEvaluation(Stamp(descriptor, rules[index].Evaluate(context)), null);
    }

    internal RuleExecutionOutcome Execute(RuleEvaluationContext context)
    {
        try
        {
            var expected = Enumerable.Range(1, 22).Select(RuleId.CreateKnown).ToImmutableArray();
            if (Descriptors.Length != 22
                || rules.Length != 22
                || !Descriptors.Select(item => item.Id).SequenceEqual(expected))
            {
                throw new InvalidOperationException("Rule catalog is incomplete, duplicated, or out of order.");
            }

            var diagnostics = ImmutableArray.CreateBuilder<Diagnostic>();
            diagnostics.AddRange(RepositoryPathPolicy.Evaluate(
                context.Current,
                context.Policy,
                Descriptors[14]));
            var deferred = ImmutableArray.CreateBuilder<DeferredRule>();
            foreach (var (descriptor, index) in Descriptors.Select((value, index) => (value, index)))
            {
                if (descriptor.Lifecycle is RuleLifecycle.Deferred)
                {
                    if (descriptor.DeferredCase is null)
                    {
                        throw new InvalidOperationException($"Deferred rule {descriptor.Id} has no case id.");
                    }

                    deferred.Add(new DeferredRule(descriptor.Id, descriptor.DeferredCase, descriptor.Title));
                    continue;
                }

                diagnostics.AddRange(Stamp(descriptor, rules[index].Evaluate(context)));
            }

            return new RuleExecutionOutcome.Completed(CompletedRuleSet.Create(
                diagnostics.OrderBy(item => item.RuleId.Value, StringComparer.Ordinal)
                    .ThenBy(item => item.Path, StringComparer.Ordinal)
                    .ThenBy(item => item.Message, StringComparer.Ordinal)
                    .ToImmutableArray(),
                deferred.ToImmutable(),
                expected));
        }
        catch (Exception exception)
        {
            return new RuleExecutionOutcome.InfrastructureFailure(
                $"Rule catalog execution failed closed: {exception.Message}");
        }
    }

    private static ImmutableArray<Diagnostic> Stamp(
        RuleDescriptor descriptor,
        ImmutableArray<RuleFinding> findings) =>
        findings.Select(finding => new Diagnostic(
                descriptor.Id,
                descriptor.Title,
                descriptor.DisplaySeverity,
                descriptor.AdmissionEffect,
                finding.Path,
                finding.Message))
            .ToImmutableArray();

    private static RuleCatalog CreateDefault()
    {
        var titles = new[]
        {
            "Stratum import closure",
            "Sorry closure",
            "Capacity pressure",
            "Mirror completeness",
            "Chronicle append only",
            "Generated status",
            "Conflict-of-interest gate",
            "Frozen Hearts semantics",
            "Provenance gate",
            "Generality closure",
            "Controlled domains",
            "Six-line Lean header",
            "Permanent task ledger",
            "Toolchain upgrade compatibility",
            "Machine field and GID grammar",
            "Backfill inventory",
            "Resolvable literature anchors",
            "Machine-produced values",
            "Balanced anomaly ledger",
            "Lean axiom closure",
            "Instantiated coordinate gate",
            "Meta bootstrap gate",
        };
        var builder = ImmutableArray.CreateBuilder<RuleDescriptor>(22);
        for (var number = 1; number <= 22; number++)
        {
            var deferredCase = number switch
            {
                7 => CaseId.CreateKnown("D5-T0011"),
                9 => CaseId.CreateKnown("D5-T0012"),
                14 => CaseId.CreateKnown("D5-T0010"),
                _ => null,
            };
            var lifecycle = deferredCase is null ? RuleLifecycle.Active : RuleLifecycle.Deferred;
            var effect = number switch
            {
                7 or 9 or 22 => AdmissionEffect.HumanGate,
                _ => AdmissionEffect.Block,
            };
            builder.Add(new RuleDescriptor(
                RuleId.CreateKnown(number),
                titles[number - 1],
                effect is AdmissionEffect.Block ? DisplaySeverity.Error : DisplaySeverity.Warning,
                number is 7 or 9 or 22 ? "trust" : "repository",
                effect,
                lifecycle,
                deferredCase));
        }

        return new RuleCatalog(
            builder.MoveToImmutable(),
            Enumerable.Range(1, 22)
                .Select(static number => (IRepositoryRule)new RepositoryRule(number))
                .ToImmutableArray());
    }
}
