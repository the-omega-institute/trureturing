using System.Collections.Immutable;
using System.Text.Json;

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
        var material = JsonSerializer.SerializeToElement(descriptors.Select(static descriptor => new
        {
            admission_effect = descriptor.AdmissionEffect.ToString(),
            category = descriptor.Category,
            deferred_case = descriptor.DeferredCase?.Value,
            display_severity = descriptor.DisplaySeverity.ToString(),
            id = descriptor.Id.Value,
            lifecycle = descriptor.Lifecycle.ToString(),
            title = descriptor.Title,
        }));
        RootSha256 = FrozenContentHash.Compute(
            FrozenHashDomains.RuleCatalog,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
    }

    public static RuleCatalog Default => DefaultCatalog.Value;

    public ImmutableArray<RuleDescriptor> Descriptors { get; }

    public string RootSha256 { get; }

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

    internal ImmutableArray<RuleDescriptor> ApplicableTo(
        RepositoryFile artifact,
        RuleApplicabilityContext context)
    {
        ArgumentNullException.ThrowIfNull(artifact);
        ArgumentNullException.ThrowIfNull(context);
        return rules
            .Select((rule, index) => (Rule: rule, Descriptor: Descriptors[index]))
            .Where(item => item.Rule.AppliesTo(artifact, context))
            .Select(static item => item.Descriptor)
            .ToImmutableArray();
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
        findings.Select(finding =>
            {
                // A finding may soften its own admission effect (e.g. a soft-limit
                // warning under a rule whose default effect blocks); severity tracks
                // the effect that actually applies.
                var effect = finding.Effect ?? descriptor.AdmissionEffect;
                var severity = finding.Effect is null
                    ? descriptor.DisplaySeverity
                    : effect is AdmissionEffect.Block ? DisplaySeverity.Error : DisplaySeverity.Warning;
                return new Diagnostic(
                    descriptor.Id,
                    descriptor.Title,
                    severity,
                    effect,
                    finding.Path,
                    finding.Message);
            })
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
            "Digestion ledger",
            "Typed anchor membership",
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
            RepositoryRules.CreateRuleSet());
    }
}
