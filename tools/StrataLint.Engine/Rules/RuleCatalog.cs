using System.Collections.Immutable;
using System.Reflection;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

public sealed record RuleDescriptor(
    RuleId Id,
    string Title,
    DisplaySeverity DisplaySeverity,
    string Category,
    AdmissionEffect AdmissionEffect,
    RuleLifecycle Lifecycle,
    CaseId? DeferredCase);

internal sealed record RuleRegistration(
    RuleDescriptor Descriptor,
    IRepositoryRule Rule);

public sealed class RuleCatalog
{
    private static readonly Lazy<RuleCatalog> DefaultCatalog = new(CreateDefault);

    // Measurement window: 19 admission runs for median gate_stage_timing and 120 failed runs
    // for rejection frequency, using the caller-provided observations from this change.
    // Active rules only: Deferred rules never execute and therefore have no execution priority.
    // Selection key: median duration ascending, rejection frequency descending, RuleId ascending.
    // These measurements explain this explicit order; runtime measurements do not derive or
    // validate it, so later timing drift cannot change execution or make the catalog fail.
    private static readonly ImmutableArray<RuleId> PriorityExecutionOrder =
    [
        RuleId.CreateKnown(22),
        RuleId.CreateKnown(23),
        RuleId.CreateKnown(2),
        RuleId.CreateKnown(18),
        RuleId.CreateKnown(12),
        RuleId.CreateKnown(26),
        RuleId.CreateKnown(6),
        RuleId.CreateKnown(25),
        RuleId.CreateKnown(4),
        RuleId.CreateKnown(10),
        RuleId.CreateKnown(11),
        RuleId.CreateKnown(21),
        RuleId.CreateKnown(28),
        RuleId.CreateKnown(15),
        RuleId.CreateKnown(19),
        RuleId.CreateKnown(8),
        RuleId.CreateKnown(20),
        RuleId.CreateKnown(1),
        RuleId.CreateKnown(17),
        RuleId.CreateKnown(16),
        RuleId.CreateKnown(3),
    ];

    private readonly ImmutableArray<RuleRegistration> registrations;

    private RuleCatalog(ImmutableArray<RuleRegistration> registrations)
    {
        this.registrations = registrations;
        Descriptors = registrations
            .Select(static registration => registration.Descriptor)
            .ToImmutableArray();
        var material = JsonSerializer.SerializeToElement(Descriptors.Select(static descriptor => new
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

    internal static ImmutableArray<RuleId> ExecutionOrder => PriorityExecutionOrder;

    internal ImmutableArray<RegisteredFindingEdge> FindingEdges =>
        registrations
            .SelectMany(registration => registration.Rule.FindingEdges.Select(edge =>
                new RegisteredFindingEdge(registration.Descriptor.Id, edge)))
            .Concat(
                typeof(RuleCatalog).Assembly
                    .GetTypes()
                    .Select(type =>
                        (type, provider: type.GetCustomAttributes<FindingEdgeProviderAttribute>().SingleOrDefault()))
                    .Where(static item => item.provider is not null)
                    .SelectMany(static item => FindingEdgeDescriptor.Discover(item.type)
                        .Select(edge => new RegisteredFindingEdge(
                            RuleId.CreateKnown(item.provider!.RuleNumber),
                            edge))))
            .ToImmutableArray();

    internal static RuleCatalog CreateForTesting(ImmutableArray<RuleRegistration> registrations) =>
        new(registrations);

    internal SingleRuleEvaluation EvaluateSingle(RuleId id, RuleEvaluationContext context)
    {
        var registration = RegistrationFor(id);
        var descriptor = registration.Descriptor;
        if (descriptor.Lifecycle is RuleLifecycle.Deferred)
        {
            return new SingleRuleEvaluation(ImmutableArray<Diagnostic>.Empty, descriptor.DeferredCase);
        }

        return new SingleRuleEvaluation(Stamp(descriptor, registration.Rule.Evaluate(context)), null);
    }

    internal ImmutableArray<RuleDescriptor> ApplicableTo(
        RepositoryFile artifact,
        RuleApplicabilityContext context)
    {
        ArgumentNullException.ThrowIfNull(artifact);
        ArgumentNullException.ThrowIfNull(context);
        return registrations
            .Where(registration => registration.Rule.AppliesTo(artifact, context))
            .Select(static registration => registration.Descriptor)
            .ToImmutableArray();
    }

    internal RuleExecutionOutcome Execute(
        RuleEvaluationContext context,
        RuleEvaluationMeasure? measureRule = null) =>
        ExecuteInOrder(context, ExecutionOrder, measureRule);

    internal RuleExecutionOutcome ExecuteInOrderForTesting(
        RuleEvaluationContext context,
        ImmutableArray<RuleId> executionOrder,
        RuleEvaluationMeasure? measureRule = null) =>
        ExecuteInOrder(context, executionOrder, measureRule);

    private RuleExecutionOutcome ExecuteInOrder(
        RuleEvaluationContext context,
        ImmutableArray<RuleId> executionOrder,
        RuleEvaluationMeasure? measureRule)
    {
        try
        {
            var expected = Enumerable.Range(1, 23).Except([5])
                .Append(25)
                .Append(26)
                .Append(28)
                .Select(RuleId.CreateKnown)
                .ToImmutableArray();
            var registeredIds = Descriptors.Select(static item => item.Id).ToImmutableArray();
            var registeredIdSet = registeredIds.ToImmutableHashSet();
            var expectedIdSet = expected.ToImmutableHashSet();
            var missing = expected.Where(id => !registeredIdSet.Contains(id)).ToImmutableArray();
            var duplicated = registeredIds
                .GroupBy(static id => id)
                .Where(static group => group.Count() > 1)
                .Select(static group => group.Key)
                .ToImmutableArray();
            var unexpected = registeredIds
                .Where(id => !expectedIdSet.Contains(id))
                .Distinct()
                .ToImmutableArray();
            if (!missing.IsEmpty || !duplicated.IsEmpty || !unexpected.IsEmpty)
            {
                throw new InvalidOperationException(
                    "Rule catalog is incomplete or duplicated:"
                    + $" missing=[{string.Join(',', missing.Select(static id => id.Value))}]"
                    + $" duplicated=[{string.Join(',', duplicated.Select(static id => id.Value))}]"
                    + $" unexpected=[{string.Join(',', unexpected.Select(static id => id.Value))}].");
            }

            var activeIds = registrations
                .Where(static registration => registration.Descriptor.Lifecycle is RuleLifecycle.Active)
                .Select(static registration => registration.Descriptor.Id)
                .ToImmutableArray();
            var executionOrderSet = executionOrder.ToImmutableHashSet();
            if (executionOrder.Length != executionOrderSet.Count
                || activeIds.Any(id => !executionOrderSet.Contains(id))
                || executionOrder.Any(id => !activeIds.Contains(id)))
            {
                throw new InvalidOperationException(
                    "Rule execution order is not an exact, non-duplicated permutation of active rules.");
            }

            var diagnostics = ImmutableArray.CreateBuilder<Diagnostic>();
            var deferred = ImmutableArray.CreateBuilder<DeferredRule>();
            var executed = ImmutableArray.CreateBuilder<RuleId>();
            var skipped = ImmutableArray.CreateBuilder<RuleId>();
            foreach (var registration in registrations.Where(static registration =>
                registration.Descriptor.Lifecycle is RuleLifecycle.Deferred))
            {
                var descriptor = registration.Descriptor;
                if (descriptor.DeferredCase is null)
                {
                    throw new InvalidOperationException($"Deferred rule {descriptor.Id} has no case id.");
                }

                deferred.Add(new DeferredRule(descriptor.Id, descriptor.DeferredCase, descriptor.Title));
            }

            foreach (var ruleId in executionOrder)
            {
                var registration = RegistrationFor(ruleId);
                var descriptor = registration.Descriptor;
                if (!context.RuleImplementationChanged && !registration.Rule.IsAffectedBy(context))
                {
                    skipped.Add(descriptor.Id);
                    continue;
                }

                executed.Add(descriptor.Id);
                var phaseDiagnostics = ImmutableArray<Diagnostic>.Empty;
                ImmutableArray<RuleFinding> EvaluatePhase()
                {
                    // SL-015 has a pre-body path-policy pass. Keep it in the same callback as
                    // the rule body so one timing event covers the complete executable phase.
                    if (descriptor.Id == RuleId.CreateKnown(15))
                    {
                        phaseDiagnostics = RepositoryPathPolicy.Evaluate(
                            context.Current,
                            context.Policy,
                            descriptor,
                            context.IsBaseFactAffected);
                    }

                    return registration.Rule.EvaluateCandidateDelta(context);
                }

                var findings = measureRule is null
                    ? EvaluatePhase()
                    : measureRule(
                        descriptor.Id,
                        descriptor.AdmissionEffect,
                        EvaluatePhase);
                diagnostics.AddRange(phaseDiagnostics);
                diagnostics.AddRange(Stamp(descriptor, findings));
            }

            return new RuleExecutionOutcome.Completed(CompletedRuleSet.Create(
                diagnostics.OrderBy(item => item.RuleId.Value, StringComparer.Ordinal)
                    .ThenBy(item => item.Path, StringComparer.Ordinal)
                    .ThenBy(item => item.Message, StringComparer.Ordinal)
                    .ToImmutableArray(),
                deferred.OrderBy(static item => item.RuleId.Value, StringComparer.Ordinal).ToImmutableArray(),
                executed.OrderBy(static id => id.Value, StringComparer.Ordinal).ToImmutableArray(),
                skipped.OrderBy(static id => id.Value, StringComparer.Ordinal).ToImmutableArray()));
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

    private RuleRegistration RegistrationFor(RuleId id)
    {
        foreach (var registration in registrations)
        {
            if (registration.Descriptor.Id == id)
            {
                return registration;
            }
        }

        throw new ArgumentOutOfRangeException(nameof(id));
    }

    private static RuleCatalog CreateDefault() => new(RepositoryRules.CreateRegistrations());
}
