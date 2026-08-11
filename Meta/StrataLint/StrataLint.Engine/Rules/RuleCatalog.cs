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

internal sealed record RuleRegistration(
    RuleDescriptor Descriptor,
    IRepositoryRule Rule);

public sealed class RuleCatalog
{
    private static readonly Lazy<RuleCatalog> DefaultCatalog = new(CreateDefault);

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

    internal RuleExecutionOutcome Execute(RuleEvaluationContext context)
    {
        try
        {
            var expected = Enumerable.Range(1, 23)
                .Append(25)
                .Select(RuleId.CreateKnown)
                .ToImmutableArray();
            if (registrations.Length != expected.Length
                || !Descriptors.Select(item => item.Id).SequenceEqual(expected))
            {
                throw new InvalidOperationException("Rule catalog is incomplete, duplicated, or out of order.");
            }

            var diagnostics = ImmutableArray.CreateBuilder<Diagnostic>();
            diagnostics.AddRange(RepositoryPathPolicy.Evaluate(
                context.Current,
                context.Policy,
                RegistrationFor(RuleId.CreateKnown(15)).Descriptor));
            var deferred = ImmutableArray.CreateBuilder<DeferredRule>();
            foreach (var registration in registrations)
            {
                var descriptor = registration.Descriptor;
                if (descriptor.Lifecycle is RuleLifecycle.Deferred)
                {
                    if (descriptor.DeferredCase is null)
                    {
                        throw new InvalidOperationException($"Deferred rule {descriptor.Id} has no case id.");
                    }

                    deferred.Add(new DeferredRule(descriptor.Id, descriptor.DeferredCase, descriptor.Title));
                    continue;
                }

                diagnostics.AddRange(Stamp(descriptor, registration.Rule.Evaluate(context)));
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
