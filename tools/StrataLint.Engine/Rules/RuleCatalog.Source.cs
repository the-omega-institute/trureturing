using System.Collections.Immutable;

namespace StrataLint.Engine;

public sealed partial class RuleCatalog
{
    // This is a prerequisite subset, never a certificate for the remaining predicates.
    // Its source cores are also called by normal current/delta execution.
    internal RuleExecutionOutcome ExecuteSourcePrerequisite(
        RepositorySnapshot current, ValidatedPolicy policy,
        RepositorySnapshot? baseline, RawChangeSet? changes, RuleEvaluationMeasure? measureRule = null)
    {
        var capacity = RegistrationFor(RuleId.CreateKnown(3));
        var paths = RegistrationFor(RuleId.CreateKnown(15));
        var findings = Evaluate(() => RepositoryRules.CurrentCapacity(current));
        if (changes is not null)
        {
            if (baseline is null)
                throw new InvalidOperationException("source delta requires a protected snapshot");
            var implementationChanged = BaseFactImpact.RuleImplementationChanged(changes,
                EngineeringProjectRegistry.ReadRuleBuildInputs(current));
            if (capacity.RecheckOnImplementationChange && implementationChanged || RepositoryRules.CapacityAffected(changes))
                findings = findings.AddRange(Evaluate(() => RepositoryRules.Capacity(current, baseline, changes)));
        }
        var diagnostics = Stamp(capacity.Descriptor, findings)
            .AddRange(RepositoryPathPolicy.Evaluate(current, policy, paths.Descriptor));
        return new RuleExecutionOutcome.Completed(CompletedRuleSet.Create(diagnostics, [],
            [capacity.Descriptor.Id, paths.Descriptor.Id],
            ExecutionOrder.Where(id => id != capacity.Descriptor.Id && id != paths.Descriptor.Id).ToImmutableArray()));

        ImmutableArray<RuleFinding> Evaluate(Func<ImmutableArray<RuleFinding>> action) =>
            measureRule is null ? action() : measureRule(capacity.Descriptor.Id, capacity.Descriptor.AdmissionEffect, action);
    }
}
