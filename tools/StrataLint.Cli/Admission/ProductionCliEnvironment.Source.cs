using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    public ExplicitCommandResult CheckSource(IReadOnlyList<string> arguments)
    {
        var timing = new AdmissionCheckTiming(timeProvider);
        ImmutableArray<Diagnostic> observations = [];
        try
        {
            var currentRequested = false;
            var capacityRequested = false;
            string? protectedBase = null;
            for (var index = 0; index < arguments.Count; index++)
            {
                switch (arguments[index])
                {
                    case "--current" when !currentRequested:
                        currentRequested = true;
                        break;
                    case "--artifact-capacity" when !capacityRequested:
                        capacityRequested = true;
                        break;
                    case "--protected-base" when protectedBase is null && index + 1 < arguments.Count:
                        protectedBase = arguments[++index];
                        if (protectedBase.StartsWith("--", StringComparison.Ordinal))
                            throw new InvalidOperationException("USAGE: --protected-base requires one value");
                        break;
                    default:
                        throw new InvalidOperationException("USAGE: check-source options are --current, --artifact-capacity, and --protected-base SHA");
                }
            }
            if (!currentRequested && !capacityRequested || capacityRequested && protectedBase is null)
                throw new InvalidOperationException("USAGE: StrataLint check-source --current [--artifact-capacity] [--protected-base SHA] | --artifact-capacity --protected-base SHA");
            var prepared = protectedBase is null ? null : repository.Prepare(protectedBase);
            if (!currentRequested)
            {
                var selected = prepared!.Changes.Entries.Where(static change =>
                    change.Kind is RawChangeKind.Added or RawChangeKind.Modified
                    && !RepositoryRules.IsArtifactLineCapacityExcluded(change.Path.Value))
                    .Select(static change => DigestionQuerySelection.Literal(change.Path.Value)).ToArray();
                var capacityRaw = selected.Length == 0 ? RawRepositorySnapshot.Create([]) : repository.ReadCurrent(selected);
                return RenderStage(timing.Measure("artifact-capacity", () => RuleCatalog.Default.ExecuteArtifactCapacity(
                    Decode(capacityRaw), prepared.Changes)));
            }
            var raw = timing.Measure("repository-read", () => AdmissionRepositoryInputs.ReadCurrent(repository));
            var baselineRaw = prepared is null ? null : AdmissionRepositoryInputs.ReadBaseline(repository, prepared.Revision);
            RepositorySnapshot current;
            RepositorySnapshot? baseline = null;
            if (prepared is not null)
            {
                raw = AdmissionRepositoryInputs.ReadDeltaInputs(repository, raw, baselineRaw!, prepared.Changes,
                    out current, out baseline);
            }
            else current = Decode(raw);
            if (capacityRequested)
            {
                var capacity = timing.Measure("artifact-capacity", () => RuleCatalog.Default.ExecuteArtifactCapacity(
                    current, prepared!.Changes));
                if (capacity is RuleExecutionOutcome.InfrastructureFailure)
                    return RenderStage(capacity, observations);
                if (capacity is RuleExecutionOutcome.Completed completed
                    && completed.Capability.Diagnostics.Any(static diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block))
                    return RenderStage(capacity, observations);
            }
            if (prepared is not null)
            {
                var failure = EvaluateAdmissionPlane(raw, baselineRaw!, prepared.Changes, out observations);
                if (failure is not null)
                    return new(2, RenderPlaneObservations(observations), failure.Message + "\n");
            }
            var policy = RepositoryPolicyLoader.Load(current) switch
            {
                PolicyLoadOutcome.Accepted accepted => accepted.Policy,
                PolicyLoadOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            };
            return RenderStage(timing.Measure("source-prerequisite", () => RuleCatalog.Default.ExecuteSourcePrerequisite(
                current, policy, baseline, prepared?.Changes), Blocked), observations);
        }
        catch (Exception exception)
        {
            return new(2, RenderPlaneObservations(observations), "INFRASTRUCTURE_FAILURE " + exception.Message + "\n");
        }
    }

}
