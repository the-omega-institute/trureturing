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
            if (arguments.Count is not (1 or 3) || arguments[0] != "--current"
                || arguments.Count == 3 && arguments[1] != "--protected-base")
                throw new InvalidOperationException("USAGE: StrataLint check-source --current [--protected-base SHA]");
            var raw = timing.Measure("repository-read", () => AdmissionRepositoryInputs.ReadCurrent(repository));
            var prepared = arguments.Count == 3 ? repository.Prepare(arguments[2]) : null;
            var baselineRaw = prepared is null ? null : AdmissionRepositoryInputs.ReadBaseline(repository, prepared.Revision);
            if (prepared is not null)
            {
                raw = AdmissionRepositoryInputs.ReadDeltaInputs(repository, raw, baselineRaw!, prepared.Changes);
                var failure = EvaluateAdmissionPlane(raw, baselineRaw!, prepared.Changes, out observations);
                if (failure is not null)
                    return new(2, RenderPlaneObservations(observations), failure.Message + "\n");
            }
            var current = Decode(raw);
            var policy = RepositoryPolicyLoader.Load(current) switch
            {
                PolicyLoadOutcome.Accepted accepted => accepted.Policy,
                PolicyLoadOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            };
            return RenderStage(timing.Measure("source-prerequisite", () => RuleCatalog.Default.ExecuteSourcePrerequisite(
                current, policy, baselineRaw is null ? null : Decode(baselineRaw), prepared?.Changes), Blocked), observations);
        }
        catch (Exception exception)
        {
            return new(2, RenderPlaneObservations(observations), "INFRASTRUCTURE_FAILURE " + exception.Message + "\n");
        }
    }
}
