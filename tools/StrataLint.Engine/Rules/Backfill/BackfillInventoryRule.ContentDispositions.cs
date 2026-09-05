using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class BackfillInventoryRule
{
    internal static ImmutableArray<RuleFinding> ClassifyContentDispositionGaps(
        DigestionLedgerEvaluation evaluation)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var observation in evaluation.ObservedContentKinds)
        {
            try
            {
                _ = DigestionContentDisposition.Resolve(observation.ContentKind);
            }
            catch (FormatException exception)
            {
                findings.Add(new RuleFinding(
                    BackfillPath,
                    $"{exception.Message} (atom {observation.AtomId}, "
                        + $"source {observation.SourceId})",
                    AdmissionEffect.Block));
            }
        }

        return findings.ToImmutable();
    }
}
