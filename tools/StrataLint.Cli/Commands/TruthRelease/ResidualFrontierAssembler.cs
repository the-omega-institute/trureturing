using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ResidualFrontierAssembler
{
    internal static ImmutableArray<byte> Assemble(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        LeanAxiomReport report,
        IScribeEmissionVerifier scribeEmissionVerifier)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);

        var verifiedScribeEmissions = scribeEmissionVerifier.Verify(snapshot, report);
        var document = BackfillInventoryLoader.Load(snapshot);
        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            lean,
            verifiedScribeEmissions);
        if (evaluation.Findings.Length > 0
            || DigestionReceiptIntegrity.HasFailure(evaluation))
        {
            throw new InvalidOperationException(
                "residual frontier evaluation failed: "
                + string.Join("; ", evaluation.Findings
                    .Concat(DigestionReceiptIntegrity.FailureReasons(evaluation))));
        }

        var summary = DigestResidualSummary.Render(evaluation);
        return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(EchoResidualBlock.Render(summary)));
    }
}
