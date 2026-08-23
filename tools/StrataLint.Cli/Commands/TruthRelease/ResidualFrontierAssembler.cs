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
            || evaluation.Entries.Any(static entry => entry.Gaps.Any(static gap => gap.Code is
                "coverage-receipt-mismatch"
                or "scribe-definition-mismatch"
                or "scribe-emission-mismatch")))
        {
            throw new InvalidOperationException(
                "residual frontier evaluation failed: "
                + string.Join("; ", evaluation.Findings
                    .Concat(evaluation.Entries.SelectMany(static entry => entry.Gaps
                        .Where(static gap => gap.Code is
                            "coverage-receipt-mismatch"
                            or "scribe-definition-mismatch"
                            or "scribe-emission-mismatch")
                        .Select(gap => $"{entry.Entry.AtomId}:{gap.Code}:{gap.Detail}")))));
        }

        var summary = DigestResidualSummary.Render(evaluation);
        return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(EchoResidualBlock.Render(summary)));
    }
}
