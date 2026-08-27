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
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyDictionary<RepoPath, TruthState> truthStates)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(truthStates);

        var verifiedScribeEmissions = scribeEmissionVerifier.Verify(snapshot, report);
        var document = BackfillInventoryLoader.Load(snapshot);
        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            lean,
            verifiedScribeEmissions,
            // A read-only assembly of the current tree is its own baseline; without one the
            // aligner reports acknowledged prior generations as structurally rejected and the
            // throw below fires on nothing (#3354).
            baselineDocument: document,
            baselineSnapshot: snapshot,
            truthStates: truthStates);
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(
                "residual frontier evaluation failed: "
                + string.Join("; ", evaluation.ReceiptIntegrityFailureReasons));
        }

        var summary = DigestResidualSummary.Render(evaluation);
        return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(EchoResidualBlock.Render(summary)));
    }
}
