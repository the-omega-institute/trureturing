using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class ResidualFrontierAssembler
{
    internal static ImmutableArray<byte> Assemble(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        LeanAxiomReport report,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyDictionary<RepoPath, TruthState> truthStates,
        IReadOnlyList<DocumentDefinition> definitions)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        ArgumentNullException.ThrowIfNull(report);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(truthStates);

        ArgumentNullException.ThrowIfNull(definitions);
        scribeEmissionVerifier.Verify(snapshot, report, definitions);
        var document = BackfillInventoryLoader.Load(snapshot);
        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            lean,
            truthStates: truthStates);
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(
                "residual frontier evaluation failed: "
                + string.Join("; ", evaluation.ReceiptIntegrityFailureReasons));
        }

        var frontier = DigestionFrontierProjection.Create(
            document,
            evaluation,
            DigestionContentKindResolver.Resolve(snapshot, document));
        var summary = DigestResidualSummary.Render(evaluation, frontier);
        return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(EchoResidualBlock.Render(summary)));
    }
}
