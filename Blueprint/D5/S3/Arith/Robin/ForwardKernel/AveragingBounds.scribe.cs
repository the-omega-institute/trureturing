using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class AveragingBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/AveragingBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward window averages commute with integrable pairings.",
        H("Bounds and pairing for forward averages"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("window-average-pairing-eq"),
                DeclarationHandle.Create(Prefix + "windowAverage_pairing_eq"),
                H("Pairing and translation averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For M>=0 and l<=r, assume that f(x+t)*z(x) is integrable on the product of (l,r] and (0,M]. The integral of the M-window average of f times z on [l,r] equals 1/M times the integral over t in [0,M] of the integral of f(x+t)*z(x) over x in [l,r]. This also holds for zero window length and degenerate spatial intervals."))),
                DescribeRole.Theorem))));
}
