using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVDimThreePackedCheckDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer coefficients for the three-dimensional refined BMV bound",
        H("Integer coefficients for the three-dimensional refined BMV bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmvdimthreepackedcheck-p5"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVDimThreePackedCheck.mask_check_five"),
                H("Packed sign comparison for five first factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In Hägele’s three-dimensional pairing, combine the first two radicands into their sum Q, and let W be the third radicand. If Z is the deficit at the three distinct indices, the polynomial is four times Q times W minus the square of Z squared minus Q minus W. Evaluate this polynomial at a positional encoding of the ordered cube-root coordinates. After adding the digit midpoint, one bit in each digit tests whether the corresponding coefficient is nonnegative. Exact integer evaluation gives the comparison for five first factors."))),
                DescribeRole.Theorem))));
}
