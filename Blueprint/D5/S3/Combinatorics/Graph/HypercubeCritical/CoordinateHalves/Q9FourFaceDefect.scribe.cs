using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9FourFaceDefectDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank loss in a three-cube and capacity of a four-face",
        H("The antipodal zero matching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-axis-parity-block-rank-loss"),
                DeclarationHandle.Create(Root + "submatrix_has_nonzero_kernel_iff"),
                H("Classify singular restrictions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An orthogonal four-by-four block whose zeros form a matching can lose rank after restriction to selected columns and rows. A surplus of columns suffices. At equal sizes, the retained or omitted antipodal singleton characterizes the singular exceptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-face-exterior-at-most-three"),
                DeclarationHandle.Create(Root + "exterior_card_le_three"),
                H("Bound the exterior of a witnessed face"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Restore the dominant coordinate as a two-point fibre. The rank witness specifies the double fibres and the empty opposite-parity fibres. Subcubicity and the antipodal matching give a capacity of at most three vertices outside the closed neighborhood."))),
                DescribeRole.Theorem)),
        []));
}
