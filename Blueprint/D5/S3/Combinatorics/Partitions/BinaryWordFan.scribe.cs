using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class BinaryWordFanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/BinaryWordFan.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary word traces positive unit steps in one oriented plane. Signed triangle sums give area and centered first moments, including paths of zero signed area.",
        H("The signed triangle fan of a binary word"),
        Blocks(
            Node("actual-fan", "One ordered path", "G", DescribeRole.Definition,
                "True is the horizontal unit step and false is the vertical unit step. Prefix sums are the vertices of the path. Each consecutive pair contributes its determinant divided by two and that signed area times the sum of its vertices divided by three. The centered vector is the raw moment minus half the area times the endpoint. The five coordinates are the endpoint, twice the signed area, and twelve times each centered moment. No division by the total area occurs."),
            Node("online-fan", "Appending a supplied letter", "G_append", DescribeRole.Theorem,
                "Appending a letter preserves the old vertices and adds their last triangle. The resulting arithmetic uses the old endpoint and old signed area. It is valid for the empty auxiliary word as well as every nonempty word."),
            Node("concat-fan", "Concatenating two paths", "G_concat", DescribeRole.Theorem,
                "The five coordinates of a concatenation satisfy the signed fan concatenation formula. Both moment coordinates include the endpoint and signed-area seam terms of the same two paths."),
            Node("reverse-fan", "Reversing the complete word", "G_reverse", DescribeRole.Theorem,
                "Reversal fixes both letter counts, negates signed area, and preserves both centered moment coordinates. This statement compares mathematical positive words in a common unit reference. It supplies no operation, acquisition, calibration, or reversal authority over a physical source.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
