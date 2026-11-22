using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class UniformCircuitResidueDiagonalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/UniformCircuitResidueDiagonal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal equations on basis coefficients.",
        H("Uniform Circuit Residue Diagonal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reduced-equations"),
                DeclarationHandle.Create(Module + ".reduced_equations"),
                H("Diagonal equations on basis coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the two insertion vectors b_i and s times b_i plus d times b_j, the first "
                    + "insertion forces the coefficients containing i to vanish. The second forces d to kill "
                    + "coefficients containing j. The scalar equation requires all coefficients to be killed "
                    + "by s."))),
                DescribeRole.Theorem))));
}
