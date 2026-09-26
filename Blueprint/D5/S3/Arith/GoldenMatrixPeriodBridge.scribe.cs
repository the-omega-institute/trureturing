using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenMatrixPeriodBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden residues act faithfully as two-dimensional multiplication matrices.",
        H("Golden Matrix Period Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-multiplication-matrix"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenMatrixPeriodBridge.goldenMatrixHom"),
                H("Multiplication in the golden residue algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the ordered basis consisting of the golden generator and one, "
                    + "the residue a+b*phi acts by the matrix with rows "
                    + "(a+b,b) and (b,a). This assignment preserves zero, one, "
                    + "addition and multiplication over any modulus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("faithful-fibonacci-matrix"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenMatrixPeriodBridge.golden_matrix_faithful"),
                H("Faithful Fibonacci matrix representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The matrix assignment is injective: its lower-right and "
                    + "upper-right entries recover both golden coordinates. "
                    + "The golden generator maps to the Fibonacci matrix with "
                    + "rows (1,1) and (1,0). Consequently the generator and "
                    + "this matrix have the same multiplicative order for every modulus."))),
                DescribeRole.Theorem))));
}
