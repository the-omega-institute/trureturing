using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaWeightedProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaWeightedProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The genuine twisted product and its complete Laurent constant column identify the actual weighted Euler quotient.", H("CubicThetaWeightedProduct"), Blocks(
            Paragraph(Text("The genuine twisted product and its complete Laurent constant column identify the actual weighted Euler quotient.")),
            Node("0", "columnZero_mul_map", "Laurent constant-column extraction commutes with multiplication by a scalar series.", DescribeRole.Theorem),
            Node("2", "columnZero_jacobi_cube_variable", "The cube-dilated Laurent variable has only its integer index zero in column zero.", DescribeRole.Theorem),
            Node("3", "columnZero_expand", "Laurent constant projection commutes with substitution of X cubed.", DescribeRole.Theorem),
            Node("4", "weighted_theta_mul_euler", "Taking the complete Laurent constant column proves the actual weighted product identity.", DescribeRole.Theorem),
            Node("5", "norm_dissection_mul_euler", "The rational cubic dissection is identified with E(X)^3/E(X^3), not assumed.", DescribeRole.Theorem),
            Paragraph(Text("Statements and proof dependencies come from the exact scoped Lean report. Classical theta mathematics is attributed to Borwein and Cooper as quoted in Huang et al. arXiv:2507.16644v1. The repository InversionSeq207 triple-product supplier is reused. No literature priority, worldwide absence, journal-typeset inspection, CI or original-problem acceptance is certified by this document."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubicthetaweightedproduct-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
