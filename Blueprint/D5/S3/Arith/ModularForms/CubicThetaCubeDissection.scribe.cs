using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaCubeDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaCubeDissection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Laurent index of the genuine Jacobi cube is evaluated by a full affine lattice reindexing.", H("CubicThetaCubeDissection"), Blocks(
            Paragraph(Text("Every Laurent index of the genuine Jacobi cube is evaluated by a full affine lattice reindexing.")),
            Node("0", "residueExponent", "The nonnegative integer exponent 3*tri(m)+r*m for every integer m and residue r in Fin 3.", DescribeRole.Definition),
            Node("1", "residue_exponent_nonneg", "All integer indices, including negative m, give a nonnegative residue exponent.", DescribeRole.Theorem),
            Node("2", "residue_exponent_cast", "Taking the natural exponent preserves the exact integer polynomial.", DescribeRole.Theorem),
            Node("3", "cube_column_three_mul", "Every index 3*m column equals the norm theta times its exact signed monomial.", DescribeRole.Theorem),
            Node("4", "cube_column_three_mul_add_one", "Every index 3*m+1 column equals negative three times the core theta times its exact signed monomial.", DescribeRole.Theorem),
            Node("5", "cube_column_three_mul_add_two", "Every index 3*m+2 column equals positive three times the core theta times its exact signed monomial.", DescribeRole.Theorem),
            Paragraph(Text("These are attributed classical intermediate identities. The remaining Borwein identities and the complete original k6 sign theorem are separate obligations. No priority or unique claim is made."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-cube-dissection-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
