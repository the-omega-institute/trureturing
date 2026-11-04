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
            Node("3", "cube_column_three_mul", "All columns in residue zero are translated complete norm lattices.", DescribeRole.Theorem),
            Node("4", "cube_column_three_mul_add_one", "All columns in residue one are translated shifted lattices, with the exact sign.", DescribeRole.Theorem),
            Node("5", "cube_column_three_mul_add_two", "Complementing the three integer indices gives every residue-two column.", DescribeRole.Theorem),
            Paragraph(Text("These are attributed classical intermediate identities. CubicThetaIdentities proves the downstream Borwein relations and EtaSignK6 proves the exact all-index sign theorem. Independent formal acceptance and publication remain separate. No priority or unique claim is made."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-cube-dissection-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
