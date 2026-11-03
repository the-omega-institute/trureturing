using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EulerNineDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/EulerNineDissection.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual Euler quotient has three genuine restricted partition sections.", H("EulerNineDissection"), Blocks(
            Paragraph(Text("The Jacobi products are identified with E times Q_r by multiplying the actual restricted-partition HasProd by the Euler HasProd. Allowed geometric factors cancel exactly; each finite block of nine leaves precisely the three forbidden factors. The finite-block identity is proved for arbitrary cutoff and then passed to its true coefficientwise limit. The constant-one Euler inverse gives J_r P=Q_r. Thus R=E(q)/E(q^3) has the required signed dissection; it is not an assumed partition identity. EulerNineSquareDissection consumes R_dissection.")),
            Node("0", "J_eq_euler_mul_Q", "For r=1,2,4, the weighted Jacobi series is E times the actual allowed-part counting series.", DescribeRole.Theorem),
            Node("1", "J_mul_inverse", "Multiplying by the genuine Euler inverse yields the restricted partition section.", DescribeRole.Theorem),
            Node("2", "R", "The actual Euler quotient E(q) times P(q^3).", DescribeRole.Definition),
            Node("3", "R_dissection", "The all-degree equality R=Q4(q^3)-qQ2(q^3)-q^2Q1(q^3).", DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("eulerninedissection-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
