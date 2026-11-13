using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FlatlandImageClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FlatlandImageClosure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/alstadduffkatzman2026segre");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-camera image equations and their polynomial deformation argument.",
        H("FlatlandImageClosure"),
        Blocks(
            Node("compatible", "Compatible",
                Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("F"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Fin"), Sp, D(2), Sp, To, Sp, F.Id("Projectivization"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Compatible"), Sp, F.Id("F"), Sp, F.Id("p"), Sp, Colon, Sp, F.Id("Prop"))), Sp, Eq, Sp, Forall, Sp, F.Id("j"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("j"), Sp, D(1))), Sp, Dot, Sp, F.Id("rep"), Sp, new Formula.Subscript(Cdot, F.Id("v")), Sp, Parenthesized(Seq(F.Id("F"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("j"), Sp, D(0))), Sp, Dot, Sp, F.Id("rep"))), Sp, Eq, Sp, D(0)),
                AssessedProvenance.FromRepo(Source),
                "The displayed formula gives the full definition.", DescribeRole.Definition),
            Node("singular-compatible-closure", "singular_compatible_closure",
                Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("F"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("F"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("F"), Sp, Dot, Sp, F.Id("det"), Sp, Eq, Sp, D(0))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Fin"), Sp, D(2), Sp, To, Sp, F.Id("Projectivization"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Compatible"), Sp, F.Id("F"), Sp, F.Id("p"))), Sp, To, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("imageClosure"), Sp, F.Id("n")),
                AssessedProvenance.FromRepo(Source),
                "The displayed formula gives the full statement.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(declaration),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
