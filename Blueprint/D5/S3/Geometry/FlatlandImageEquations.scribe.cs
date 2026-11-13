using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FlatlandImageEquationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FlatlandImageEquations.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/alstadduffkatzman2026segre");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-camera image equations and their polynomial deformation argument.",
        H("FlatlandImageEquations"),
        Blocks(
            Node("claim", "claim",
                Seq(F.Id("claim"), Sp, Iff, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(9), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, Forall, Sp, F.Id("p"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Fin"), Sp, D(2), Sp, To, Sp, F.Id("Projectivization"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("imageClosure"), Sp, F.Id("n"), Sp, Iff, Sp, F.Id("equations"), Sp, F.Id("p")))),
                AssessedProvenance.FromLiterature(Source),
                "Example 4.6, page 15: “A natural question arises: for n>8, do the 8-point constraints in Equation (38) and the Segre-determinantal minors suffice to give equations for the closed image of Θ₃,₍₂,₂₎,ₙ?” The source asks, in particular, for set-theoretic equations. Here n ranges over natural numbers at least nine, the two cameras vary, and the closure is defined by multihomogeneous vanishing on their actual rational image.", DescribeRole.Definition),
            Node("result", "result",
                Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(9), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, Forall, Sp, F.Id("p"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Fin"), Sp, D(2), Sp, To, Sp, F.Id("Projectivization"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("imageClosure"), Sp, F.Id("n"), Sp, Iff, Sp, F.Id("equations"), Sp, F.Id("p")),
                AssessedProvenance.FromRepo(Source),
                "Example 4.6, page 15: “A natural question arises: for n>8, do the 8-point constraints in Equation (38) and the Segre-determinantal minors suffice to give equations for the closed image of Θ₃,₍₂,₂₎,ₙ?” The source asks, in particular, for set-theoretic equations. Here n ranges over natural numbers at least nine, the two cameras vary, and the closure is defined by multihomogeneous vanishing on their actual rational image.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(declaration),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
