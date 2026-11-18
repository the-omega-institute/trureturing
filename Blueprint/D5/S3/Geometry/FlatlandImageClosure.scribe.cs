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
                Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("F"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Fin"), Sp, D(2), Sp, To, Sp, F.Id("Projectivization"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Compatible"), Sp, F.Id("F"), Sp, F.Id("p"), Sp, Colon, Sp, F.Id("Prop"))), Sp, Eq, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("j"), Sp, D(1))), Sp, Dot, Sp, F.Id("rep"), Sp, new Formula.Subscript(Cdot, F.Id("v")), Sp, Parenthesized(Seq(F.Id("F"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("j"), Sp, D(0))), Sp, Dot, Sp, F.Id("rep"))), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(Source),
                "Each image pair satisfies the bilinear equation defined by the same matrix.", DescribeRole.Definition),
            Node("singular-compatible-closure", "singular_compatible_closure",
                Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("F"), Sp, Colon, Sp, F.Id("Matrix"), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("F"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("F"), Sp, Dot, Sp, F.Id("det"), Sp, Eq, Sp, D(0))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Fin"), Sp, D(2), Sp, To, Sp, F.Id("Projectivization"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Compatible"), Sp, F.Id("F"), Sp, F.Id("p"))), Sp, To, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("imageClosure"), Sp, F.Id("n")),
                AssessedProvenance.FromRepo(Source),
                "Every configuration compatible with a nonzero singular matrix belongs to the variable-camera closed image.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(declaration),
        StatementSource.FromAuthor(formula), provenance, Content(declaration, prose), role);

    private static BlockSequence Content(string declaration, string prose)
    {
        if (declaration == "claim")
            return Blocks(Paragraph(Text("Example 4.6, page 15: “A natural question arises: for "),
                Math(Seq(F.Id("n"), Gt, D(8))), Text(", do the "), Math(D(8)),
                Text("-point constraints in Equation (38) and the Segre-determinantal minors suffice to give equations for "),
                Math(Seq(Overline, Grp(Seq(Operatorname, Grp(F.Id("Im")),
                    new Formula.Subscript(Theta, Seq(D(3), Comma, Parenthesized(Seq(D(2), Comma, D(2))), Comma, F.Id("n"))))))),
                Text("?”")),
                Paragraph(Text("“To make this more concrete, we may pose the problem of finding the following descriptions of the ideal of the image variety, in increasing order of difficulty: local equations, set-theoretic equations, scheme-theoretic equations, generators of the vanishing ideal, and/or (universal) Gröbner bases.”")),
                Paragraph(Text(prose + " The field is complex, both cameras vary, and closed image is expressed by multihomogeneous vanishing.")));
        if (declaration is "theta" or "imageClosure")
            return Blocks(Paragraph(Text("Definition 4.1, page 12: “For any "), Math(F.Id("n")), Text(", "),
                Math(F.Id("N")), Text(", and "), Text("m•"),
                Text(" as above, we define the associated image variety (c.f. [2]) to be the closed image of the rational map”")),
                Paragraph(Text(prose + " Here N = 3 and the two image planes have dimension two.")));
        return Blocks(Paragraph(Text(prose)));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
