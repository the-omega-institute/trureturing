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
                "The set-theoretic question in Example 4.6, page 15, for every natural number at least nine.", DescribeRole.Definition),
            Node("result", "result",
                Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(9), Sp, Leq, Sp, F.Id("n"), Sp, To, Sp, Forall, Sp, F.Id("p"), Sp, Colon, Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"), Sp, To, Sp, F.Id("Fin"), Sp, D(2), Sp, To, Sp, F.Id("Projectivization"), Sp, Seq(Mathbb, Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, D(3), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Comma, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("imageClosure"), Sp, F.Id("n"), Sp, Iff, Sp, F.Id("equations"), Sp, F.Id("p")),
                AssessedProvenance.FromRepo(Source),
                "The nine-row Segre minors and the eight-point constraints cut out exactly the variable-camera closed image for every natural number at least nine.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("op-adk2606ex46"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(declaration),
        StatementSource.FromAuthor(formula), provenance, Content(declaration, prose), role, resolution);

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
