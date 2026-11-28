using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class MekeraNilpotentAdjacencyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Algebra/MekeraNilpotentAdjacencyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mekerasomeryesil2026annihilatordigraphs");

    private static readonly Formula R = F.Id("R");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");
    private static readonly Formula T = F.Id("t");
    private static readonly Formula K = F.Id("k");
    private static readonly Formula Zero = D(0);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two opposite matrix units refute nilpotent adjacency in the annihilator digraph.",
        H("Distinct nonzero nilpotents can be nonadjacent"),
        Blocks(
            Definition("vertex", "vertex", "Vertices of the annihilator digraph", VertexFormula(),
                "A vertex is a nonzero element with a nonzero annihilator on at least one side."),
            Definition("arc", "arc", "The ordered arc relation", ArcFormula(),
                "Definition 4.1 requires distinct vertices. Each witness is in the ambient ring. "
                + "The left branch excludes both left endpoint annihilators, and the right branch "
                + "excludes both right endpoint annihilators. Reversing the arc reverses the product."),
            Definition("nilpotent", "nilpotent", "Positive-power nilpotence", NilpotentFormula(),
                "The exponent k + 1 is positive, so the power uses multiplication alone. "
                + "For a nonzero nilpotent, the last nonzero power gives a nonzero annihilator."),
            Definition("adjacency-claim", "claim", "The Section 7 adjacency assertion", ClaimFormula(),
                "The assertion quantifies over associative rings in carrier universe zero whose "
                + "multiplication is noncommutative. A multiplicative identity is optional. "
                + "Either arc suffices for adjacency. The two nilpotence exponents can differ."),
            Describe.Lean(DescribeId.Create("adjacency-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("The universal assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Name("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "In the two-by-two matrix ring over the binary field, take the opposite "
                        + "off-diagonal matrix units A and B. They are distinct and nonzero and "
                        + "both square to zero, so each is a vertex. Their products AB and BA "
                        + "are different diagonal units, which exhibits noncommutativity.")),
                    Paragraph(Text(
                        "Matrix-unit multiplication gives (AB)A = A and B(AB) = B. By "
                        + "associativity, a left annihilator of AB annihilates A on the left, "
                        + "and a right annihilator of AB annihilates B on the right. Thus neither "
                        + "can witness an arc from A to B.")),
                    Paragraph(Text(
                        "The identities (BA)B = B and A(BA) = A give the corresponding "
                        + "contradictions for an arc from B to A. Lifting the coefficient type "
                        + "gives the same refutation at each carrier universe."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mekera-somer-yesil-nilpotent-adjacency"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Binder(Formula variables, Formula type) => Seq(variables, Colon, Sp, type);
    private static Formula Quantify(Formula quantifier, Formula binder, Formula body) =>
        Seq(quantifier, Sp, binder, Comma, Sp, body);

    private static Formula And(Formula left, Formula right) => Seq(left, Sp, Land, Sp, right);
    private static Formula Or(Formula left, Formula right) => Seq(left, Sp, Lor, Sp, right);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);

    private static Formula VertexFormula() =>
        Seq(Apply("vertex", X), Sp, Iff, Sp,
            And(NotEqual(X, Zero), Par(Quantify(Exists, Binder(T, R),
                And(NotEqual(T, Zero), Par(Or(Equal(Multiply(X, T), Zero),
                    Equal(Multiply(T, X), Zero))))))));

    private static Formula ArcFormula()
    {
        var product = Par(Multiply(X, Y));
        var left = Quantify(Exists, Binder(T, R),
            And(Equal(Multiply(T, product), Zero),
                And(NotEqual(Multiply(T, X), Zero), NotEqual(Multiply(T, Y), Zero))));
        var right = Quantify(Exists, Binder(T, R),
            And(Equal(Multiply(product, T), Zero),
                And(NotEqual(Multiply(X, T), Zero), NotEqual(Multiply(Y, T), Zero))));
        return Seq(Apply("arc", X, Y), Sp, Iff, Sp,
            And(Apply("vertex", X), And(Apply("vertex", Y),
                And(NotEqual(X, Y), Par(Or(Par(left), Par(right)))))));
    }

    private static Formula NilpotentFormula() =>
        Seq(Apply("nilpotent", X), Sp, Iff, Sp,
            Quantify(Exists, Binder(K, Seq(Mathbb, Grp(F.Id("N")))),
                Equal(new Formula.Power(X, Add(K, D(1))), Zero)));

    private static Formula ClaimFormula()
    {
        var r = F.Id("r");
        var s = F.Id("s");
        var commutative = Quantify(Forall, Binder(Seq(r, Comma, Sp, s), R),
            Equal(Multiply(r, s), Multiply(s, r)));
        var adjacent = Or(Apply("arc", X, Y), Apply("arc", Y, X));
        var endpoints = Quantify(Forall, Binder(Seq(X, Comma, Sp, Y), R),
            Arrow(NotEqual(X, Y), Arrow(NotEqual(X, Zero), Arrow(NotEqual(Y, Zero),
                Arrow(Apply("nilpotent", X), Arrow(Apply("nilpotent", Y), Par(adjacent)))))));
        var carrier = Par(Binder(R, new Formula.Subscript(Name("Type"), Zero)));
        var ring = Seq(OpenBracket, Apply("NonUnitalRing", R), CloseBracket);
        return Seq(Name("claim"), Sp, Iff, Sp,
            Quantify(Forall, Seq(carrier, Sp, ring),
                Arrow(new Formula.Not(Par(commutative)), endpoints)));
    }
}
