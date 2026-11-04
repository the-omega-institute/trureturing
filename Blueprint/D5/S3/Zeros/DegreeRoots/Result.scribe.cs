using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.DegreeRoots;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/DegreeRoots/Result.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/browngeorge2025degree");
    private const string SourceClaim =
        "If z is a nonzero degree root of a graph of order n with argument arg(z) ∈ (−π, π], "
        + "then |z| ≤ (n − 1)^{|arg(z)/π|}.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero degree root satisfies the Brown–George argument-dependent modulus bound.",
        H("The degree polynomial root bound"), Blocks(
            Node("degreePolynomial", "The degree polynomial", DegreeFormula(),
                "Section 1, p. 164: “For any v ∈ V, let deg(v) = deg_G(v) denote its degree in G, "
                + "and let a_k be the number of vertices of degree k in G. The degree polynomial of G is defined by” "
                + "D(G;x)=Σ_{v∈V} x^{deg(v)}=Σ_{k=δ}^{Δ} a_k x^k. "
                + "Here G is a simple graph on Fin n, and Polynomial.X has complex coefficients. "
                + "The sum counts every vertex once, including vertices of degree zero.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("claim", "Conjecture 4.1", Eqn(Id("claim"), Parenthesized(ClaimBody())),
                "Conjecture 4.1, p. 180: “" + SourceClaim + "” "
                + "The order is a positive natural number n; the vertices are Fin n. "
                + "Complex.arg takes values in (−π, π], the modulus is the complex norm, "
                + "and the real power has exponent |Complex.arg z|/Real.pi. "
                + "Since Real.pi is positive, this exponent equals |arg(z)/π|.",
                AssessedProvenance.FromLiterature(Source), DescribeRole.Definition),
            Node("result", "Conjecture 4.1 holds", ClaimBody(),
                "For roots outside the unit disk, divide the polynomial equation by its largest degree power. "
                + "The vertices of maximum degree contribute a positive constant. "
                + "The normalized inverse-power estimate bounds the norm by the ratio of the remaining "
                + "vertex count to that constant, raised to |Complex.arg z|/Real.pi. "
                + "This ratio is at most n−1. For n at least two, roots in the unit disk satisfy the "
                + "same bound; for n=1 the degree polynomial is one and has no roots.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("brown-george-2025-degree-polynomial-root-bound"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("brown-george-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(DefinitionDsl.Text(prose))), role, openProblemResolutionClaim: resolution);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Q(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Id(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Arrow(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Nat => Op("Nat");
    private static Formula Real => Op("Real");
    private static Formula Complex => Op("Complex");
    private static Formula GraphType() => Call("SimpleGraph", Call("Fin", Id("n")));
    private static Formula DegreeFormula() => All("n", Nat, All("G", GraphType(),
        Eqn(Call("degreePolynomial", Id("G")),
            Seq(new Formula.Subscript(Sum, Typed(Id("v"), Call("Fin", Id("n")))),
                new Formula.Power(Q("Polynomial", "X"), App(Seq(Id("G"), Dot, Id("degree")), Id("v")))))));
    private static Formula ClaimBody()
    {
        var z = Id("z");
        var root = Eqn(App(Seq(Parenthesized(Call("degreePolynomial", Id("G"))), Dot, Id("eval")), z), D(0));
        var bound = Leq(new Formula.Norm(z), new Formula.Power(
            Parenthesized(Seq(Typed(Id("n"), Real), Minus, D(1))),
            new Formula.Fraction(new Formula.Absolute(App(Q("Complex", "arg"), z)), Q("Real", "pi"))));
        return All("n", Nat, Arrow(Leq(D(1), Id("n")), All("G", GraphType(), All("z", Complex,
            Arrow(new Formula.Relation(z, FormulaRelationOperator.NotEqual, D(0)), Arrow(root, bound))))));
    }
}
