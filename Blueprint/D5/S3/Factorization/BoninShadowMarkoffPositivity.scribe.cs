using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class BoninShadowMarkoffPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/BoninShadowMarkoffPositivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/bonin2024shadowmarkoff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nonnegative integer shadow Markoff tree has exactly Bonin's quadrilateral of initial points.",
        H("Bonin's Shadow Markoff Positivity Region"),
        Blocks(
            Paragraph(Text("A node is the rational tuple (a, al, b, be, c, ga), in that order. "
                + "The real coordinates are a, b, c and the shadow coordinates are al, be, ga. "
                + "All divisions below are rational divisions. Natural numbers include zero.")),
            Node("Move", "The two directions", MoveFormula(),
                "Section 5, page 9, uses the letters l and r. The constructor l mutates the "
                + "second real-shadow pair, and r mutates the first pair.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("step", "A shadow mutation", StepFormula(),
                "These are the two cases of the mutation in the source's path code, Section 5, "
                + "page 9. The first four entries keep the two unmutated pairs in their new order; "
                + "the final pair contains the quadratic real mutation and its linear shadow.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("path", "Every finite branch, with the root", PathFormula(),
                "Section 5, page 9: \"the 2 mandatory beginning mutations (to the right, then to "
                + "the left)\". The initial real triple is (1,1,1). List.scanl includes its "
                + "initial tuple, then the mandatory r and l moves, and then the word C.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsNatNode", "All six entries are natural numbers", NatNodeFormula(),
                "Equation (8), page 3: \"a, b, c, α, β, γ ∈ ℕ.\" Each existential coordinate "
                + "is explicitly cast to the rationals. In the tuple the real and shadow "
                + "coordinates alternate, as in the source's path code.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("quadrilateral", "The four projective vertices in an affine chart", QuadrilateralFormula(),
                "Conjecture 1, page 3, gives the vertices {(0 : 0 : 1); (1/2 : 0 : 1) ≡ "
                + "(1 : 0 : 2); (1 : 1 : 1); (0 : 2 : 1)}. In the chart ga = 1 their convex "
                + "hull over the rationals has the four vertices displayed here.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1 for the rooted tree", ClaimFormula(),
                "Conjecture 1, page 3: \"Every triple (A, B, C) of positive integer solutions to "
                + "(3) can be obtained from the initial triple (7) where (α, β, γ) are positive "
                + "integers such that (α : β : γ) ∈ ℚP² are the rational points that belong to "
                + "the quadrilateral with vertices {(0 : 0 : 1); (1/2 : 0 : 1) ≡ (1 : 0 : 2); "
                + "(1 : 1 : 1); (0 : 2 : 1)} depicted in the following figure via mutations (5) "
                + "and permutations along the Markoff tree.\" The same page says: \"It can be "
                + "reformulated in terms of the initial triple (7) such that under every series "
                + "of mutations along the Markoff tree the triple (α, β, γ) remain positive.\" "
                + "The symbols al, be, ga encode α, β, γ. Equation (8) and the boundary "
                + "vertices give the nonnegative integer reading. The zero triple is excluded; "
                + "ga > 0 selects the affine chart. The tree is precisely the rooted tree of "
                + "Sections 2 and 5, with every finite word after the mandatory r, l moves. "
                + "Arbitrary independent permutations at the root are outside this assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The exact positivity region", Disp(ClaimBody()),
                "The shifted shadows 3x − σa, with σ the sum of the initial shadows, satisfy "
                + "a cone invariant under both mutations. This proves positivity throughout "
                + "the tree when al + be ≤ 2ga and 2al ≤ be + ga. Conversely, the two constant "
                + "direction spines satisfy forced second order recurrences. A negative forcing "
                + "makes a shadow negative by the normalized Wronskian drift estimate. The two "
                + "inequalities cut out exactly the displayed convex hull. Integrality is "
                + "preserved even for arbitrary integer initial shadows. The result determines "
                + "the polygon left unspecified by the source's Theorem 1 for this rooted tree.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bonin-2024-shadow-markoff-positivity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("bonin-shadow-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula MoveFormula() => Disp(new Formula.Aligned([
        Seq(Operatorname, Grp(F.Id("inductive")), Sp, F.Id("Move"), Colon, Sp, F.Id("Type")),
        Seq(Mid, Sp, Qualified("Move", "l"), Colon, Sp, F.Id("Move")),
        Seq(Mid, Sp, Qualified("Move", "r"), Colon, Sp, F.Id("Move")),
    ]));

    private static Formula StepFormula()
    {
        var a = F.Id("a"); var al = F.Id("al"); var b = F.Id("b");
        var be = F.Id("be"); var c = F.Id("c"); var ga = F.Id("ga");
        var leftReal = Div(Add(Sq(a), Sq(c)), b);
        var rightReal = Div(Add(Sq(b), Sq(c)), a);
        var leftShadow = Div(Add(Add(Mul(new Formula.Negate(leftReal), be),
            Mul(Mul(D(2), a), al)), Mul(Mul(D(2), c), ga)), b);
        var rightShadow = Div(Add(Add(Mul(new Formula.Negate(rightReal), al),
            Mul(Mul(D(2), b), be)), Mul(Mul(D(2), c), ga)), a);
        return Disp(All(["a", "al", "b", "be", "c", "ga"], Q(),
            new Formula.Aligned([
                Equal(Call("step", Tuple(a, al, b, be, c, ga), Qualified("Move", "l")),
                    Tuple(a, al, c, ga, leftReal, leftShadow)),
                Equal(Call("step", Tuple(a, al, b, be, c, ga), Qualified("Move", "r")),
                    Tuple(c, ga, b, be, rightReal, rightShadow)),
            ])));
    }

    private static Formula PathFormula() => Disp(All(["al", "be", "ga"], Q(),
        All(["C"], Call("List", F.Id("Move")),
            Equal(Call("path", F.Id("al"), F.Id("be"), F.Id("ga"), F.Id("C")),
                Apply(Qualified("List", "scanl"), F.Id("step"),
                    Tuple(D(1), F.Id("al"), D(1), F.Id("be"), D(1), F.Id("ga")),
                    Seq(Qualified("Move", "r"), Colon, Colon,
                        Qualified("Move", "l"), Colon, Colon, F.Id("C")))))));

    private static Formula NatNodeFormula() => Disp(All(["t"], NodeType(),
        Iff(Call("IsNatNode", F.Id("t")),
            new Formula.BindMany(FormulaQuantifier.Exists,
                [Bound("a", N()), Bound("al", N()), Bound("b", N()),
                 Bound("be", N()), Bound("c", N()), Bound("ga", N())],
                Equal(F.Id("t"), Tuple(Cast("a"), Cast("al"), Cast("b"),
                    Cast("be"), Cast("c"), Cast("ga")))))));

    private static Formula QuadrilateralFormula() => Disp(Equal(Call("quadrilateral"),
        Call("convexHull", Q(), new Formula.SetLiteral([
            Tuple(D(0), D(0)), Tuple(Div(D(1), D(2)), D(0)),
            Tuple(D(1), D(1)), Tuple(D(0), D(2)),
        ]))));

    private static Formula ClaimFormula() => Disp(Iff(Call("claim"), ClaimBody()));

    private static Formula ClaimBody()
    {
        var al = F.Id("al"); var be = F.Id("be"); var ga = F.Id("ga");
        var nodes = All(["C"], Call("List", F.Id("Move")), All(["t"], NodeType(),
            Implies(Member(F.Id("t"), Call("path", Cast("al"), Cast("be"), Cast("ga"), F.Id("C"))),
                Call("IsNatNode", F.Id("t")))));
        var region = And(Lt(D(0), ga), Member(Tuple(Div(Cast("al"), Cast("ga")),
            Div(Cast("be"), Cast("ga"))), Call("quadrilateral")));
        return All(["al", "be", "ga"], N(),
            Implies(NotEqual(Tuple(al, be, ga), Tuple(D(0), D(0), D(0))), Iff(nodes, region)));
    }

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula NodeType() => Seq(Q(), Times, Q(), Times, Q(), Times,
        Q(), Times, Q(), Times, Q());
    private static Formula Cast(string name) => Parenthesized(Seq(F.Id(name), Colon, Sp, Q()));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Tuple(params Formula[] values)
    {
        Formula result = values[0];
        for (int i = 1; i < values.Length; i++) result = Seq(result, Comma, Sp, values[i]);
        return Parenthesized(result);
    }
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name)))
            : Apply(Seq(Operatorname, Grp(F.Id(name))), args);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(string[] names, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => Bound(name, type))], body);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
}
