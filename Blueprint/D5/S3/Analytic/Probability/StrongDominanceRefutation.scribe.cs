using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class StrongDominanceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Probability/StrongDominanceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/zoroa2017couponcollector");
    private const string DominanceQuotation =
        "Definition 8.2, arXiv v1 pp. 28, 30 (published Definition 7.2): “Let X and X′ be two real random variables, "
        + "defined on probabilities spaces (Ω,P) and (Ω′,P′), respectively, and taking values in a denumerable set D. "
        + "We say that the random variable X strongly stochastically dominates the random variable X′ if there is "
        + "a critical value c∈ℝ such that, for any d∈D” followed by “if d≤c, then P(X=d)≤P′(X′=d),” "
        + "and “if d>c, then P(X=d)≥P′(X′=d).” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive four-label, five-draw counterexample to strong dominance.",
        H("Strong dominance fails for unequal-probability coupon collection"),
        Blocks(
            Entry("pmf", "distinctCountPMF", "Probability mass function for the distinct-label count", PmfDefinition(),
                AssessedProvenance.FromLiterature(Source),
                "Section 3, arXiv v1 p. 7: “Let Yₙ be the random variable representing the number of parasitized "
                + "hosts after n draws, that is Yₙ=k if there are exactly k parasitized hosts after n draws.” "
                + "Section 2, pp. 5–6, assigns the cylinder probability pᵢ₁pᵢ₂⋯pᵢₙ to each fixed initial word. "
                + "Fin N labels hosts from zero, and Fin n labels draws from zero. The standard simplex supplies "
                + "nonnegative real weights of total one, allowing zero weights. The sum runs over every word, "
                + "including the unique empty word when n=0; image cardinality counts distinct labels.", DescribeRole.Definition),
            Entry("strong-dominance", "StronglyDominates", "One threshold for the two mass functions",
                DominanceDefinition(), AssessedProvenance.FromLiterature(Source),
                DominanceQuotation + " Here D is ℕ embedded in ℝ, a and b are the two mass functions, "
                + "and equality with the real threshold belongs to the lower side. Values beyond the finite support "
                + "have zero mass.", DescribeRole.Definition),
            Entry("claim", "claim", "The strong-dominance conjecture",
                Eqn(Call("claim"), Parenthesized(ClaimBody())), AssessedProvenance.FromLiterature(Source),
                "The positive integers N and n are explicit. The implication has the source direction p≺q.",
                DescribeRole.Definition),
            Entry("result", "result", "Refutation", new Formula.Not(Parenthesized(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                "Take N=4, n=5, p=(48,48,2,2)/100 and q=(50,46,3,1)/100. Their decreasing prefix "
                + "numerators are (48,96,98,100) and (50,96,99,100). The mass numerators at k=2 are "
                + "7874904000 and 7873379340, and those at k=3 are 1560192000 and 1566757440, all over "
                + "100⁵. The strict inequality at 2 forces c<2. Then 3>c requires the opposite of the strict "
                + "inequality at 3. All four coordinates of each vector are positive. This contradicts the universal "
                + "one-threshold assertion while making no assertion against ordinary stochastic dominance.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            declaration == "claim" ? ClaimExplanation(prose) : Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock ConjectureSource() => Paragraph(
        Text("Conjecture, arXiv v1 p. 30: “If p≺q, then the random variable Yₙ defined on the probability space "
            + "(Ω,Pₚ) strongly stochastically dominates the random variable Yₙ defined on the probability space (Ω,"),
        Math(new Formula.Subscript(V("P"), V("q"))), Text(").”"));

    private static BlockSequence ClaimExplanation(string prose)
    {
        var k = V("k");
        var population = V("N");
        return Blocks(
            ConjectureSource(), Paragraph(Text(prose)),
            Paragraph(Text("In Definition 6.1, the majorization premise p≺q uses the decreasing "
                + "rearrangements of p and q. The subscripts with a bar denote positions in these "
                + "rearrangements. Majorization requires both conditions below.")),
            new DocumentBlock.DisplayFormula(Disp(Seq(
                Le(SortedPrefix("p", k), SortedPrefix("q", k)), Comma, Quad,
                Le(D(1), k), Sp, FormulaDsl.Lt, Sp, population))),
            new DocumentBlock.DisplayFormula(Disp(Eqn(SortedPrefix("p", population), SortedPrefix("q", population)))),
            Paragraph(Text("The predicate moreMixed also compares the zero-length prefixes, which gives 0≤0.")));
    }

    private static Formula SortedPrefix(string vector, Formula length)
    {
        var i = V("i");
        return Seq(Sum, Underscore, Grp(i, Sp, FormulaDsl.Eq, Sp, D(1)), Caret, Grp(length), Sp,
            new Formula.Subscript(V(vector), Seq(Overline, Grp(i))));
    }

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        var op = Seq(Operatorname, Grp([.. parts]));
        return args.Length == 0 ? op : new Formula.Apply(op, [.. args]);
    }
    private static Formula App(Formula f, Formula a) => new Formula.Apply(f, [a]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Simplex(Formula n) => Call("Convexity.StdSimplex", R, Call("Fin", n));
    private static Formula Weight(Formula p, Formula i) => App(Call("Convexity.StdSimplex.weights", p), i);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Colon, Sp, R));
    private static Formula Fn(string x, Formula type, Formula body) =>
        Seq(Call("fun"), Sp, V(x), Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula PmfDefinition()
    {
        Formula n = V("n"), population = V("N"), p = V("p"), k = V("k"), w = V("w"), j = V("j");
        var imageCard = Call("Finset.card", Call("Finset.image", w, Call("Finset.univ")));
        var product = Seq(new Formula.Subscript(Prod, Seq(j, Colon, Sp, Call("Fin", n))),
            Sp, Weight(p, App(w, j)));
        var summand = Seq(Call("if"), Sp, Parenthesized(Eqn(imageCard, k)), Sp,
            Call("then"), Sp, Parenthesized(product), Sp, Call("else"), Sp, D(0));
        var sum = Seq(new Formula.Subscript(Sum, Seq(w, Colon, Sp,
            Arrow(Call("Fin", n), Call("Fin", population)))), Sp, Parenthesized(summand));
        return All("N", N, All("p", Simplex(population), All("n", N, All("k", N,
            Eqn(Call("distinctCountPMF", p, n, k), sum)))));
    }
    private static Formula DominanceDefinition()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), k = V("k");
        var body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("c"), R,
            All("k", N, And(Imp(Le(Cast(k), c), Le(App(a, k), App(b, k))),
                Imp(Lt(c, Cast(k)), Le(App(b, k), App(a, k))))));
        return All("a", Arrow(N, R), All("b", Arrow(N, R),
            Eqn(Call("StronglyDominates", a, b), Parenthesized(body))));
    }
    private static Formula ClaimBody()
    {
        Formula population = V("N"), n = V("n"), p = V("p"), q = V("q"), i = V("i");
        var mixed = Call("D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing.moreMixed",
            Parenthesized(Fn("i", Call("Fin", population), Weight(p, i))),
            Parenthesized(Fn("i", Call("Fin", population), Weight(q, i))));
        var conclusion = Call("StronglyDominates", Call("distinctCountPMF", p, n), Call("distinctCountPMF", q, n));
        return All("N", N, All("n", N, Imp(Lt(D(0), population), Imp(Lt(D(0), n),
            All("p", Simplex(population), All("q", Simplex(population), Imp(mixed, conclusion)))))));
    }
}
