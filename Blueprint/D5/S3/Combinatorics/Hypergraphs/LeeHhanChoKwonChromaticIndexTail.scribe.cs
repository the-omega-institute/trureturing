using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypergraphs;

internal sealed class LeeHhanChoKwonChromaticIndexTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/leehhanchokwon2025chromatictail");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed nonempty hyperedge prefix refutes the proposed chromatic-index failure bound.",
        H("The chromatic-index tail conjecture of Lee, Hhan, Cho and Kwon"),
        Blocks(
            Node("chromaticIndex", "Chromatic index of labelled hyperedges", ChromaticFormula(),
                "Supplemental Material §4, p. 17: “Then, the chromatic index χ′(H) of H is exactly the minimum depth of applying all the gates.” The vertices are Fin k and the labelled edge occurrences are Fin alpha. The least natural colour count is taken over functions assigning different colours to distinct intersecting occurrences. Equal nonempty edge sets retain distinct occurrence indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tailProb", "The uniform chromatic-index tail", TailFormula(),
                "Supplemental Material §4, p. 17: “Each edge of H contains v with the probability of m/k. Since each edge is sampled independently”. Each of the alpha coordinates ranges independently over Finset.univ.powersetCard m on Fin k. The numerator counts ordered tuples whose chromatic index exceeds the real threshold x; the denominator counts all ordered tuples. Repeated edges are allowed. Both counts are coerced to Real before division.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("eps", "A particular failure-level family", EpsFormula(),
                "Choose eps(c,t) = 2 raised to minus t raised to 1+c, a particular family in the regime of Supplemental Material §4, p. 18: “if log(1/ϵ) scales with t^{1+c} for some c > 0”. For positive t this gives log₂(1/eps(c,t)) = t^(1+c). The exponent and base in eps are real.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("kParam", "The number of vertices", KFormula(),
                "Supplemental Material §4, p. 17: “Additionally, let us set k = 3 log(t²/ϵ), m = log t, and α = βt log(1/ϵ).” Logarithms are base two. The number of vertices is the natural ceiling of 3 log₂(t²/eps(c,t)); Nat.ceil is the natural ceiling, including its truncation at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("alphaParam", "The number of edge occurrences", AlphaFormula(),
                "Supplemental Material §4, p. 17: “Additionally, let us set k = 3 log(t²/ϵ), m = log t, and α = βt log(1/ϵ).” The number of independently sampled edge occurrences is the natural ceiling of beta times t times log₂(1/eps(c,t)). All products inside Nat.ceil are real.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The failure-probability conjecture", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Supplemental Material §4, p. 18, after Eq. (87): “We conjecture that in this regime, χ′(H) is upper bounded by O(t log t) with a failure probability smaller than ϵ.” The preceding regime is “if log(1/ϵ) scales with t^{1+c} for some c > 0, and β is set by β > 1 + c”. The encoding uses real c and beta with 0 < c and 1+c < beta, the particular family eps(c,t), natural t, m = Nat.ceil(log₂ t), kParam and alphaParam. The big-O bound means that a real constant C works for all natural t beyond a natural threshold T. The probability inequality is strict.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation by a fixed-edge prefix", new Formula.Not(Parenthesized(ClaimBody())),
                "Take c = 1 and beta = 3. A prefix of r copies of one nonempty m-edge needs at least r colours. Counting all possible suffixes gives the lower bound 1/k^(m*r) for the tail whenever the threshold is below r. For any proposed C and T, choose L = max(1,Nat.ceil C), s = max(64,max(T,32*(L+1))), q = 2^s, t = 2^q and r = L*t*q+1. Then k = 3*t²+6*q, m = q and alpha = 3*t³. The inequalities r ≤ alpha, C*t*log₂(t) < r, k ≤ 2^(2*q+3) and (2*q+3)*q*r < t² give tailProb > 2^(−t²) = eps(1,t). The exact binomial bound (m/k)^r and a variant requiring pairwise distinct edges are outside this proof. The weaker probability 1 − O(1/log t) in Eq. (87) is not refuted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("lee-hhan-cho-kwon-2025-chromatic-index-tail"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("lhck-chromatic-tail-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Op(name) : App(Op(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula N() => Op("Nat");
    private static Formula R() => Op("Real");
    private static Formula RealCast(Formula value) => Typed(value, R());
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula EdgeType(Formula k) => Call("Finset", Fin(k));
    private static Formula Fn(Formula from, Formula to) => new Formula.TypeArrow(from, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Log(Formula value) => App(Q("Real", "logb"), D(2), value);
    private static Formula Ceil(Formula value) => App(Q("Nat", "ceil"), value);
    private static Formula Edges(Formula k, Formula m) =>
        App(Q("Finset", "powersetCard"), m, Typed(Q("Finset", "univ"), EdgeType(k)));
    private static Formula Card(Formula value) => App(Q("Finset", "card"), value);
    private static Formula Sample(Formula k, Formula m, Formula alpha) =>
        App(Q("Fintype", "piFinset"), App(Q("Function", "const"), Fin(alpha), Edges(k, m)));

    private static Formula ChromaticFormula()
    {
        Formula k = V("k"), alpha = V("alpha"), e = V("e"), c = V("c"), f = V("f"), i = V("i"), j = V("j");
        Formula intersection = App(Q("Finset", "inter"), App(e, i), App(e, j));
        Formula valid = All("i", Fin(alpha), All("j", Fin(alpha),
            Imp(Ne(i, j), Imp(App(Q("Finset", "Nonempty"), intersection), Ne(App(f, i), App(f, j))))));
        Formula colours = Seq(OpenBrace, c, Colon, Sp, N(), Sp, Mid, Sp,
            Some("f", Fn(Fin(alpha), Fin(c)), valid), CloseBrace);
        return All("k", N(), All("alpha", N(), All("e", Fn(Fin(alpha), EdgeType(k)),
            Eqn(Call("chromaticIndex", e), Call("sInf", colours)))));
    }

    private static Formula TailFormula()
    {
        Formula k = V("k"), m = V("m"), alpha = V("alpha"), x = V("x"), e = V("e");
        Formula predicate = Parenthesized(Seq(Op("fun"), Sp, Typed(e, Fn(Fin(alpha), EdgeType(k))), Sp,
            Mapsto, Sp, Lt(x, RealCast(Call("chromaticIndex", e)))));
        Formula count = Card(App(Q("Finset", "filter"), predicate, Sample(k, m, alpha)));
        Formula denominator = RealCast(Pow(Card(Edges(k, m)), alpha));
        return All("k", N(), All("m", N(), All("alpha", N(), All("x", R(),
            Eqn(Call("tailProb", k, m, alpha, x), new Formula.Fraction(RealCast(count), denominator))))));
    }

    private static Formula EpsFormula() => All("c", R(), All("t", N(),
        Eqn(Call("eps", V("c"), V("t")), Pow(Typed(D(2), R()),
            new Formula.Negate(Pow(RealCast(V("t")), Add(D(1), V("c"))))))));

    private static Formula KFormula() => All("c", R(), All("t", N(),
        Eqn(Call("kParam", V("c"), V("t")), Ceil(Mul(D(3),
            Log(new Formula.Fraction(Pow(RealCast(V("t")), D(2)), Call("eps", V("c"), V("t")))))))));

    private static Formula AlphaFormula() => All("c", R(), All("beta", R(), All("t", N(),
        Eqn(Call("alphaParam", V("c"), V("beta"), V("t")), Ceil(Mul(Mul(V("beta"), RealCast(V("t"))),
            Log(new Formula.Fraction(D(1), Call("eps", V("c"), V("t"))))))))));

    private static Formula ClaimBody()
    {
        Formula c = V("c"), beta = V("beta"), t = V("t");
        Formula threshold = Mul(Mul(V("C"), RealCast(t)), Log(RealCast(t)));
        Formula tail = Call("tailProb", Call("kParam", c, t), Ceil(Log(RealCast(t))),
            Call("alphaParam", c, beta, t), threshold);
        return All("c", R(), All("beta", R(), Imp(Lt(D(0), c), Imp(Lt(Add(D(1), c), beta),
            Some("C", R(), Some("T", N(), All("t", N(), Imp(Leq(V("T"), t), Lt(tail, Call("eps", c, t))))))))));
    }
}
