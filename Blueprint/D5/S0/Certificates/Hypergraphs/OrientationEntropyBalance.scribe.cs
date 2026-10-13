using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Hypergraphs;

internal sealed class OrientationEntropyBalanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/pelekis2019orientationentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unbalanced three-edge multigraph maximises orientation-count entropy.",
        H("Entropy maximisers need not have balanced degrees"),
        Blocks(
            TheoremNode("orientations_eq", "Orientations as a product of finite sets",
                OrientationsFormula(),
                "The functions choosing a member of every edge are exactly Fintype.piFinset E. "
                + "This equality converts the orientation counts in entropyX to product-set counts."),
            TheoremNode("sum_entropy_formula", "Entropy from the count product",
                SumEntropyFormula(),
                "For nonnegative integer counts with positive total N, the base-two entropy "
                + "is log₂ N minus the logarithm of their count product divided by N. "
                + "The factor for a zero count is 0^0=1. This identity compares the entropies "
                + "of the three-vertex maximiser and the four-vertex circular competitor."),
            Node("X", "The number of vertices reached", XFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Page 122 states: “In other words, X_C is the number of vertices with non-zero "
                + "in-degree after a random orientation on the edges of H_C and the above mentioned "
                + "question on coloured dice can be equivalently expressed as follows.” The image "
                + "of o contains exactly the vertices selected by at least one edge. E labels the "
                + "edge family; the value depends only on o."),
            Node("entropyX", "Shannon entropy in bits", EntropyFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Page 120 states: “The Shannon entropy (or entropy, for short) of a random variable "
                + "X that takes values on a finite set S is defined as H(X) = −∑_{s∈S} P[X = s] · "
                + "log P[X = s], with the convention 0 log 0 = 0. Throughout the text, log(·) denotes "
                + "logarithm with base 2.” Page 121 states: “Here and later, the phrase random "
                + "orientation on the edges of a hypergraph H expresses the fact that each edge in H "
                + "is oriented towards one of its elements with probability 1/r, where each edge is "
                + "oriented independently of all other edges.” The two filters count orientations "
                + "with X=k. Every r-uniform edge family has r^m equally likely orientations. "
                + "The range includes k=0 through n; p is a real probability, so its division is real."),
            Node("deg", "Vertex degree with edge multiplicity", DegreeFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Page 122 states: “Given a hypergraph H = (V,ℰ) and a vertex v ∈ V, we denote by "
                + "deg_H(v) the number of edges in ℰ that contain v.” Counting edge indices retains "
                + "repeated edges."),
            Node("claim", "Conjecture 1.3", ClaimFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Conjecture 1.3, p. 122, states: “Let the positive integers m,n,r be such that "
                + "m ≥ n > r ≥ 2. A hypergraph H = (V,ℰ) from D_{n,m,r} for which it holds "
                + "H(X_H) ≥ H(X_G), for all G ∈ D_{n,m,r} is such that "
                + "|deg_H(v₁) − deg_H(v₂)| ≤ 1, for all v₁,v₂ ∈ V.” Page 121 states: “Here and "
                + "later, the class consisting of all r-uniform multi-hypergraphs on n vertices and "
                + "m edges is denoted by D_{n,m,r}.” Vertices are Fin n and edges are indexed by "
                + "Fin m. Repeated edges and isolated vertices are allowed. The two ordered vertex "
                + "choices express both signs of the absolute-value bound. The assumptions imply "
                + "that n,m,r are positive."),
            Describe.Lean(DescribeId.Create("pel-balance-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Conjecture 1.3 is false"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take n=m=3, r=2 and the edges {0,1},{0,1},{0,2}. The degrees are (3,2,1), "
                    + "and the counts for X=0,1,2,3 are (0,1,5,2) out of eight orientations. "
                    + "All 27 ordered edge tuples have count product ∏c^c at least 12500, equal to "
                    + "this example's 5^5·2^2. For a common positive denominator N and counts "
                    + "summing to N, entropy equals log₂ N − log₂(∏c^c)/N, with 0^0=1. "
                    + "Monotonicity of the logarithm therefore proves global maximality in this "
                    + "class, although the degrees at vertices zero and two differ by two."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pelekis-2018-orientation-entropy-balance"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock TheoremNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("pel-balance-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula OrientationsFormula() => Parameters(Equal(
        QCall("Finset", "filter", Lambda("o", OrientationType(),
            All("i", Call("Fin", Id("m")),
                Rel(Call("o", Id("i")), FormulaRelationOperator.MemberOf, Call("E", Id("i"))))),
            Q("Finset", "univ")),
        QCall("Fintype", "piFinset", Id("E"))));

    private static Formula SumEntropyFormula()
    {
        var c = Call("c", Id("i")); var n = Id("N");
        var probability = new Formula.Fraction(Coerce(c, Reals()), Coerce(n, Reals()));
        var sumCounts = OverSet(F.Sum, c);
        var product = OverSet(F.Prod, new Formula.Power(c, c));
        var entropy = OverSet(F.Sum,
            Multiply(new Formula.Negate(probability), QCall("Real", "logb", Num(2), probability)));
        var value = Subtract(QCall("Real", "logb", Num(2), Coerce(n, Reals())),
            new Formula.Fraction(QCall("Real", "logb", Num(2), Coerce(product, Reals())),
                Coerce(n, Reals())));
        return All("A", Id("Type"), All("s", Call("Finset", Id("A")),
            All("c", new Formula.TypeArrow(Id("A"), Naturals()), All("N", Naturals(),
                Implies(Lt(Num(0), n), Implies(Equal(sumCounts, n), Equal(entropy, value)))))));
    }

    private static Formula OverSet(Formula symbol, Formula body) =>
        F.Seq(new Formula.Subscript(symbol,
            Rel(Id("i"), FormulaRelationOperator.MemberOf, Id("s"))), F.Sp, Parenthesized(body));

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("pel-balance-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula XFormula() => Parameters(
        All("o", OrientationType(), Equal(Call("X", Id("E"), Id("o")),
            QCall("Finset", "card", QCall("Finset", "image", Id("o"), Q("Finset", "univ"))))));

    private static Formula EntropyFormula()
    {
        var o = Id("o"); var k = Id("k"); var p = Id("p");
        var admissible = QCall("Finset", "filter",
            Lambda("o", OrientationType(), All("i", Call("Fin", Id("m")),
                Rel(Call("o", Id("i")), FormulaRelationOperator.MemberOf, Call("E", Id("i"))))),
            Q("Finset", "univ"));
        var count = QCall("Finset", "card", QCall("Finset", "filter",
            Lambda("o", OrientationType(), Equal(Call("X", Id("E"), o), k)), admissible));
        var probability = new Formula.Fraction(Coerce(count, Reals()),
            new Formula.Power(Coerce(Id("r"), Reals()), Id("m")));
        var summand = F.Seq(Id("let"), F.Sp, p, F.Sp, F.Colon, F.Eq, F.Sp,
            probability, F.Semi, F.Sp,
            Multiply(new Formula.Negate(p), QCall("Real", "logb", Num(2), p)));
        var sum = F.Seq(new Formula.Subscript(F.Sum,
            Rel(k, FormulaRelationOperator.MemberOf, QCall("Finset", "range", Add(Id("n"), Num(1))))),
            F.Sp, Parenthesized(summand));
        return All("n", Naturals(), All("m", Naturals(), All("r", Naturals(),
            All("E", EdgeType(), Equal(Call("entropyX", Id("r"), Id("E")), sum)))));
    }

    private static Formula DegreeFormula() => Parameters(All("v", Call("Fin", Id("n")),
        Equal(Call("deg", Id("E"), Id("v")), QCall("Finset", "card",
            QCall("Finset", "filter", Lambda("i", Call("Fin", Id("m")),
                Rel(Id("v"), FormulaRelationOperator.MemberOf, Call("E", Id("i")))),
                Q("Finset", "univ"))))));

    private static Formula ClaimFormula()
    {
        var balance = All("v1", Call("Fin", Id("n")), All("v2", Call("Fin", Id("n")),
            Le(Subtract(Coerce(Call("deg", Id("E"), Id("v1")), new Formula.Integers()),
                Coerce(Call("deg", Id("E"), Id("v2")), new Formula.Integers())), Num(1))));
        var maximum = All("F", EdgeType(), Implies(Uniform("F"),
            Le(Call("entropyX", Id("r"), Id("F")), Call("entropyX", Id("r"), Id("E")))));
        var proposition = All("n", Naturals(), All("m", Naturals(), All("r", Naturals(),
            Implies(Le(Id("n"), Id("m")), Implies(Lt(Id("r"), Id("n")),
                Implies(Le(Num(2), Id("r")), All("E", EdgeType(),
                    Implies(Uniform("E"), Implies(maximum, balance)))))))));
        return Equal(Id("claim"), proposition);
    }

    private static Formula Uniform(string edge) => All("i", Call("Fin", Id("m")),
        Equal(QCall("Finset", "card", Call(edge, Id("i"))), Id("r")));
    private static Formula Parameters(Formula body) => All("n", Naturals(),
        All("m", Naturals(), All("E", EdgeType(), body)));
    private static Formula EdgeType() => new Formula.TypeArrow(Call("Fin", Id("m")),
        Call("Finset", Call("Fin", Id("n"))));
    private static Formula OrientationType() => new Formula.TypeArrow(Call("Fin", Id("m")),
        Call("Fin", Id("n")));
    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(Id("N")));
    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(Id("R")));
    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(F.Seq(value, F.Sp, F.Colon, F.Sp, type));
    private static Formula Lambda(string name, Formula type, Formula body) =>
        F.Seq(Id("fun"), F.Sp, Parenthesized(F.Seq(Id(name), F.Sp, F.Colon, F.Sp, type)),
            F.Sp, F.Mapsto, F.Sp, body);
    private static Formula Q(string owner, string name) => F.Seq(F.Id(owner), F.Dot, F.Id(name));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Q(owner, name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
}
