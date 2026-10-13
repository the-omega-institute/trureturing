using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ExtremalDensity;

internal sealed class ThreeClassHomomorphismLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ExtremalDensity/ThreeClassHomomorphismLimit.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/daysarkar2021extremaldensities");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-class graph homomorphism densities equal their finite weighting sum.",
        H("Three-class homomorphism limits"),
        Blocks(
            Entry("yellow-weight", "yW", "Yellow weight", Weight("yW",
                Mul(App(Qualified("Real", "sqrt"), V("beta")), V("q"))),
                "Day and Sarkar, §3, p. 4: y(q) = √β q. The yellow class has asymptotic size y(q)n.", true),
            Entry("red-weight", "rW", "Red weight", Weight("rW",
                Sub(N(1), Radical())),
                "Day and Sarkar, §3, p. 4: r(q) = 1 − √(1 − β(1 − q²)). The red class has asymptotic size r(q)n.", true),
            Entry("blue-weight", "bW", "Blue weight", Weight("bW",
                Sub(Radical(), Mul(App(Qualified("Real", "sqrt"), V("beta")), V("q")))),
                "Day and Sarkar, §3, p. 4: b(q) = √(1 − β(1 − q²)) − √β q. The blue class has asymptotic size b(q)n.", true),
            Entry("vertex-classes", "vertexClass", "Floor-sized classes", VertexClass(),
                "Vertices are numbered by Fin n. Yellow has index 1, red index 0 and blue index 2. "
                + "The first Nat.floor(yW beta q * n) vertices are yellow; the next Nat.floor(rW beta q * n) "
                + "are red; the rest are blue. Nat.floor is the nonnegative natural floor. "
                + "The source omits floors in its asymptotic class sizes.", false),
            Entry("allowed-classes", "classAllowed", "Allowed class pairs", Allowed(),
                "A pair of yellow classes is allowed. A pair with at least one red class is allowed. "
                + "Blue–blue and yellow–blue pairs are excluded.", false),
            Entry("three-class-graph", "tGraph", "The finite T graph", Graph(),
                "Day and Sarkar, §2, p. 4, verbatim: “The sets Y_T and R_T both span cliques, while B_T "
                + "is an independent set. Also, every vertex in R_T is connected to every vertex in Y_T and B_T.” "
                + "There are no yellow–blue edges. The formula specifies the adjacency relation of the "
                + "SimpleGraph on Fin n; distinct endpoints exclude loops.", true),
            Entry("homomorphism-count", "homCount", "Labelled homomorphisms", HomCount(),
                "Day and Sarkar, §2, p. 3, verbatim: “A graph homomorphism from G_l to H is a map "
                + "f:V(G_l)→V(H) such that {f(u),f(w)}∈E(H) for all {u,w}∈E(G_l). We write hom(G_l,H) "
                + "for the number of homomorphisms from G_l to H.” The vertex sets here are Fin v and Fin n. "
                + "The subtype counts all adjacency-preserving functions, including noninjective ones.", true),
            Entry("homomorphism-density", "tDens", "The literal asymptotic density", Density(),
                "Day and Sarkar, §2, p. 3 define t(G_l,H_n) as lim(n→∞) hom(G_l,H_n)/n^v. "
                + "The displayed limUnder at Filter.atTop is that limit for the floor-sized T graphs. "
                + "The integer cardinality and vertex number are coerced to real numbers before division.", true),
            Entry("class-weight", "colourWeight", "Weight of one class", ColourWeight(),
                "Class 0 receives r(q), class 1 receives y(q), and class 2 receives b(q), "
                + "as in the red, yellow and blue sets of §3, pp. 4–5.", true),
            Entry("half-integral-weight", "independentWeight", "Half-integral weights", IndependentWeight(),
                "The three indices 0, 1 and 2 encode the fractional independence weights 0, 1/2 and 1. "
                + "The natural value of the index is coerced to a real number before division by 2.", false),
            Entry("admissible-colouring", "admissible", "Fractional independence colourings", Admissible(),
                "Day and Sarkar, §2, p. 3, verbatim: “Given a graph G, a function φ:V(G)→[0,1] such that "
                + "φ(u)+φ(w)≤1 for all {u,w}∈E(G) is known as a fractional independence weighting of G.” "
                + "Here φ takes the three values 0, 1/2 and 1, represented by c:Fin v→Fin 3.", true),
            Entry("weighting-sum", "weightingSum", "The finite weighting sum", WeightingSum(),
                "Sum the product of class weights over all half-integral fractional independence weightings. "
                + "Colourings that violate an edge condition contribute zero. This is the sum in "
                + "Day and Sarkar's Lemma 1, §3, p. 5 (arXiv v1).", true),
            Entry("weights-valid", "weights_valid", "Nonnegative weights summing to one", ValidWeights(),
                "For beta and q in [0,1], the yellow, red and blue weights are nonnegative and sum to one. "
                + "Their natural floors therefore fit into the n-vertex carrier.", false, DescribeRole.Theorem),
            Entry("density-weighting-identity", "tDens_eq_weightingSum", "Counting the density", LimitIdentity(),
                "For every finite labelled SimpleGraph and every beta and q in [0,1], the homomorphism "
                + "limit equals the weighting sum. The ideal count partitions functions by their class map. "
                + "A function counted ideally but failing to preserve adjacency identifies the endpoints of "
                + "an edge. Restricting such a function away from one endpoint gives the bound n^(v−1) "
                + "for each ordered pair; the total error is at most v² n^(v−1). Dividing by n^v makes "
                + "this error tend to zero, while each floor-sized class fraction tends to its weight. "
                + "Nonadjacent vertices may share an image. The argument includes v=0 and zero class weights.",
                true, DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool literature, DescribeRole role = DescribeRole.Definition) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula N(int n) => new Formula.Number(n);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula EqTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Cast(Formula a) => Parenthesized(Seq(a, Colon, Sp, Real));
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula Icc => App(Qualified("Set", "Icc"), N(0), N(1));
    private static Formula Member(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula LeTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula IfThenElse(Formula p, Formula a, Formula b) =>
        Seq(Operatorname, Grp(V("ite")), Parenthesized(p), Parenthesized(a), Parenthesized(b));
    private static Formula GraphType(Formula n) => Call("SimpleGraph", Fin(n));
    private static Formula WeightCall(string name) => Call(name, V("beta"), V("q"));
    private static Formula Radical() => App(Qualified("Real", "sqrt"),
        Sub(N(1), Mul(V("beta"), Sub(N(1), Pow(V("q"), N(2))))));
    private static Formula Weight(string name, Formula body) =>
        All("beta", Real, All("q", Real, EqTo(WeightCall(name), body)));
    private static Formula FloorSize(string name) => App(Qualified("Nat", "floor"), Mul(WeightCall(name), Cast(V("n"))));
    private static Formula VertexClass() => All("beta", Real, All("q", Real, All("n", Natural,
        All("i", Fin(V("n")), EqTo(Call("vertexClass", V("beta"), V("q"), V("n"), V("i")),
            IfThenElse(Rel(Val(V("i")), FormulaRelationOperator.LessThan, FloorSize("yW")), N(1),
                IfThenElse(Rel(Val(V("i")), FormulaRelationOperator.LessThan,
                    Add(FloorSize("yW"), FloorSize("rW"))), N(0), N(2))))))));
    private static Formula Allowed() => All("a", Fin(N(3)), All("b", Fin(N(3)),
        EqTo(Call("classAllowed", V("a"), V("b")),
            Or(And(EqTo(V("a"), N(1)), EqTo(V("b"), N(1))),
                Or(And(EqTo(V("a"), N(0)), EqTo(V("b"), N(0))),
                    Or(EqTo(V("a"), N(0)), EqTo(V("b"), N(0))))))));
    private static Formula Graph() => All("beta", Real, All("q", Real, All("n", Natural,
        All("i", Fin(V("n")), All("j", Fin(V("n")),
            new Formula.Logic(App(Seq(Parenthesized(Call("tGraph", V("beta"), V("q"), V("n"))),
                Dot, Operatorname, Grp(V("Adj"))), V("i"), V("j")), FormulaLogicOperator.Iff,
                And(Rel(V("i"), FormulaRelationOperator.NotEqual, V("j")), Call("classAllowed",
                    Call("vertexClass", V("beta"), V("q"), V("n"), V("i")),
                    Call("vertexClass", V("beta"), V("q"), V("n"), V("j"))))))))));
    private static Formula Adj(string graph, Formula i, Formula j) =>
        App(Seq(V(graph), Dot, Operatorname, Grp(V("Adj"))), i, j);
    private static Formula Subtype(string x, Formula type, Formula p) =>
        Seq(OpenBrace, V(x), Colon, Sp, type, Sp, Mid, Sp, p, CloseBrace);
    private static Formula HomCount() => All("v", Natural, All("n", Natural,
        All("G", GraphType(V("v")), All("H", GraphType(V("n")),
            EqTo(Call("homCount", V("G"), V("H")), App(Qualified("Nat", "card"),
                Subtype("f", Arrow(Fin(V("v")), Fin(V("n"))),
                    All("i", Fin(V("v")), All("j", Fin(V("v")),
                        Imp(Adj("G", V("i"), V("j")), Adj("H", Call("f", V("i")), Call("f", V("j")))))))))))));
    private static Formula Density() => All("v", Natural, All("G", GraphType(V("v")),
        All("beta", Real, All("q", Real, EqTo(Call("tDens", V("G"), V("beta"), V("q")),
            Call("limUnder", Qualified("Filter", "atTop"),
                Parenthesized(Seq(V("fun"), Sp, V("n"), Colon, Sp, Natural, Sp, Mapsto, Sp,
                    new Formula.Fraction(Cast(Call("homCount", V("G"),
                        Call("tGraph", V("beta"), V("q"), V("n")))), Pow(Cast(V("n")), V("v")))))))))));
    private static Formula ColourWeight() => All("beta", Real, All("q", Real, All("a", Fin(N(3)),
        EqTo(Call("colourWeight", V("beta"), V("q"), V("a")),
            IfThenElse(EqTo(V("a"), N(0)), WeightCall("rW"),
                IfThenElse(EqTo(V("a"), N(1)), WeightCall("yW"), WeightCall("bW")))))));
    private static Formula IndependentWeight() => All("a", Fin(N(3)),
        EqTo(Call("independentWeight", V("a")), new Formula.Fraction(Cast(Val(V("a"))), N(2))));
    private static Formula Admissible() => All("v", Natural, All("G", GraphType(V("v")),
        All("c", Arrow(Fin(V("v")), Fin(N(3))), EqTo(Call("admissible", V("G"), V("c")),
            Parenthesized(All("i", Fin(V("v")), All("j", Fin(V("v")), Imp(Adj("G", V("i"), V("j")),
                LeTo(Add(Call("independentWeight", Call("c", V("i"))),
                    Call("independentWeight", Call("c", V("j")))), N(1))))))))));
    private static Formula WeightingSum() => All("v", Natural, All("G", GraphType(V("v")),
        All("beta", Real, All("q", Real, EqTo(Call("weightingSum", V("G"), V("beta"), V("q")),
            Seq(new Formula.Subscript(Sum, Seq(V("c"), Colon, Arrow(Fin(V("v")), Fin(N(3))))),
                Parenthesized(IfThenElse(Call("admissible", V("G"), V("c")),
                    Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Fin(V("v")))),
                        Call("colourWeight", V("beta"), V("q"), Call("c", V("i")))), N(0)))))))));
    private static Formula ValidWeights() => All("beta", Real, All("q", Real,
        Imp(And(Member(V("beta"), Icc), Member(V("q"), Icc)),
            And(LeTo(N(0), WeightCall("yW")), And(LeTo(N(0), WeightCall("rW")),
                And(LeTo(N(0), WeightCall("bW")), EqTo(Add(Add(WeightCall("yW"),
                    WeightCall("rW")), WeightCall("bW")), N(1))))))));
    private static Formula LimitIdentity() => All("v", Natural, All("G", GraphType(V("v")),
        All("beta", Real, All("q", Real,
            Imp(And(Member(V("beta"), Icc), Member(V("q"), Icc)),
                EqTo(Call("tDens", V("G"), V("beta"), V("q")),
                    Call("weightingSum", V("G"), V("beta"), V("q"))))))));
}
