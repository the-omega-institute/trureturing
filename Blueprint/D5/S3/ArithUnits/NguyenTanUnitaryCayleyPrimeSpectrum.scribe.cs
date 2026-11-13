using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class NguyenTanUnitaryCayleyPrimeSpectrumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/ArithUnits/NguyenTanUnitaryCayleyPrimeSpectrum";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/nguyentan2025supercharacters");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime connected and anti-connected unitary Cayley graphs can have zero as an adjacency eigenvalue.",
        H("Primeness does not imply adjacency nonsingularity"),
        Blocks(
            Node("IsFrobenius", "A nondegenerate functional", FrobeniusFormula(),
                "Section 4.1, page 12: \"being Frobenius means that R is a Z/n algebra equipped with a non-degenerate Z/n linear functional ψ : R → Z/n. Here, non-degenerate means that the kernel of ψ does not contain any non-zero ideal in R.\" The integer n annihilates R, and the additive homomorphism psi is automatically Z/n-linear. Every ideal contained in its kernel is the zero ideal.",
                AssessedProvenance.FromLiterature(Source)),
            Node("unitaryCayley", "The graph on the additive ring", CayleyFormula(),
                "Section 3.1, page 7: \"Let R be a finite commutative ring and S be a symmetric subset of R\"; \"we fix a subgroup U of R× such that −1 ∈ U (this will ensure that all relevant generating sets are symmetric).\" SimpleGraph.fromRel makes the relation symmetric and removes loops. Under minus-one membership, two vertices a and b are adjacent exactly when a − b is the value of a unit in U. Units.val is the coercion to R.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsHomogeneousSet", "Homogeneous vertex sets", HomogeneousFormula(),
                "Section 3.3, page 10: \"A subset X in a graph G is called a homogeneous set if every vertex in V(G) \\ X is adjacent to either all or none of the vertices in X.\" The two alternatives are separate universal statements over X; the outside vertex v may choose either alternative.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsPrimeGraph", "No non-trivial homogeneous set", PrimeFormula(),
                "Section 3.3, page 10: \"A homogeneous set X with 2 ≤ |X| < |V(G)| is called non-trivial. The graph G is said to be prime if it does not contain any non-trivial homogeneous sets.\" Finset represents every subset of the finite vertex type. A homogeneous finset has cardinality less than two or equal to Fintype.card V.",
                AssessedProvenance.FromLiterature(Source)),
            Node("HasZeroEigenvalue", "A nonzero vector in the adjacency kernel", ZeroEigenvalueFormula(),
                "Zero is an adjacency eigenvalue exactly when the complex adjacency matrix annihilates a nonzero vector.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Nguyen–Tân Question 4.17", Logic(Q("claim"),
                    FormulaLogicOperator.Iff, ClaimBody()),
                "Question 4.17, page 19 of arXiv:2508.10348v1: \"Suppose that Γ(R, U) is both connected and anti-connected. Is it true that Γ(R, U) is prime if and only if 0 is not an eigenvalue?\" The affirmative proposition ranges over finite commutative Frobenius rings and subgroups of their units containing minus one. Anti-connected means that the complement is connected. Zero is an eigenvalue exactly when the complex adjacency matrix annihilates a nonzero vector; the HasZeroEigenvalue definition node displays this condition in full.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("nt2508-result"),
                DeclarationHandle.Create(Module + ".result"), H("The affirmative proposition is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite commutative group G of even cardinality at least three, the group algebra MonoidAlgebra (ZMod 2) G is Frobenius: its coefficient at the identity detects every nonzero ideal after multiplication by a suitable inverse basis element. The subgroup of basis units contains minus one. Coefficient vectors identify its Cayley graph with the binary Hamming graph. Coordinate changes connect the graph, and two changes through the complement connect each pair that differs in one coordinate. A proper homogeneous set in a connected triangle-free graph is independent, and two of its vertices would have identical neighbourhoods. Three available coordinates exclude such twins. A product of coordinate signs has eigenvalue card G − 2 card s; selecting half the coordinates gives a nonzero vector with eigenvalue zero. The cyclic group Multiplicative (ZMod d) therefore gives the family for every even d at least four. The settling contradiction uses d = 4. A polynomial-quotient isomorphism, a complete eigenbasis and the general multiplicity of zero are separate questions."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nguyen-tan-2025-unitary-cayley-prime-zero-eigenvalue"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("nt2508-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Q(params string[] names) => Seq([.. names.SelectMany(
        (name, index) => index == 0
            ? new Formula[] { Operatorname, Grp(F.Id(name)) }
            : [Dot, Operatorname, Grp(F.Id(name))])]);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Comma, Sp, body);
    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(Parenthesized(left), operation, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula EqFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula LambdaFormula(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula FunctionType(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Units(Formula type) => Call("Units", type);
    private static Formula Graph(Formula type) => Call("SimpleGraph", type);
    private static Formula Gamma(Formula ring, Formula subgroup) => Call("unitaryCayley", ring, subgroup);
    private static Formula Connected(Formula graph) => App(Q("SimpleGraph", "Connected"), graph);
    private static Formula Complement(Formula graph) => new Formula.Power(Parenthesized(graph), F.Id("c"));

    private static Formula FrobeniusFormula()
    {
        Formula r = F.Id("R"), n = F.Id("n"), psi = F.Id("psi"), ideal = F.Id("I"), x = F.Id("x");
        var kernel = All("x", r, ImpliesFormula(Member(x, ideal), EqFormula(App(psi, x), D(0))));
        var ideals = All("I", Call("Ideal", r), ImpliesFormula(kernel, EqFormula(ideal, Seq(Perp))));
        var body = Ex("n", Nat, And(EqFormula(Cast(n, r), D(0)),
            Ex("psi", Call("AddMonoidHom", r, Call("ZMod", n)), ideals)));
        return All("R", F.Id("Type"), Instance("CommRing", r,
            Logic(Call("IsFrobenius", r), FormulaLogicOperator.Iff, body)));
    }

    private static Formula CayleyFormula()
    {
        Formula r = F.Id("R"), u = F.Id("U"), a = F.Id("a"), b = F.Id("b");
        var relation = LambdaFormula("a", r, LambdaFormula("b", r,
            Ex("u", Units(r), And(Member(F.Id("u"), u),
                EqFormula(new Formula.Binary(a, FormulaBinaryOperator.Subtract, b),
                    App(Q("Units", "val"), F.Id("u")))))));
        var body = EqFormula(Gamma(r, u), App(Q("SimpleGraph", "fromRel"), relation));
        return All("R", F.Id("Type"), Instance("CommRing", r,
            All("U", Call("Subgroup", Units(r)), body)));
    }

    private static Formula HomogeneousFormula()
    {
        Formula vtype = F.Id("V"), g = F.Id("G"), set = F.Id("X"), v = F.Id("v"), x = F.Id("x");
        var adjacent = App(Q("SimpleGraph", "Adj"), g, v, x);
        var all = All("x", vtype, ImpliesFormula(Member(x, set), adjacent));
        var none = All("x", vtype, ImpliesFormula(Member(x, set), new Formula.Not(adjacent)));
        var body = All("v", vtype, ImpliesFormula(new Formula.Not(Parenthesized(Member(v, set))),
            Logic(all, FormulaLogicOperator.Or, none)));
        return All("V", F.Id("Type"), All("G", Graph(vtype), All("X", Call("Set", vtype),
            Logic(Call("IsHomogeneousSet", g, set), FormulaLogicOperator.Iff, body))));
    }

    private static Formula PrimeFormula()
    {
        Formula vtype = F.Id("V"), g = F.Id("G"), x = F.Id("X");
        var card = App(Q("Finset", "card"), x);
        var sizes = Logic(new Formula.Relation(card, FormulaRelationOperator.LessThan, D(2)),
            FormulaLogicOperator.Or, EqFormula(card, App(Q("Fintype", "card"), vtype)));
        var body = All("X", Call("Finset", vtype), ImpliesFormula(
            Call("IsHomogeneousSet", g, Cast(x, Call("Set", vtype))), sizes));
        return All("V", F.Id("Type"), Instance("Fintype", vtype, All("G", Graph(vtype),
            Logic(Call("IsPrimeGraph", g), FormulaLogicOperator.Iff, body))));
    }

    private static Formula ZeroEigenvalueBody(Formula vertexType, Formula graph)
    {
        Formula v = F.Id("v");
        var matrix = App(Q("SimpleGraph", "adjMatrix"), Complex, graph);
        return Ex("v", FunctionType(vertexType, Complex),
            And(new Formula.Not(Parenthesized(EqFormula(v, D(0)))),
                EqFormula(App(Q("Matrix", "mulVec"), matrix, v), D(0))));
    }

    private static Formula ZeroEigenvalueFormula()
    {
        Formula vtype = F.Id("V"), g = F.Id("G");
        return All("V", F.Id("Type"), Instance("Fintype", vtype,
            All("G", Graph(vtype), Logic(Call("HasZeroEigenvalue", g),
                FormulaLogicOperator.Iff, ZeroEigenvalueBody(vtype, g)))));
    }

    private static Formula ClaimBody()
    {
        Formula r = F.Id("R"), u = F.Id("U");
        var graph = Gamma(r, u);
        var prime = Logic(Call("IsPrimeGraph", graph), FormulaLogicOperator.Iff,
            new Formula.Not(Parenthesized(Call("HasZeroEigenvalue", graph))));
        var hypotheses = ImpliesFormula(Member(Cast(Seq(Minus, D(1)), Units(r)), u),
            ImpliesFormula(Connected(graph), ImpliesFormula(Connected(Complement(graph)), prime)));
        return All("R", F.Id("Type"), Instance("CommRing", r, Instance("Fintype", r,
            ImpliesFormula(Call("IsFrobenius", r), All("U", Call("Subgroup", Units(r)), hypotheses)))));
    }
}
