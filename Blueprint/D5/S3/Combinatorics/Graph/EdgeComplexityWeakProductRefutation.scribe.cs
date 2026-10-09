using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class EdgeComplexityWeakProductRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026edgecomplexity");
    private const string Question = "Remark. The coprimality hypothesis is not merely a technicality in the present argument: it is what permits the product labeling to be viewed as a cyclic labeling. Proposition 3.7 does not prove closure under arbitrary weak products. Consequently, unrestricted closure of the equality class under the weak product has not been established. Whether such closure holds is a natural open question.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "K3 times K3 refutes unrestricted weak-product closure of energy equality.",
        H("Weak products do not preserve edge-complexity equality"), Blocks(
            Node("f", "Labeled adjacency indicator", Indicator(),
                "Section 1, page 1: “Let G = (V, E) be a simple graph with at least one edge and |V| = N. After choosing a labeling of the vertices by Z_N, identify the adjacency matrix with the edge indicator” followed by f : Z_N × Z_N → {0, 1}. A labeling sigma is an equivalence from V to Fin (Fintype.card V). The values zero and one are real numbers.", DescribeRole.Definition, Lit()),
            Node("fhat", "Fourier transform", Transform(),
                "Section 1, page 1: “Its two-dimensional discrete Fourier transform is” the displayed sum. Fin N represents the cyclic labels; val reads their natural-number representatives. Both the indicator and the natural-number expression in the exponent are coerced to Complex. Division here is in Complex.", DescribeRole.Definition, Lit()),
            Node("FR", "Fourier ratio", Ratio(),
                "Section 1, page 2: “The Fourier ratio of f is” the displayed quotient of the entrywise l1 norm by the Frobenius norm. Both sums range over all Fin N labels; the denominator is the real square root of the sum of squared complex norms.", DescribeRole.Definition, Lit()),
            Node("FRmin", "Minimum over labelings", Minimum(),
                "Section 1, page 2: “If fσ is the adjacency matrix produced by a vertex labeling σ, the edge complexity introduced in [7] is” the minimum Fourier ratio over all labelings. Finset.univ is the finite set of equivalences V to Fin (Fintype.card V), which contains Fintype.equivFin V. Its inf' is its attained minimum, including for an empty vertex type.", DescribeRole.Definition, Lit()),
            Node("energy", "Graph energy", Energy(),
                "Section 1, page 2: “The graph energy is” the sum of the absolute adjacency eigenvalues, “where λ1(G), . . . , λN(G) are the adjacency eigenvalues.” The Hermitian proof is G.isHermitian_adjMatrix Real; eigenvalues are real, indexed by V.", DescribeRole.Definition, Lit()),
            Node("size", "Number of edges", GraphBind(v => EqOf(Call("size", g), MemberCall(g, "edgeFinset", "card"))),
                "The size s in Theorem 1.1 counts unoriented edges once. The cardinality of G.edgeFinset implements that convention.", DescribeRole.Definition, Lit()),
            Node("AttainsEquality", "Energy equality with a positive edge count", Equality(),
                "Theorem 1.1, page 2, states the lower bound FR_min(G) at least E(G)/sqrt(2s) for size s greater than zero. AttainsEquality is exactly a positive size together with equality in that bound.", DescribeRole.Definition, Lit()),
            Node("claim", "Unrestricted weak-product closure", Claim(),
                "Remark after Corollary 3.10, page 18: “" + Question + "” The equality class is AttainsEquality. The quantifiers cover all finite vertex types and simple graphs, with decidable adjacency. Definition 3.1, page 15: “Definition 3.1. Let G and H be graphs. Their weak product G × H has vertex set V(G) × V(H), and (g₁, h₁) is adjacent to (g₂, h₂) if and only if g₁ is adjacent to g₂ in G and h₁ is adjacent to h₂ in H.” The operation in the formula is the existing dirProd, with exactly that adjacency relation.", DescribeRole.Definition, Lit()),
            Node("result", "The closure assertion is false", Disp(new Formula.Not(F.Id("claim"))),
                "Both factors are the complete graph on Fin 3. Their Fourier ratio minimum is 4/sqrt(6), their energy is four and their size is three. The product has size eighteen and energy sixteen. For every labeling its Fourier ratio is strictly greater than 8/3. Equality would make its squared adjacency circulant; the identity A squared equals 2J plus 2I minus A would then make A circulant. No zero-one circulant matrix of order nine satisfies that identity. The sign matrix (6A+3I-2J)/9 supplies the norm bound and its equality conditions.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static readonly Formula v = F.Id("V"), w = F.Id("W"), g = F.Id("G"), h = F.Id("H"), n = F.Id("N"), a = F.Id("a");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Card(Formula type) => QCall(["Fintype", "card"], type);
    private static Formula Label => Call("Equiv", v, Fin(Card(v)));
    private static Formula Array => new Formula.TypeArrow(Fin(n), new Formula.TypeArrow(Fin(n), Real));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(F.Id(name));
        }
        return Seq(Operatorname, Grp([.. items]));
    }
    private static Formula QCall(string[] names, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var arg in args)
        {
            if (items.Count != 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arg);
        }
        return Seq(Qualified(names), Parenthesized(Seq([.. items])));
    }
    private static Formula MemberCall(Formula owner, params string[] names) => Seq(owner, Dot, Qualified(names));
    private static Formula For(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Instance(string name, Formula type, Formula body) => Seq(OpenBracket, Call(name, type), CloseBracket, Sp, body);
    private static Formula EqOf(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula IffOf(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Product(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, Parenthesized(body));
    private static Formula Coerce(Formula expr, Formula type) => Parenthesized(Seq(expr, Colon, Sp, type));
    private static Formula GraphBind(System.Func<Formula, Formula> body) => Disp(For("V", F.Id("Type"),
        Instance("Fintype", v, Instance("DecidableEq", v, For("G", Call("SimpleGraph", v),
            Instance("DecidableRel", MemberCall(g, "Adj"), body(v)))))));
    private static Formula Indicator() => GraphBind(_ => For("sigma", Label,
        For("x", Fin(Card(v)), For("y", Fin(Card(v)), EqOf(Call("f", g, F.Id("sigma"), F.Id("x"), F.Id("y")),
            Seq(F.Id("if"), Sp, Parenthesized(Seq(g, Dot, Call("Adj", Seq(F.Id("sigma"), Dot, Call("symm", F.Id("x"))), Seq(F.Id("sigma"), Dot, Call("symm", F.Id("y")))))), Sp,
                F.Id("then"), Sp, D(1), Sp, F.Id("else"), Sp, D(0)))))));
    private static Formula Transform()
    {
        var m = F.Id("m"); var k = F.Id("n"); var x = F.Id("x"); var y = F.Id("y");
        var labels = new Formula.Binary(Product(Call("val", m), Call("val", x)), FormulaBinaryOperator.Add, Product(Call("val", k), Call("val", y)));
        var exponent = new Formula.Fraction(Product(Product(Product(Seq(Minus, D(2)), Coerce(Qualified("Real", "pi"), Complex)), Qualified("Complex", "I")), Coerce(labels, Complex)), Coerce(n, Complex));
        var body = Product(new Formula.Fraction(D(1), Coerce(n, Complex)),
            SumOver("x", Fin(n), SumOver("y", Fin(n),
                Product(Coerce(Call("a", x, y), Complex), QCall(["Complex", "exp"], exponent)))));
        return Disp(For("N", Nat, For("a", Array, For("m", Fin(n), For("n", Fin(n),
            EqOf(Call("fhat", a, m, k), body))))));
    }
    private static Formula Ratio()
    {
        var z = Call("fhat", a, F.Id("m"), F.Id("n"));
        return Disp(For("N", Nat, For("a", Array, EqOf(Call("FR", a), new Formula.Fraction(
            SumOver("m", Fin(n), SumOver("n", Fin(n), new Formula.Norm(z))),
            QCall(["Real", "sqrt"], SumOver("m", Fin(n), SumOver("n", Fin(n), new Formula.Power(new Formula.Norm(z), D(2))))))))));
    }
    private static Formula Minimum() => GraphBind(_ => EqOf(Call("FRmin", g), Seq(
        Qualified("Finset", "univ"), Dot, Qualified("inf"), Apos, Parenthesized(Seq(
            Langle, QCall(["Fintype", "equivFin"], v), Comma, Sp, Seq(F.Id("by"), Sp, F.Id("simp")), Rangle,
            Comma, Sp, F.Id("fun"), Sp, Parenthesized(Seq(F.Id("sigma"), Colon, Sp, Label)), Sp, Mapsto, Sp,
            Call("FR", Call("f", g, F.Id("sigma"))))))));
    private static Formula Energy() => GraphBind(_ => EqOf(Call("energy", g), SumOver("j", v,
        new Formula.Absolute(Seq(Parenthesized(Seq(g, Dot, Operatorname, Grp(F.Id("isHermitian"), Underscore, Grp(F.Id("adjMatrix"))), Parenthesized(Real))), Dot, Call("eigenvalues", F.Id("j")))))));
    private static Formula Equality() => GraphBind(_ => IffOf(Call("AttainsEquality", g), And(
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("size", g)),
        EqOf(Call("FRmin", g), new Formula.Fraction(Call("energy", g), QCall(["Real", "sqrt"], Product(D(2), Coerce(Call("size", g), Real))))))));
    private static Formula Claim()
    {
        var product = QCall(["D5", "S3", "StatisticalMechanics", "Percolation", "DirectProductCyclePathBootstrap", "dirProd"], g, h);
        Formula body = Imp(Call("AttainsEquality", g), Imp(Call("AttainsEquality", h), Call("AttainsEquality", product)));
        body = Instance("DecidableRel", MemberCall(h, "Adj"), body);
        body = Instance("DecidableRel", MemberCall(g, "Adj"), body);
        body = For("H", Call("SimpleGraph", w), body);
        body = For("G", Call("SimpleGraph", v), body);
        body = Instance("DecidableEq", w, body);
        body = Instance("Fintype", w, body);
        body = Instance("DecidableEq", v, body);
        body = Instance("Fintype", v, body);
        return Disp(IffOf(F.Id("claim"), For("V", F.Id("Type"), For("W", F.Id("Type"), body))));
    }
    private static AssessedProvenance Lit() => AssessedProvenance.FromLiterature(Source);
    private static DocumentBlock Node(string selector, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("edgec-" + selector.ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
}
