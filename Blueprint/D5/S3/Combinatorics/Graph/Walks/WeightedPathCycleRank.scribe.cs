using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class WeightedPathCycleRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ranks of Weighted Paths and Cycles",
        H("Ranks of Weighted Paths and Cycles"), Blocks(
            Paragraph(Text("Let V be any finite vertex type and K any characteristic-two field. All matrices retain their actual entries; symmetry, zero diagonal and exact graph support express an alternating matrix. Equivalences carry arbitrary vertex labels. A path has every size m, including m=1 and m=2. An odd cycle has every odd m>=3. The graph evenCycleGraph(n) has two copies of Fin(n+2), with edges L(i)-R(i) and L(i)-R(sigma(i)); its two displayed edge families are the two alternating perfect matchings, each covering every vertex exactly once. WeightedCycleWalk.parityIso identifies it with the ordinary cycle on 2(n+2) vertices, hence this covers every even length at least four.")),
            Describe.Lean(DescribeId.Create("rank-path"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_path"),
                H("Every weighted path"), StatementSource.FromAuthor(RankPathFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("If the support is the path on m vertices, rank(A)=2 floor(m/2). NoEvenCycleRank.rank_eq_twice_maximum_matching is applied directly. Pairing consecutive vertices constructs a matching of floor(m/2) edges, and the vertex count bounds every matching above by this number. No restriction is imposed on the nonzero edge weights."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-odd-cycle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_odd_cycle"),
                H("Every weighted odd cycle"), StatementSource.FromAuthor(RankOddCycleFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For odd m>=3 and exact cycle support, rank(A)=m-1. Connectedness and degree two imply that every simple cycle spans all vertices and therefore has the same odd length m. The same no-even-cycle theorem applies. Consecutive pairing still constructs a maximum matching, with (m-1)/2 edges."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-even-cycle"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_even_cycle"),
                H("Every weighted even cycle"), StatementSource.FromAuthor(RankEvenCycleFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For an actual graph isomorphism from evenCycleGraph(n) to the support, take a(i)=A(L(i),R(i)) and b(i)=A(L(i),R(sigma(i))). Exact support makes these nonzero and makes all same-class entries zero. Symmetry identifies the other off-diagonal block with the transpose. Reindexing the actual matrix and applying cyclic_bipartite_rank gives rank 2n+2 when product(a)=product(b), and 2(n+2) otherwise. Thus at length L=2(n+2), the two possibilities are L-2 and L."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-even-adjacency"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank.rank_even_adjacency"),
                H("The Actual Binary Adjacency Matrix"), StatementSource.FromAuthor(RankEvenAdjacencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite vertex type and every actual graph isomorphism from evenCycleGraph(n) to G, G.adjMatrix(ZMod(2)) has rank 2n+2. Each of its entries on the two actual alternating edge families is one. This directly applies rank_even_cycle, and the stabilizer proof consumes it after proving that the actual same-component mask restriction equals this actual adjacency matrix."))),
                DescribeRole.Theorem))));

    private static Formula RankPathFormula()
    {
        Formula v = F.Id("V"), k = F.Id("K"), m = F.Id("m"), a = F.Id("A"), e = F.Id("e");
        Formula assumptions = And(IsSymm(a), And(DiagonalZero(a, v), PathSupport(m, a, e)));
        Formula conclusion = Eq(Call("rank", a), Mul(D(2), Call("NatDiv", m, D(2))));
        return Disp(All("V", F.Id("Type"), Seq(Instance("Fintype", v),
            All("K", F.Id("Type"), Seq(Instance("Field", k), InstanceAt("CharP", k, D(2)),
                All("m", Nat(), All("A", Matrix(v, k), All("e", EquivType(Fin(m), v),
                    Implies(assumptions, conclusion)))))))));
    }

    private static Formula RankOddCycleFormula()
    {
        Formula v = F.Id("V"), k = F.Id("K"), m = F.Id("m"), a = F.Id("A"), e = F.Id("e");
        Formula assumptions = And(Leq(D(3), m), And(Call("Odd", m),
            And(IsSymm(a), And(DiagonalZero(a, v), CycleSupport(m, a, e)))));
        Formula conclusion = Eq(Call("rank", a), Sub(m, D(1)));
        return Disp(All("V", F.Id("Type"), Seq(Instance("Fintype", v),
            All("K", F.Id("Type"), Seq(Instance("Field", k), InstanceAt("CharP", k, D(2)),
                All("m", Nat(), All("A", Matrix(v, k), All("e", EquivType(Fin(m), v),
                    Implies(assumptions, conclusion)))))))));
    }

    private static Formula RankEvenCycleFormula()
    {
        Formula v = F.Id("V"), k = F.Id("K"), n = F.Id("n"), a = F.Id("A"), g = F.Id("G"), e = F.Id("e");
        Formula assumptions = And(IsSymm(a), GraphSupport(g, a));
        Formula productsEqual = Eq(
            ProductOver(F.Id("i"), Fin(Add(n, D(2))), MatrixEntry(a, Apply(e, Inl(F.Id("i"))), Apply(e, Inr(F.Id("i"))))),
            ProductOver(F.Id("i"), Fin(Add(n, D(2))),
                MatrixEntry(a, Apply(e, Inl(F.Id("i"))),
                    Apply(e, Inr(Call("finRotate", Add(n, D(2)), F.Id("i")))))));
        Formula conclusion = Eq(Call("rank", a),
            Call("If", productsEqual, Add(Mul(D(2), n), D(2)), Mul(D(2), Add(n, D(2)))));
        return Disp(All("V", F.Id("Type"), Seq(Instance("Fintype", v),
            All("K", F.Id("Type"), Seq(Instance("Field", k), InstanceAt("CharP", k, D(2)),
                All("n", Nat(), All("A", Matrix(v, k), All("G", SimpleGraph(v),
                    All("e", GraphIsoType(EvenCycleGraph(n), g), Implies(assumptions, conclusion))))))))));
    }

    private static Formula RankEvenAdjacencyFormula()
    {
        Formula v = F.Id("V"), n = F.Id("n"), g = F.Id("G"), e = F.Id("e");
        Formula conclusion = Eq(Call("rank", Call("adjMatrix", g, Call("ZMod", D(2)))),
            Add(Mul(D(2), n), D(2)));
        return Disp(All("V", F.Id("Type"), Seq(Instance("Fintype", v),
            All("n", Nat(), All("G", SimpleGraph(v),
                All("e", GraphIsoType(EvenCycleGraph(n), g),
                    Implies(GraphIsoWitness(e, EvenCycleGraph(n), g), conclusion)))))));
    }

    private static Formula PathSupport(Formula m, Formula a, Formula e) =>
        ForAll2("i", Fin(m), "j", Fin(m),
            Iff(Call("Adj", Call("pathGraph", m), F.Id("i"), F.Id("j")),
                NotEqual(MatrixEntry(a, Apply(e, F.Id("i")), Apply(e, F.Id("j"))), D(0))));

    private static Formula CycleSupport(Formula m, Formula a, Formula e) =>
        ForAll2("i", Fin(m), "j", Fin(m),
            Iff(Call("Adj", Call("cycleGraph", m), F.Id("i"), F.Id("j")),
                NotEqual(MatrixEntry(a, Apply(e, F.Id("i")), Apply(e, F.Id("j"))), D(0))));

    private static Formula GraphSupport(Formula g, Formula a) =>
        ForAll2("u", F.Id("V"), "v", F.Id("V"),
            Iff(Call("Adj", g, F.Id("u"), F.Id("v")),
                NotEqual(MatrixEntry(a, F.Id("u"), F.Id("v")), D(0))));

    private static Formula DiagonalZero(Formula a, Formula v) =>
        ForAll("i", v, Eq(MatrixEntry(a, F.Id("i"), F.Id("i")), D(0)));

    private static Formula IsSymm(Formula a) => Call("IsSymm", a);
    private static Formula GraphIsoWitness(Formula e, Formula source, Formula target) =>
        Call("IsGraphIso", e, source, target);
    private static Formula GraphIsoType(Formula source, Formula target) =>
        Call("GraphIso", source, target);
    private static Formula EquivType(Formula source, Formula target) =>
        Call("Equiv", source, target);
    private static Formula EvenCycleGraph(Formula n) => Call("evenCycleGraph", n);
    private static Formula SimpleGraph(Formula v) => Call("SimpleGraph", v);
    private static Formula Matrix(Formula v, Formula k) => Call("Matrix", v, v, k);
    private static Formula MatrixEntry(Formula a, Formula i, Formula j) =>
        new Formula.Apply(new Formula.Apply(a, [i]), [j]);
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula ProductOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(variable, Sp, InMacro, Sp, type)), Sp, body);
    private static Formula Inl(Formula value) => Qualified("Sum", "inl", value);
    private static Formula Inr(Formula value) => Qualified("Sum", "inr", value);
    private static Formula Qualified(string owner, string name, params Formula[] args)
    {
        Formula head = Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula ForAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ForAll2(string n1, Formula t1, string n2, Formula t2, Formula body) =>
        ForAll(n1, t1, ForAll(n2, t2, body));
    private static Formula All(string name, Formula type, Formula body) => ForAll(name, type, body);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula InstanceAt(string name, Formula type, Formula value) =>
        Seq(OpenBracket, Call(name, type, value), CloseBracket, Sp);
    private static Formula Nat() => Call("Nat");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
}
