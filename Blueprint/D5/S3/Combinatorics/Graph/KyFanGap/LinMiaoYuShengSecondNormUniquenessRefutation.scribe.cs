using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class LinMiaoYuShengSecondNormUniquenessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/lin2022kyfanli");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two nonisomorphic connected graphs on six vertices and seven edges have the same second Ky Fan norm of their LI-matrices.",
        H("Second-norm equality does not determine the graph"),
        Blocks(
            Node("li", "Centered Laplacian", "LI", LIFormula(),
                "The introduction, journal page 681, states: “Let G be a graph with n vertices and m edges. Then the LI-matrix of G is defined as LI(G)=L(G)−(2m/n)Iₙ.” Here SimpleGraph.lapMatrix is the degree diagonal matrix minus the adjacency matrix, and Nat.card G.edgeSet counts unordered edges. The quotient is in ℝ. Classical.decRel supplies the adjacency decision procedure.",
                AssessedProvenance.FromLiterature(Source)),
            Node("graph", "The graph with triangles on a common edge", "Gmn", GmnFormula(),
                "Section 2 of arXiv v2 (journal page 682) states: “The Gₘ,ₙ, shown in Fig. 2.1, is a graph with n vertices and m edges which has m−n+1 triangles with a common edge and 2n−m+3 pendent edges incident with one end vertex of the common edge.” The printed pendant count conflicts with the stated order and size. On the conjecture's range n ≤ m and m+3 ≤ 2n, the graph drawn there has 2n−m−3 pendant vertices: vertex 0 is universal, and vertex 1 meets vertices 2 through m−n+2. Gmn takes n first and m second. SimpleGraph.fromRel removes loops and symmetrizes the displayed relation; Nat.sub is truncated subtraction.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 5.11 with separate maxima", "claim",
                Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Conjecture 5.11, journal page 694, states: “Among all connected graphs with n and m edges n ≤ m ≤ 2n−3, the Gₘ,ₙ is the unique graph with maximal value of ‖LI(G)‖F₂ and ‖LI(G)‖F₃.” The phrase “with n and m edges” means n vertices and m edges. The proposition asserts the maximum and equality characterization separately for k=2 and k=3, on Fin n. The upper range is m+3 ≤ 2n. The existing kyFan sums singular values in decreasing order with multiplicity and zero extension. Graph isomorphism is expressed by Nonempty (G ≃g Gmn n m). A simultaneous-maximizer interpretation is outside this proposition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "A second-norm tie without isomorphism", "result",
                new Formula.Not(Parenthesized(ClaimBody())),
                "On Fin 6, take all edges {0,i} for 1 ≤ i ≤ 5 and the additional edges {1,2}, {3,4}. This graph is connected and has seven edges. Its degrees are 5,2,2,2,2,1, whereas Gmn 6 7 has degrees 5,3,2,2,1,1, so the graphs are nonisomorphic. Their Laplacian spectra are respectively {6,3,3,1,1,0} and {6,4,2,1,1,0}. Exact rational change-of-basis matrices identify the singular values of the centered Laplacians; the largest two are 11/3 and 7/3 in both cases. Both second Ky Fan norms therefore equal 6, contradicting the equality characterization. This also contradicts the uniqueness assertion of the source's Theorem 5.9 at order six. The third norm, the global upper bound and an equality classification for general orders are not asserted here.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("lmys511-kyfan"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("lmys-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula FinN() => Call("Fin", V("n"));
    private static Formula GraphN() => Call("SimpleGraph", FinN());
    private static Formula CastReal(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Real()));
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Mul(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Call("fun"), Sp, V(name), Sp, Colon, Sp, type, Sp, Mapsto, Sp, body);

    private static Formula LIFormula()
    {
        Formula adjacency = QCall("SimpleGraph", "Adj", V("G"));
        Formula scalar = new Formula.Fraction(
            Mul(D(2), CastReal(QCall("Nat", "card", QCall("SimpleGraph", "edgeSet", V("G"))))),
            CastReal(V("n")));
        Formula matrix = Call("Matrix", FinN(), FinN(), Real());
        Formula rhs = Seq(Call("letI"), Sp, Colon, Sp, Call("DecidableRel", adjacency),
            Sp, Colon, Eq, Sp, QCall("Classical", "decRel", adjacency), Semi, Sp,
            QCall("SimpleGraph", "lapMatrix", Real(), V("G")), Sp, Minus, Sp,
            Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, matrix)));
        return All("n", Nat(), All("G", GraphN(), Eqn(Call("LI", V("G")), rhs)));
    }

    private static Formula GmnFormula()
    {
        Formula u = Call("val", V("u"));
        Formula v = Call("val", V("v"));
        Formula relation = Or(Eqn(u, D(0)),
            And(Eqn(u, D(1)), And(Leq(D(2), v), Less(v, Add(QCall("Nat", "sub", V("m"), V("n")), D(3))))));
        Formula rhs = QCall("SimpleGraph", "fromRel", Lam("u", FinN(), Lam("v", FinN(), relation)));
        return All("n", Nat(), All("m", Nat(), Eqn(Call("Gmn", V("n"), V("m")), rhs)));
    }

    private static Formula ClaimBody()
    {
        Formula source = Call("Gmn", V("n"), V("m"));
        Formula left = Call("kyFan", V("k"), Call("LI", V("G")));
        Formula right = Call("kyFan", V("k"), Call("LI", source));
        Formula iso = Call("Nonempty", QCall("SimpleGraph", "Iso", V("G"), source));
        Formula equality = Logic(Eqn(left, right), FormulaLogicOperator.Iff, iso);
        return All("n", Nat(), All("m", Nat(), Imp(Leq(V("n"), V("m")),
            Imp(Leq(Add(V("m"), D(3)), Mul(D(2), V("n"))), All("G", GraphN(),
                Imp(QCall("SimpleGraph", "Connected", V("G")),
                    Imp(Eqn(QCall("Nat", "card", QCall("SimpleGraph", "edgeSet", V("G"))), V("m")),
                        All("k", Nat(), Imp(Or(Eqn(V("k"), D(2)), Eqn(V("k"), D(3))),
                            And(Leq(left, right), equality))))))))));
    }
}
