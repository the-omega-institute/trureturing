using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;
internal sealed class NoEvenCycleRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over every characteristic-two field, a symmetric zero-diagonal matrix whose support graph has no even simple cycle has rank twice its maximum matching cardinality.",
        H("Rank from Maximum Matchings without Even Simple Cycles"),
        Blocks(
            Paragraph(Text("Let V be any finite vertex type and K any field of characteristic two. "
                + "A is symmetric with zero diagonal, and G.Adj(i,j) holds exactly when A(i,j) is nonzero. "
                + "The cycle hypothesis concerns simple cycles, not all closed walks. "
                + "An IsMatching subgraph has exactly one incident edge at every one of its vertices. "
                + "Edges(M) is M.coe.edgeFinset, with unordered edges counted once.")),
            Describe.Lean(DescribeId.Create("rank-maximum-matching"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank.rank_eq_twice_maximum_matching"),
                H("Rank Equals Twice the Maximum Matching Size"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem constructs a matching M, proves rank(A)=2|Edges(M)|, "
                    + "and proves |Edges(N)|<=|Edges(M)| for every matching N. Maximum means maximum "
                    + "cardinality. Two perfect matchings on any induced vertex set would give a nonempty "
                    + "symmetric difference consisting of even simple cycles. Thus each such set has at "
                    + "most one perfect matching. In the determinant sum, permutation inversion pairs "
                    + "non-involutions and cancels them in characteristic two. The remaining nonzero "
                    + "terms correspond to perfect matchings; uniqueness prevents cancellation. "
                    + "Selecting a basis of actual rows and using symmetry constructs a nonsingular "
                    + "principal restriction of size rank(A). Its perfect matching supplies M. "
                    + "Every matching N makes the restriction to its own vertices nonsingular, so "
                    + "2|Edges(N)|<=rank(A). All intermediate constructions remain inside this proof."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the stabilizer application, fix odd n>=3 and q>=2, N arbitrary, "
                + "Grep=(Z/n)^(q-1), a primitive nth root zeta in an algebraic closure of F2, and "
                + "F=F2(zeta). A character t has f_t(c)=t_c for c<q and f_t(q)=0. "
                + "Let Gamma be any symmetric zero-diagonal F2 matrix and col:[N]->[q] any coloring, "
                + "including empty parties. Put lambda_u=zeta^(f_t(col(u))), Lambda=diag(lambda), "
                + "M=Lambda Gamma+Gamma Lambda over F, and let pi_t be the nonempty fibers of f_t. "
                + "The mask B=Gamma^(pi_t) keeps Gamma_uv exactly when f_t(col(u)) differs from "
                + "f_t(col(v)). Color inequality alone does not define this mask.")),
            Paragraph(Text("The primitive-root power injection proves lambda_u=lambda_v iff the "
                + "character readouts agree. Characteristic two then gives lambda_u+lambda_v=0 iff "
                + "they agree. Direct diagonal multiplication proves M_uv=Gamma_uv(lambda_u+lambda_v). "
                + "The embedding F2->F is injective, so M and B have exactly the same nonzero support "
                + "H_t, with H_t.Adj(u,v) iff Gamma_uv is nonzero and the readouts differ. Both matrices "
                + "are symmetric and zero-diagonal. For any C subset of [N], restrict both rows and "
                + "columns to C. If the induced graph H_t[C] has no even simple cycle, apply the "
                + "content theorem over F to M[C] and independently over F2 to B[C]. Defining nu(H) "
                + "as the maximum edge cardinality among all matching subgraphs gives "
                + "rank_F M[C]=rank_F2 B[C]=2 nu(H_t[C]). The integer subtraction "
                + "delta_C(t)=(rank_F M[C]:Z)-(rank_F2 B[C]:Z) is therefore zero.")),
            Paragraph(Text("C may be empty, disconnected, contain isolated vertices, or contain odd "
                + "cycles. No perfect matching on all of C, connectivity, bipartiteness, or forest "
                + "hypothesis is used. On the empty vertex type the determinant is one and the "
                + "maximum matching and rank are zero. The graph-rank theorem itself requires only "
                + "a characteristic-two field; finiteness of F and the replica inequalities belong "
                + "to the original parameter setup. Graphs containing even simple cycles lie outside "
                + "this theorem's support hypothesis. The weighted characteristic-two statement is "
                + "a repository derivation; the classical forest adjacency-rank special case is not "
                + "claimed as novel.")))));
    private static Formula Statement()
    {
        Formula V = F.Id("V"), K = F.Id("K"), A = F.Id("A"), G = F.Id("G");
        Formula x = F.Id("x"), p = F.Id("p"), M = F.Id("M"), N = F.Id("N");
        Formula cycles = All("x", V, All("p", Call("Walk", G, x, x),
            Implies(Call("IsCycle", p), new Formula.Not(Call("Even", Call("length", p))))));
        Formula support = All("i", V, All("j", V,
            Iff(Call("Adj", G, F.Id("i"), F.Id("j")),
                Ne(Call("Entry", A, F.Id("i"), F.Id("j")), D(0)))));
        Formula diag = All("i", V, Eq(Call("Entry", A, F.Id("i"), F.Id("i")), D(0)));
        Formula result = Exists("M", Call("Subgraph", G), And(Call("IsMatching", M),
            And(Eq(Call("rank", A), Seq(D(2), Times, Call("card", Call("Edges", M)))),
                All("N", Call("Subgraph", G), Implies(Call("IsMatching", N),
                    new Formula.Relation(Call("card", Call("Edges", N)),
                        FormulaRelationOperator.LessThanOrEqual, Call("card", Call("Edges", M))))))));
        return Disp(All("V", Call("Type"), All("K", Call("Type"), Seq(
            OpenBracket, Call("Fintype", V), CloseBracket, Sp,
            OpenBracket, Call("Field", K), CloseBracket, Sp,
            OpenBracket, Call("CharP", K, D(2)), CloseBracket, Sp,
            All("A", Call("Matrix", V, V, K), Implies(Call("IsSymm", A),
                Implies(diag, All("G", Call("SimpleGraph", V),
                    Implies(support, Implies(cycles, result))))))))));
    }
    private static Formula Call(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Exists(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Iff, Seq(Open, b, Close));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
}
