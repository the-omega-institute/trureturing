using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class BonettoSignatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/BonettoSignature.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/bonetto2024mixed");

    public DocumentDefinition Create()
    {
        Formula f = V("F"), g = V("G"), h = V("H"), u = V("u"), q = V("Q");
        Formula partition = Graphs(Eqn(Call("IsEdgePartition", f, g, h),
            Parenthesized(And(Call("Disjoint", g, h),
                Eqn(Seq(g, Sp, Cup, Sp, h), f)))));
        Formula matrix = GraphPair(All("u", C("Real"),
            Eqn(Call("mixedMatrix", g, h, u),
                Add(App(Qualified("SimpleGraph", "lapMatrix"), g, C("Real")),
                    Mul(u, App(Qualified("SimpleGraph", "adjMatrix"), h, C("Real")))))));
        Formula roots = App(Qualified("Polynomial", "roots"),
            App(Qualified("Matrix", "charpoly"), q));
        Formula positive = Seq(LambdaLower, Sp, V("x"), Mapsto, Lt(D(0), V("x")));
        Formula negative = Seq(LambdaLower, Sp, V("x"), Mapsto, Lt(V("x"), D(0)));
        Formula signature = Carrier(All("Q", Call("Matrix", V("V"), V("V"), C("Real")),
            Eqn(Call("signature", q), Sub(
                IntegerCast(Call("card", Call("filter", Parenthesized(positive), roots))),
                IntegerCast(Call("card", Call("filter", Parenthesized(negative), roots)))))));
        Formula conclusion = Graphs(Imp(Call("IsEdgePartition", f, g, h),
            All("s", C("Real"), All("t", C("Real"),
                Imp(And(Lt(D(0), V("s")), Le(V("s"), V("t"))),
                    Le(Call("signature", Call("mixedMatrix", g, h, V("t"))),
                        Call("signature", Call("mixedMatrix", g, h, V("s")))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The spectral signature of a graph Laplacian plus a positive adjacency weight is nonincreasing.",
            H("Mixed graph matrices and spectral signature"), Blocks(
                Node("partition", "Disjoint spanning edge partition", "IsEdgePartition", partition,
                    "F, G and H are simple undirected loopless graphs on the same finite vertex type V. Disjoint G H means their edge sets are disjoint; G ∪ H = F means their union is exactly the original graph. The common vertex type makes the two subgraphs spanning. This is Definition 3, with no connectivity or nonempty-edge requirement.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("matrix", "The actual real graph matrix", "mixedMatrix", matrix,
                    "Definitions 1–3 give the ordinary symmetric 0/1 adjacency matrix A_H and combinatorial Laplacian L_G = D_G − A_G, whose diagonal entries are the vertex degrees. mixedMatrix G H u is exactly L_G + u A_H over the reals. The expression is defined for every real u; the conclusion uses only strictly positive parameters. Mathlib's SimpleGraph matrices provide this realization directly.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("signature", "Signature with algebraic multiplicity", "signature", signature,
                    "Definitions 7 and 8 count positive and negative eigenvalues with multiplicity and subtract the latter count from the former in the integers. Here roots is the multiset of real roots of the actual characteristic polynomial, filter preserves multiplicity, and card is its multiset cardinality. Zero roots pass neither strict sign filter. For each Hermitian real Q, Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies this entire multiset with the indexed spectral eigenvalues. Thus the definition equals RHLinalg.posIndex minus RHLinalg.negIndex; no spectral realization is assumed. Only real symmetric matrices are used in the conclusion.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("result", "Signature monotonicity on the positive axis", "result", conclusion,
                    "This is the nonincreasing assertion of Section 3, Conjecture 1. Every finite vertex type, including the empty type, every disjoint spanning edge partition and all 0 < s ≤ t are quantified. Singular matrices, persistent kernels, disconnected graphs, empty edge classes and s = t remain included. The partition fixes the original graph interpretation; the argument itself needs only L_G ≥ 0 and symmetry. Write M(u) = L_G + u A_H. The identities M(s) = (s/t)M(t) + (1−s/t)L_G and −M(t) = (t/s)(−M(s)) + (t/s−1)L_G have strictly positive first coefficients and nonnegative second coefficients. Consequently every subspace positive for M(t) is positive for M(s), and every subspace positive for −M(s) is positive for −M(t). RHLinalg.posIndex_eq_max_finrank_posDefOn and finrank_le_posIndex_of_posDefOn turn these transfers into Nplus(M(t)) ≤ Nplus(M(s)) and Nminus(M(s)) ≤ Nminus(M(t)); the existing posIndex_neg_eq_negIndex supplies the sign reversal. Subtracting the integer counts proves the displayed inequality. This assembly uses established spectral and inertia ingredients. No eigenvalue continuity, inverse matrix, generic crossing or kernel removal is required. It asserts no transition-count bound or limiting-signature formula. Bounded literature checks do not establish global novelty or priority.",
                    DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
    }

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("bonetto-signature-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Carrier(Formula body) => All("V", C("Type"), Seq(
        OpenBracket, Call("Fintype", V("V")), CloseBracket, Sp,
        OpenBracket, Call("DecidableEq", V("V")), CloseBracket, Sp, body));
    private static Formula GraphPair(Formula body) => Carrier(
        All("G", Call("SimpleGraph", V("V")), All("H", Call("SimpleGraph", V("V")), body)));
    private static Formula Graphs(Formula body) => Carrier(
        All("F", Call("SimpleGraph", V("V")), All("G", Call("SimpleGraph", V("V")),
            All("H", Call("SimpleGraph", V("V")), body))));
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(C(owner), Dot, C(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? C(name) : App(C(name), args);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula IntegerCast(Formula value) => Parenthesized(Seq(value, Colon, Sp, C("Int")));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
