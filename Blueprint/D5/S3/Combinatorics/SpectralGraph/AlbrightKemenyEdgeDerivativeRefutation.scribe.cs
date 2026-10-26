using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class AlbrightKemenyEdgeDerivativeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/albright2023kemenyedgederivative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected barbell on 23 vertices has a smaller Kemeny edge derivative than the path.",
        H("The path-ends derivative does not minimize Kemeny's edge derivative"),
        Blocks(
            Paragraph(Text("The edge weight varies by a real parameter t, and weighted degrees vary with it. Kemeny's constant is the sum of reciprocals of the nonzero eigenvalues of the normalized Laplacian, counted with multiplicity.")),
            Node("adj", "One-edge perturbation", "paramAdj", ParamAdjFormula(),
                "Section 2, page 3, states: “Aksoy et al. in [2] represented M(t) = A + tB where A is the adjacency matrix of a graph G and B is a symmetric matrix representing a collection of edges.” It continues: “We will not restrict B and instead have B be a symmetric matrix representing any collection of edges denoted EC.” Section 1, page 3, states: “Here, we assume all unweighted edges have weight 1 and all non-edges have weight 0.” For vertices a and b, B is the sum of the two matrix units at (a,b) and (b,a); the vertex set is Fin n.", AssessedProvenance.FromLiterature(Source)),
            Node("lap", "Normalized Laplacian", "normLap", NormLapFormula(),
                "Section 1, page 3, states: “The normalized Laplacian matrix of a graph is given by L = I − D^{−1/2} A D^{−1/2} where A is the adjacency matrix and D is the degree diagonal matrix.” The displayed entries use the row sums of A for those degrees, including for the perturbed adjacency matrix.", AssessedProvenance.FromLiterature(Source)),
            Node("kemeny", "Kemeny's constant", "kemeny", KemenyFormula(),
                "Section 1, page 3, states: “Kemeny’s constant can be computed as” K(G) = Σ_{λT ≠ 1} 1/(1 − λT) = Σ_{λL ≠ 0} 1/λL, “where each λL is an eigenvalue of L.” The encoding filters the multiset of real characteristic roots by nonzeroness, maps inversion, and sums. For the real symmetric normalized Laplacians in the proof, these roots are the eigenvalues with multiplicity.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 3.5: minimality", "claim", Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Conjecture 3.5, page 19, states verbatim: “For a given n, the derivative of Kemeny’s constant on simple graphs of order n is smallest on the path on n vertices with respect to the non-edge connecting the ends of the path. The value of this derivative is O(n³).” The proposition expresses the first sentence for connected graphs on Fin n with n ≥ 2 and a ≠ b. Both derivatives must exist at zero. The path endpoints are the elements of Fin n with values 0 and n − 1; the inequality n ≥ 2 supplies their bounds. The second sentence concerns growth of the path value and is outside this proposition.", AssessedProvenance.FromLiterature(Source)),
            Node("result", "A strict counterexample at order 23", "result", new Formula.Not(Parenthesized(ClaimBody())),
                "Take cliques on {0,…,7} and {8,…,15}, joined by the path 0,16,17,18,19,20,21,22,8. This is a connected simple graph on Fin 23. The missing chord {0,8} has Kemeny derivative −7683669/4096 at zero, while the missing chord {0,22} of pathGraph 23 has derivative −77763/44. The difference is −4891047/45056 < 0. Grounded Green matrices give exact inverse certificates; spectral diagonalization identifies their weighted trace with the sum over nonzero characteristic roots. A rational rank-one update holds on a neighborhood of zero and yields both derivatives. Thus the universal minimality statement fails. No infinite family or asymptotic minimum is asserted.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("albright-et-al-2023-kemeny-edge-derivative-conjecture-3-5"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ak-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula FinN() => Call("Fin", V("n"));
    private static Formula MatrixN() => Call("Matrix", FinN(), FinN(), Real());
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(Call("fun"), Sp, V(name), Sp, Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, Colon, Sp, FinN())), Sp, body);
    private static Formula GraphBinders(Formula body) =>
        All("G", Call("SimpleGraph", FinN()),
            Seq(OpenBracket, Call("DecidableRel", QCall("SimpleGraph", "Adj", V("G"))),
                CloseBracket, Sp, body));

    private static Formula ParamAdjFormula()
    {
        Formula edge = Parenthesized(Seq(QCall("Matrix", "single", V("a"), V("b"), D(1)), Sp, Plus, Sp,
            QCall("Matrix", "single", V("b"), V("a"), D(1))));
        Formula rhs = Seq(QCall("SimpleGraph", "adjMatrix", V("G"), Real()), Sp, Plus, Sp,
            V("t"), Sp, Cdot, Sp, edge);
        return All("n", Nat(), GraphBinders(All("a", FinN(), All("b", FinN(), All("t", Real(),
            Eqn(Call("paramAdj", V("G"), V("a"), V("b"), V("t")), rhs))))));
    }

    private static Formula NormLapFormula()
    {
        Formula denominator = Seq(QCall("Real", "sqrt", SumOver("k", App(V("A"), V("i"), V("k")))),
            Sp, Cdot, Sp, QCall("Real", "sqrt", SumOver("k", App(V("A"), V("j"), V("k")))));
        Formula entries = Lam("i", FinN(), Lam("j", FinN(),
            new Formula.Fraction(App(V("A"), V("i"), V("j")), denominator)));
        return All("n", Nat(), All("A", MatrixN(), Eqn(Call("normLap", V("A")),
            Seq(D(1), Sp, Minus, Sp, QCall("Matrix", "of", entries)))));
    }

    private static Formula KemenyFormula()
    {
        Formula roots = QCall("Polynomial", "roots", QCall("Matrix", "charpoly", Call("normLap", V("A"))));
        Formula filtered = QCall("Multiset", "filter", Lam("x", Real(), Ne(V("x"), D(0))), roots);
        Formula mapped = QCall("Multiset", "map", Lam("x", Real(), new Formula.Power(V("x"), new Formula.Negate(D(1)))), filtered);
        return All("n", Nat(), All("A", MatrixN(), Eqn(Call("kemeny", V("A")), QCall("Multiset", "sum", mapped))));
    }

    private static Formula ClaimBody()
    {
        Formula path = QCall("SimpleGraph", "pathGraph", V("n"));
        Formula last = Seq(Langle, Sp, Seq(V("n"), Sp, Minus, Sp, D(1)), Rangle);
        Formula graphFunction = Lam("t", Real(), Call("kemeny", Call("paramAdj", V("G"), V("a"), V("b"), V("t"))));
        Formula pathFunction = Lam("t", Real(), Call("kemeny", Call("paramAdj", path, Seq(Langle, D(0), Rangle), last, V("t"))));
        Formula comparison = Imp(QCall("SimpleGraph", "Connected", V("G")), Imp(Ne(V("a"), V("b")),
            Imp(Call("HasDerivAt", graphFunction, V("dG"), D(0)),
                Imp(Call("HasDerivAt", pathFunction, V("dP"), D(0)), Leq(V("dP"), V("dG"))))));
        return All("n", Nat(), Imp(Leq(D(2), V("n")), GraphBinders(All("a", FinN(), All("b", FinN(),
            All("dG", Real(), All("dP", Real(), comparison)))))));
    }
}
