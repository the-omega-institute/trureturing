using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class TotalConformalRigidityTwoNotOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/TotalConformalRigidityTwoNotOne.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/assumpcaocoutinhogodsil2026totalconformal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The graph K5 with one edge removed is two-conformally rigid and is not one-conformally rigid.",
        H("Two-conformal rigidity does not imply one-conformal rigidity"),
        Blocks(
            Node("Edge", "Undirected edges counted once", EdgeFormula(),
                "The Introduction, printed page 1, states: “Let G = (V,E) be a simple, connected, undirected graph on n vertices with at least one edge, and let A := A(G) denote its adjacency matrix.” Vertices are Fin n; each undirected edge is represented by its two endpoints in strictly increasing order. The subtype retains exactly the adjacent pairs.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("uniform", "Uniform edge weights", GraphBinders(All("e", Edges(), Eqn(Call("uniform", V("G"), V("e")), D(1)))),
                "The Introduction, printed page 2, states: “For the remainder of the text, we shall use 1 to denote the all-ones vector with the appropriate dimension, which will be clear from the context.” Every edge has weight one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ValidWeight", "The closed simplex of admissible weights", GraphWeightBinders(Iff(Call("ValidWeight", V("G"), V("w")),
                And(All("e", Edges(), Leq(D(0), App(V("w"), V("e")))), Eqn(SumOver("e", Edges(), App(V("w"), V("e"))),
                    Parenthesized(Seq(QCall("Fintype", "card", Edges()), Sp, Colon, Sp, Real())))))),
                "The Introduction, printed page 2, states: “The simplex of valid edge weights is thus defined as Δ_E := {w ∈ ℝ^E: w ≥ 0, 1^T w = |E|}.” Zero edge weights are included. The natural edge cardinality is coerced to Real.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("eigenvalue", "Increasing eigenvalues of the real Laplacian", EigenvalueFormula(),
                "The Introduction, printed page 1, states: “For an edge ab ∈ E, we define z_ab := e_a − e_b, where e_a ∈ ℝ^V denotes the a-th canonical basis vector, and we also let L_ab := z_ab z_ab^T.” Equation (1) is ℒ(w) := ∑_{ab∈E} w_ab L_ab = ∑_{ab∈E} w_ab z_ab z_ab^T. Both endpoint differences are expanded in the matrix entries. The Introduction, printed page 2, states: “We shall order the eigenvalues of ℒ(w) as 0 = λ₁(w) ≤ λ₂(w) ≤ … ≤ λₙ(w).” The formula reverses the nonincreasing eigenvalues₀ order and uses zero-based indices. The proof h states that the real matrix is Hermitian; e identifies the two finite index sizes. Proof irrelevance makes their choices immaterial. Nonnegative normalized weights are required when using the source's positivity and zero-eigenvalue assertions.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("smallestSum", "The smallest nontrivial eigenvalue sum", SumFormula(false),
                "Definition 1.2, printed pages 2–3, states: “Let S_k(w) and s_k(w) denote the sum of the k largest and k smallest nontrivial eigenvalues of ℒ(w), respectively, for some k ∈ [n−1].” The Introduction specifies: “By the nontrivial eigenvalues of ℒ(w), we shall mean λ₂(w),…,λₙ(w).” Thus indices 1 through k are included, retaining any additional zero eigenvalues.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("largestSum", "The largest eigenvalue sum", SumFormula(true),
                "Definition 1.2, printed pages 2–3, states: “Let S_k(w) and s_k(w) denote the sum of the k largest and k smallest nontrivial eigenvalues of ℒ(w), respectively, for some k ∈ [n−1].” The cutoff n ≤ val i + k avoids natural-number subtraction. The rigidity predicate restricts k to 1 ≤ k < n.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("KConformallyRigid", "Both extremal sums at the same uniform weights", GraphBinders(All("k", Nat(),
                Iff(Call("KConformallyRigid", V("G"), V("k")), RigidityBody()))),
                "Definition 1.2, printed pages 2–3, states: “We say that G is k-conformally rigid if, for any w,w′ ∈ Δ_E,” followed by s_k(w) ≤ s_k(1) and S_k(1) ≤ S_k(w′). The independent second weighting is called u here. The range 1 ≤ k < n and both simplex premises are explicit.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The Section 9 existence question", Iff(Call("claim"), ClaimBody()),
                "Section 9, printed page 20, asks: “Are there graphs that are 2-conformally rigid but not 1-conformally rigid?” The formula asks for a finite simple connected graph with an actual edge, satisfying precisely those two properties. The graph and its order are existential conclusions.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "An affirmative answer on five vertices", ClaimBody(),
                "Take K5 with the edge {0,1} removed. It has nine edges and a universal vertex. Its uniform increasing spectrum is [0,3,5,5,5]. A real symmetric matrix with decreasing spectrum [8/9,5/9,5/9,0,0] has edge quadratic value 10/9 on every edge. Consequently its trace pairing with every normalized weighted Laplacian is 10. The von Neumann trace inequality and eigenvalue monotonicity bound this pairing by the two largest eigenvalues. The Laplacian has trace 18 and is positive semidefinite, giving smallestSum ≤ 8 and 10 ≤ largestSum throughout the closed simplex; uniform weights attain both. Assigning 6/5 to the six edges meeting {0,1} and 3/5 to the other three gives increasing spectrum [0,18/5,21/5,21/5,6]. Its second eigenvalue exceeds the uniform value 3, so one-conformal rigidity fails. The trace-pairing estimate itself applies to every real Hermitian five by five matrix, without assuming that tested matrix is positive semidefinite.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("op-acg2605cr"), ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("acg-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Op(name) : App(Op(name), args);
    private static Formula Qualified(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Vertices() => Call("Fin", V("n"));
    private static Formula Edges() => Call("Edge", V("G"));
    private static Formula Weights() => Seq(Edges(), Sp, To, Sp, Real());
    private static Formula GraphBinders(Formula body) => All("n", Nat(), All("G", Call("SimpleGraph", Vertices()), body));
    private static Formula GraphWeightBinders(Formula body) => GraphBinders(All("w", Weights(), body));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum,
        Seq(V(name), Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula EdgeFormula() => GraphBinders(Eqn(Edges(), Seq(OpenBrace, V("e"), Sp, Colon, Sp,
        Vertices(), Sp, Times, Sp, Vertices(), Sp, Mid, Sp,
        And(Lt(Seq(V("e"), Dot, D(1)), Seq(V("e"), Dot, D(2))),
            QCall("SimpleGraph", "Adj", V("G"), Seq(V("e"), Dot, D(1)), Seq(V("e"), Dot, D(2)))), CloseBrace)));
    private static Formula EndpointDifference(string vertex) => Parenthesized(new Formula.Binary(
        Call("ite", Eqn(V(vertex), Seq(Parenthesized(Call("val", V("e"))), Dot, D(1))), D(1), D(0)),
        FormulaBinaryOperator.Subtract,
        Call("ite", Eqn(V(vertex), Seq(Parenthesized(Call("val", V("e"))), Dot, D(2))), D(1), D(0))));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula EigenvalueFormula()
    {
        Formula matrix = QCall("Matrix", "of", Parenthesized(Seq(LambdaLower, Sp,
            Parenthesized(Seq(V("row"), Sp, Colon, Sp, Vertices())), Sp,
            Parenthesized(Seq(V("col"), Sp, Colon, Sp, Vertices())), Sp, Mapsto, Sp,
            SumOver("e", Edges(), Mul(Mul(App(V("w"), V("e")), EndpointDifference("row")), EndpointDifference("col"))))));
        Formula htype = QCall("Matrix", "IsHermitian", matrix);
        Formula esize = Eqn(V("n"), QCall("Fintype", "card", Vertices()));
        Formula index = QCall("Fin", "cast", V("e"), Seq(V("i"), Dot, Op("rev")));
        Formula values = Seq(V("h"), Dot, new Formula.Subscript(Op("eigenvalues"), D(0)));
        return GraphWeightBinders(All("i", Vertices(), All("h", htype, All("e", Parenthesized(esize),
            Eqn(Call("eigenvalue", V("G"), V("w"), V("i")), App(values, index))))));
    }
    private static Formula SumFormula(bool largest) => GraphWeightBinders(All("k", Nat(),
        Eqn(Call(largest ? "largestSum" : "smallestSum", V("G"), V("w"), V("k")), SumOver("i", Vertices(),
            Call("ite", largest ? Leq(V("n"), Add(Call("val", V("i")), V("k"))) :
                And(Lt(D(0), Call("val", V("i"))), Leq(Call("val", V("i")), V("k"))),
                Call("eigenvalue", V("G"), V("w"), V("i")), D(0))))));
    private static Formula RigidityBody() => And(Leq(D(1), V("k")), And(Lt(V("k"), V("n")),
        All("w", Weights(), All("u", Weights(), Imp(Call("ValidWeight", V("G"), V("w")),
            Imp(Call("ValidWeight", V("G"), V("u")), And(
                Leq(Call("smallestSum", V("G"), V("w"), V("k")), Call("smallestSum", V("G"), Call("uniform", V("G")), V("k"))),
                Leq(Call("largestSum", V("G"), Call("uniform", V("G")), V("k")), Call("largestSum", V("G"), V("u"), V("k"))))))))));
    private static Formula ClaimBody() => Ex("n", Nat(), Ex("G", Call("SimpleGraph", Vertices()),
        And(QCall("SimpleGraph", "Connected", V("G")), And(
            Ex("a", Vertices(), Ex("b", Vertices(), QCall("SimpleGraph", "Adj", V("G"), V("a"), V("b")))),
            And(Call("KConformallyRigid", V("G"), D(2)), new Formula.Not(Parenthesized(Call("KConformallyRigid", V("G"), D(1)))))))));
}
