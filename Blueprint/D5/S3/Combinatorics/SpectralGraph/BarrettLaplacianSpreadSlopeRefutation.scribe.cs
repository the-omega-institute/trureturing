using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class BarrettLaplacianSpreadSlopeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/barrettcameronevanshallkempton2022laplacianspread");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent clusters refute every universal slope-one Laplacian-spread bound.",
        H("No universal slope-one bound for digraph Laplacian spread"),
        Blocks(
            Paragraph(Text("An imbalanced five-vertex digraph has two zero-sum unit vectors with quadratic values 3408/679 and zero. Replacing each vertex by an independent cluster of size m produces an unweighted loopless digraph of order 5m whose spread is at least 3408m/679. The excess 13m/679 is unbounded.")),
            Node("laplacian", "The out-degree Laplacian", LaplacianFormula(),
                "Section 2, page 2, states verbatim: “Moreover, we define the Laplacian matrix of Γ by L = D − A, where A is the adjacency matrix of Γ and D is a diagonal matrix whose ith diagonal entry is d⁺(i).” The same page states: “After indexing the vertex set as V = {1, 2, . . . , n}, we define the adjacency matrix of Γ by A = [aᵢⱼ]ⁿᵢ,ⱼ₌₁, where aᵢⱼ = 1 if (i, j) ∈ E and aᵢⱼ = 0 otherwise.” It also states: “We denote the out-degree of vertex i ∈ V by d⁺(i), which is equal to the number of edges of the form (i, j) ∈ E.” Fin n labels the vertices from zero; each arc contributes one to its source's row sum."),
            Node("quadraticValues", "Restricted real quadratic values", QuadraticFormula(),
                "Section 2, page 2, defines the extrema by xᵀLx subject to x ⟂ e and ‖x‖ = 1, where e is the all ones vector. The formula gives precisely these values in the real Euclidean space. Coordinate sum zero expresses orthogonality to e; the norm is the Euclidean norm."),
            Node("alpha", "The lower extremum", GraphBinders(Eqn(Call("alpha", V("G")), Call("sInf", Call("quadraticValues", V("G"))))),
                "Section 2, page 2, states verbatim: “The algebraic connectivity of Γ is given by” α(Γ) = min{xᵀLx : x ⟂ e, ‖x‖ = 1}. The formula uses the infimum of that quadratic-value set; for order at least two the set is nonempty and compact, so the infimum is attained."),
            Node("beta", "The upper extremum", GraphBinders(Eqn(Call("beta", V("G")), Call("sSup", Call("quadraticValues", V("G"))))),
                "Section 2, page 2, states verbatim: “Another related and useful quantity is” β(Γ) = max{xᵀLx : x ⟂ e, ‖x‖ = 1}. The formula uses the supremum of the same set, attained for order at least two."),
            Node("spread", "Laplacian spread", GraphBinders(Eqn(Call("spread", V("G")), Seq(Call("beta", V("G")), Sp, Minus, Sp, Call("alpha", V("G"))))),
                "Section 3, page 5, states verbatim: “We define the Laplacian spread of a digraph Γ by” sp(Γ) = β(Γ) − α(Γ), “that is, sp(Γ) is equal to the length of the real part of Wᵣ(L).”"),
            Node("claim", "The slope-one conjecture", Eqn(Call("claim"), ClaimBody()),
                "Conjecture 20 in the HTML rendering, numbered Conjecture 6.7 on page 16 of the arXiv v1 PDF, states verbatim: “The bound on the Laplacian spread of digraphs given in (3.2) can be reduced to a linear function in n with a slope of 1.” Section 6, page 14, states: “Note that all conjectures are made for unweighted digraphs.” Equation (3.2) on page 6 is sp(Γ) ≤ 5(n−1)/2. One real intercept must work for all n ≥ 2 and all loopless directed graphs; opposite arcs are allowed. The graph relation has no balance or polygonality assumption."),
            Node("result", "Refutation for every real intercept", new Formula.Not(Parenthesized(ClaimBody())),
                "The Figure 3 graph has adjacency rows 00100, 10111, 11011, 00000 and 00000. The vectors (2,26,−26,−1,−1) and (0,0,0,1,−1) have coordinate sum zero, squared norms 1358 and 2, and Laplacian quadratic values 6816 and zero before normalization. Independent clusters multiply squared norms by m and quadratic values by m². Compact-sphere bounds compare the two normalized values with the supremum and infimum. Choosing a positive integer m > max(0,679C/13) gives spread > 5m + C. No calculation of every eigenvalue is required.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("bce20-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Nat() => Call("Nat");
    private static Formula Real() => Call("Real");
    private static Formula FinN() => Call("Fin", V("n"));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(V(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsF(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula GraphBinders(Formula body) => All("n", Nat(), All("G", Call("Digraph", FinN()), body));
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, Colon, Sp, FinN())), Sp, body);
    private static Formula Fun(string name, Formula body) =>
        Seq(Call("fun"), Sp, Parenthesized(Seq(V(name), Sp, Colon, Sp, FinN())), Sp, Mapsto, Sp, body);
    private static Formula Adj() => App(Qualified("Digraph", "Adj"), V("G"), V("i"), V("j"));
    private static Formula Entry() => Call("ite", Adj(), D(1), D(0));
    private static Formula LaplacianFormula() => GraphBinders(Eqn(Call("laplacian", V("G")),
        Seq(App(Qualified("Matrix", "diagonal"), Parenthesized(Fun("i", SumOver("j", Entry())))),
            Sp, Minus, Sp, App(Qualified("Matrix", "of"), Parenthesized(Fun("i", Fun("j", Entry())))))));
    private static Formula QuadraticFormula()
    {
        Formula vector = Parenthesized(Fun("i", App(V("x"), V("i"))));
        Formula value = Call("dotProduct", vector, App(Qualified("Matrix", "mulVec"), Call("laplacian", V("G")), vector));
        Formula constraints = And(Eqn(SumOver("i", App(V("x"), V("i"))), D(0)),
            And(Eqn(Seq(Vert, Sp, V("x"), Vert), D(1)), Eqn(V("t"), value)));
        Formula set = Seq(OpenBrace, V("t"), Sp, Colon, Sp, Real(), Sp, Mid, Sp,
            ExistsF("x", Call("EuclideanSpace", Real(), FinN()), constraints), CloseBrace);
        return GraphBinders(Eqn(Call("quadraticValues", V("G")), set));
    }
    private static Formula ClaimBody() => ExistsF("C", Real(), All("n", Nat(),
        Imp(Leq(D(2), V("n")), All("G", Call("Digraph", FinN()),
            Imp(All("i", FinN(), new Formula.Not(App(Qualified("Digraph", "Adj"), V("G"), V("i"), V("i")))),
                Leq(Call("spread", V("G")), Seq(Parenthesized(Seq(V("n"), Sp, Colon, Sp, Real())), Sp, Plus, Sp, V("C"))))))));
}
