using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class BarrettLaplacianSpreadSlopeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/barrett2022laplacianspread");

    public DocumentDefinition Create()
    {
        Formula g = V("G"), i = V("i"), j = V("j");
        return DocumentDefinition.Create(ScribeNode.Create(
            "The Laplacian spread of loopless unweighted digraphs admits no universal bound n + C.",
            H("No universal slope-one Laplacian-spread bound"), Blocks(
                Node("outDegree", "Out-degree", Graph(All("i", FinN(), Eqn(Call("outDegree", g, i),
                    SumOver("j", App(AdjacencyMatrix(g), i, j))))),
                    "Section 2, page 2: \"We denote the out-degree of vertex i∈V by d⁺(i), which is equal to the number of edges of the form (i,j)∈E.\" The sum counts the real 0/1 entries in the selected row. FiniteGraphEntropy.adjacency supplies the natural entries and Nat.cast embeds them into the reals.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("inDegree", "In-degree", Graph(All("i", FinN(), Eqn(Call("inDegree", g, i),
                    SumOver("j", App(AdjacencyMatrix(g), j, i))))),
                    "Section 2, page 2: \"Similarly, we denote the in-degree of vertex i∈V by d⁻(i), which is equal to the number of edges of the form (j,i)∈E.\" The sum counts the incoming arcs in the selected column.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("laplacian", "Directed Laplacian matrix", Graph(Eqn(Call("laplacian", g),
                    Sub(App(Q("Matrix", "diagonal"), Call("outDegree", g)), AdjacencyMatrix(g)))),
                    "Section 2, page 2: \"Moreover, we define the Laplacian matrix of Γ by L=D−A, where A is the adjacency matrix of Γ and D is a diagonal matrix whose ith diagonal entry is d⁺(i).\" Both matrices have real entries indexed by Fin n.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("Balanced", "Balance at every vertex", Graph(Iffn(Call("Balanced", g), All("i", FinN(),
                    Eqn(Call("outDegree", g, i), Call("inDegree", g, i))))),
                    "Section 4, page 9: \"Now, let Γ=(V,E) be a balanced digraph, that is, d⁺(i)=d⁻(i) for all i∈V.\" Balance equates the outgoing and incoming degree at each vertex separately.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("quadraticValues", "Zero-sum unit quadratic values", Graph(Eqn(Call("quadraticValues", g),
                    Seq(OpenBrace, V("t"), Sp, Colon, Sp, Reals(), Sp, Bar, Sp,
                        Ex("x", Call("EuclideanSpace", Reals(), FinN()), Andn(
                            Eqn(SumOver("i", App(V("x"), i)), D(0)), Andn(
                            Eqn(Norm(V("x")), D(1)), Eqn(V("t"), Quadratic(g, Vector(V("x"))))))), CloseBrace))),
                    "Section 2, page 2: \"The algebraic connectivity of Γ is given by α(Γ) = min_{x⊥e, ‖x‖=1} xᵀLx.\" \"Another related and useful quantity is β(Γ) = max_{x⊥e, ‖x‖=1} xᵀLx.\" This set is exactly those real quadratic values: the sum of the Euclidean coordinates is zero, the Euclidean norm is one, and the value is dotProduct x (Matrix.mulVec L x). It is nonempty for n≥2 and compact; the extrema are attained.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("alpha", "Minimum quadratic value", Graph(Eqn(Call("alpha", g), Call("sInf", Call("quadraticValues", g)))),
                    "Section 2, page 2: \"The algebraic connectivity of Γ is given by α(Γ) = min_{x⊥e, ‖x‖=1} xᵀLx.\" The infimum agrees with this minimum for n≥2, since the quadratic-value set is nonempty and compact.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("beta", "Maximum quadratic value", Graph(Eqn(Call("beta", g), Call("sSup", Call("quadraticValues", g)))),
                    "Section 2, page 2: \"Another related and useful quantity is β(Γ) = max_{x⊥e, ‖x‖=1} xᵀLx.\" The supremum agrees with this maximum for n≥2.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("spread", "Laplacian spread", Graph(Eqn(Call("spread", g), Sub(Call("beta", g), Call("alpha", g)))),
                    "Section 3, pages 4–5: \"We define the Laplacian spread of a digraph Γ by sp(Γ) = β(Γ) − α(Γ), that is, sp(Γ) is equal to the length of the real part of Wᵣ(L).\" The expression uses the same constrained real extrema as Section 2.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("quadraticValues_isCompact", "Compactness of the quadratic-value set", Graph(Call("IsCompact", Call("quadraticValues", g))),
                    "The zero-sum unit sphere is the intersection of a compact Euclidean sphere with a closed linear equation. Its continuous quadratic image is compact, including the empty cases at orders zero and one.",
                    DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
                Node("rayleigh_mem", "Normalization gives a quadratic value", RayleighBody(),
                    "A nonzero zero-sum vector can be divided by its Euclidean norm. The resulting unit vector has quadratic value equal to its Rayleigh quotient.",
                    DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
                Node("claim", "Conjecture 20", Iffn(Call("claim"), Parenthesized(ClaimBody())),
                    "Conjecture 20, page 16: \"The bound on the Laplacian spread of digraphs given in (5) can be reduced to a linear function in n with a slope of 1.\" The real constant C is independent of the order and the loopless unweighted digraph. Orders n≥2 are exactly those with a nonempty zero-sum unit sphere.",
                    DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
                Node("result", "Conjecture 20 is false", Notn(ClaimBody()),
                    "A five-vertex digraph has zero-sum vectors with Rayleigh values 3408/679 and 0. Replacing each vertex by m independent vertices multiplies both values by m. The order is 5m and the spread is at least (5+13/679)m, so no fixed intercept C can give a bound 5m+C for all positive m.",
                    DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));
    }

    private static Formula AdjacencyMatrix(Formula g) => App(Q("Matrix", "map"),
        App(Q("FiniteGraphEntropy", "adjacency"), App(Q("Digraph", "Adj"), g)),
        Parenthesized(Seq(Q("Nat", "cast"), Sp, Colon, Sp, Arrow(Naturals(), Reals()))));
    private static Formula ClaimBody() => Ex("C", Reals(), All("n", Naturals(), Imp(Leq(D(2), V("n")),
        All("G", Call("Digraph", FinN()), Imp(Loopless(), Leq(Call("spread", V("G")), Add(Cast(V("n")), V("C"))))))));
    private static Formula RayleighBody() => Graph(All("x", Arrow(FinN(), Reals()),
        Imp(Eqn(SumOver("i", App(V("x"), V("i"))), D(0)),
            Imp(Ne(V("x"), D(0)), Member(new Formula.Fraction(Quadratic(V("G"), V("x")),
                Call("dotProduct", V("x"), V("x"))), Call("quadraticValues", V("G")))))));
    private static Formula Quadratic(Formula g, Formula x) => Call("dotProduct", x,
        App(Q("Matrix", "mulVec"), Call("laplacian", g), x));
    private static Formula Vector(Formula x) => Parenthesized(Lam("i", FinN(), App(x, V("i"))));
    private static Formula Loopless() => All("i", FinN(), Notn(App(Q("Digraph", "Adj"), V("G"), V("i"), V("i"))));
    private static Formula Graph(Formula body) => All("n", Naturals(), All("G", Call("Digraph", FinN()), body));
    private static DocumentBlock Node(string selector, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("bce20-" + (selector switch { "outDegree" => "outdegree", "inDegree" => "indegree", "Balanced" => "balanced", "quadraticValues" => "quadraticvalues", "quadraticValues_isCompact" => "compact", "rayleigh_mem" => "rayleigh", _ => selector })),
            DeclarationHandle.Create(Prefix + selector), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Q(string owner, string name) => Seq(C(owner), Dot, C(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? C(name) : App(C(name), args);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula FinN() => Call("Fin", V("n"));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(Call("fun"), Sp, V(name), Sp, Colon, Sp, type, Sp, Mapsto, Sp, body);
    private static Formula SumOver(string name, Formula body) => Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, Colon, Sp, FinN())), Sp, body);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Reals()));
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Leq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iffn(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Andn(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Notn(Formula body) => Seq(Neg, Sp, Parenthesized(body));
}
