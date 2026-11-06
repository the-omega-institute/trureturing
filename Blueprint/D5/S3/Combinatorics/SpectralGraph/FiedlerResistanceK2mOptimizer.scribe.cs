using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class FiedlerResistanceK2mOptimizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-resistance Fiedler maximum on labelled K2m has exactly two edge restrictions.",
        H("The fixed-resistance optimizer on the full labelled K2m family"),
        Blocks(
            Paragraph(Text("The parameter m ranges over every natural number at least three. Vertices are Fin (2+m): the hubs are castAdd m 0 and castAdd m 1, and leaf i is natAdd 2 i. Only the two hub-to-leaf edges for each i are present. Every edge conductance varies independently over positive reals. The ordinary, unnormalized wLap, its nonzero mean-zero Rayleigh infimum lambda2, and the original harmonic-current totalRes are those of FiedlerResistanceInvariantWeightsRefutation. The total counts every unordered distinct vertex pair once, including nonedges. Feasible weights satisfy totalRes=R0 for an arbitrary R0>0; there is no total-conductance or competitor-symmetry constraint.")),
            Node("graph", "The labelled complete bipartite graph", "K2m",
                All("m", Nat(), Eqn(Call("K2m", V("m")), QCall("SimpleGraph", "comap",
                    QCall("Equiv", "symm", Call("finSumFinEquiv", D(2), V("m"))),
                    Call("completeBipartiteGraph", Call("Fin", D(2)), Call("Fin", V("m")))))),
                "The left part has two labelled hubs and the right part has m labelled leaves."),
            Node("decidable", "Decidable adjacency", "K2m_dec", All("m", Nat(),
                Call("DecidableRel", QCall("SimpleGraph", "Adj", Graph()))), "Adjacency is decidable."),
            Node("constant", "The sharp product constant", "sharpConstant", All("m", Nat(),
                Eqn(Call("sharpConstant", V("m")), Mul(Add(V("m"), D(2)), Add(V("m"), Div(D(1), V("m")))))),
                "The constant is (m+2)(m+1/m), with every operation interpreted in the real numbers."),
            Node("ratio", "The nonzero splitting ratio", "splitRatio", All("m", Nat(),
                Eqn(Call("splitRatio", V("m")), QCall("Real", "sqrt", Div(Sub(V("m"), D(2)), Add(V("m"), D(2)))))),
                "For m at least three, the splitting ratio is strictly between zero and one."),
            Node("value", "The attained maximum value", "maxValue", Parameters(Eqn(T(), Div(Call("sharpConstant", V("m")), V("R")))),
                "The resistance level is positive in the theorem; maxValue is the ratio C_m/R0."),
            Node("plus", "The larger conductance", "plusConductance", Parameters(Eqn(A(), Mul(Div(T(), D(2)), Add(D(1), Call("splitRatio", V("m")))))),
                "This is t(1+rho)/2."),
            Node("minus", "The smaller conductance", "minusConductance", Parameters(Eqn(B(), Mul(Div(T(), D(2)), Sub(D(1), Call("splitRatio", V("m")))))),
                "This is t(1-rho)/2."),
            Node("edges", "Equality of the labelled edge restriction", "EdgeRestriction", All("m", Nat(), All("a", Real(), All("b", Real(), All("w", Weights(),
                Iff(Edges(V("a"), V("b"), V("w")), All("i", Call("Fin", V("m")), And(Eqn(App(V("w"), Pair(U(), Leaf(V("i")))), V("a")), Eqn(App(V("w"), Pair(HubV(), Leaf(V("i")))), V("b"))))))))),
                "Only the 2m labelled edges are compared. Values on all nonedges are unrestricted."),
            Node("weights", "An explicit representative with constant leaf families", "uniformWeights", All("m", Nat(), All("a", Real(), All("b", Real(), All("p", Vertices(), All("q", Vertices(),
                Eqn(App(Call("uniformWeights", V("m"), V("a"), V("b")), Pair(V("p"), V("q"))),
                    Call("ite", Or(Eqn(V("p"), U()), Eqn(V("q"), U())), V("a"), V("b")))))))),
                "The representative assigns a to pairs containing the first hub and b otherwise. Its edge restriction is the required constant pair; its nonedge values are only a choice of representative."),
            Node("exchange", "Exchange of the two hubs", "exchangeWeights", All("m", Nat(), All("w", Weights(), All("e", PairType(),
                Eqn(App(Call("exchangeWeights", V("m"), V("w")), V("e")), App(V("w"), QCall("Sym2", "map", QCall("Equiv", "swap", U(), HubV()), V("e"))))))),
                "The swap fixes every leaf and interchanges the two labelled hubs."),
            Node("claim", "The complete optimizer conclusion", "OptimizerClaim", Parameters(Iff(Call("OptimizerClaim", V("m"), V("R")), Conclusion())),
                "The conjunction gives the upper bound, both explicit positive feasible attainments, the iff exclusion of every other labelled edge restriction, distinctness, exchange in both directions, and invariance under arbitrary nonedge changes."),
            LeanNode("hub", "The labelled hubs", "The original hub coordinate is castAdd m j for j in Fin 2.", DescribeRole.Definition),
            LeanNode("leaf", "The labelled leaves", "The original leaf coordinate is natAdd 2 i for i in Fin m.", DescribeRole.Definition),
            LeanNode("adj_hub_hub", "No hub-to-hub edges", "The two hubs are never adjacent in K2m.", DescribeRole.Theorem),
            LeanNode("adj_leaf_leaf", "No leaf-to-leaf edges", "No two leaves are adjacent in K2m.", DescribeRole.Theorem),
            LeanNode("lap_hermitian", "Symmetry of the native weighted Laplacian", "For every finite simple graph with decidable adjacency and every real pair-weight function, the original wLap is Hermitian.", DescribeRole.Theorem),
            LeanNode("lap_mul", "Native weighted edge action", "For every n,G,w,x and vertex i, the original matrix action is the sum over adjacent j of w(i,j)*(x i-x j).", DescribeRole.Theorem),
            LeanNode("lap_one", "Constants lie in the native kernel", "For every n,G,w, the original Laplacian sends the all-ones vector to zero.", DescribeRole.Theorem),
            LeanNode("proj_hermitian", "The constant projector is Hermitian", "For every n, constProj n is Hermitian.", DescribeRole.Theorem),
            LeanNode("proj_mul", "The constant projector averages coordinates", "For every n,x,i, its matrix action at i is the coordinate sum of x divided by n.", DescribeRole.Theorem),
            LeanNode("proj_energy", "The constant quadratic form", "For every n,x, the constant-projector energy is the square of the coordinate sum divided by n.", DescribeRole.Theorem),
            LeanNode("proj_sq", "Idempotence of the constant projector", "For every positive n, constProj n squared equals itself.", DescribeRole.Theorem),
            LeanNode("lap_proj", "The original Laplacian annihilates constants", "For every n,G,w, wLap G w times constProj n is zero.", DescribeRole.Theorem),
            LeanNode("lap_sum", "The native Laplacian image has sum zero", "For every n,G,w,x, the coordinate sum of wLap G w acting on x is zero.", DescribeRole.Theorem),
            LeanNode("delta", "Original pair-difference vector", "For every n,p,q, delta p q is the difference of the two standard coordinate vectors.", DescribeRole.Definition),
            LeanNode("delta_sum", "Pair differences have zero sum", "For every n,p,q, the coordinate sum of delta p q is zero.", DescribeRole.Theorem),
            LeanNode("delta_dot", "Pair differences read coordinate gaps", "For every n,p,q,x, dotProduct (delta p q) x equals x p-x q.", DescribeRole.Theorem),
            LeanNode("delta_ne", "Distinct pair differences are nonzero", "For every n and distinct p,q, delta p q is nonzero.", DescribeRole.Theorem),
            LeanNode("proj_delta", "The constant projector kills pair differences", "For every n,p,q, constProj n acting on delta p q is zero.", DescribeRole.Theorem),
            LeanNode("double_sum_lt", "Symmetric pair sums count unordered pairs twice", "For every n and symmetric real pair function f with zero diagonal, the sum over all ordered pairs equals twice the sum over i less than j.", DescribeRole.Theorem),
            LeanNode("pair_gap_sum", "Independent-part pair-gap identity", "For every m, real function s on Fin m and real t, the ordered off-diagonal sum of s i+s j-2*t equals 2*(m-1)*(sum s-m*t).", DescribeRole.Theorem),
            LeanNode("constProj", "The constant-space projection matrix", "Every entry is the reciprocal of the number of vertices.", DescribeRole.Definition),
            LeanNode("zero_eigenvalue_count", "The native zero eigenvalue has multiplicity one", "For m positive and every positive edge weighting of K2m, exactly one indexed native Hermitian eigenvalue is zero.", DescribeRole.Theorem),
            LeanNode("lambda2_spectral", "The Rayleigh value and the native eigenvalues", "For m positive and every positive edge weighting, lambda2 is positive, L-lambda2*(I-P) is positive semidefinite, and every nonzero native eigenvalue is at least lambda2.", DescribeRole.Theorem),
            LeanNode("resistance_spectral", "Harmonic all-pairs resistance and the native spectrum", "For m positive and every positive edge weighting, the harmonic totalRes is (m+2) times the sum of reciprocal native Hermitian eigenvalues, with the zero inverse interpreted as zero.", DescribeRole.Theorem),
            LeanNode("leafSum", "The two conductances incident to a leaf", "The original leafSum is the sum of its two hub-to-leaf conductances.", DescribeRole.Definition),
            LeanNode("lap_trace", "The native Laplacian trace", "The trace equals twice the sum of all leafSum values, for arbitrary real weights.", DescribeRole.Theorem),
            LeanNode("product_bound_trace", "The sharp product bound and its trace equality consequence", "For every m at least three and positive edge weighting, lambda2*totalRes is at most C_m; equality forces the sum of leafSum values to be m*lambda2.", DescribeRole.Theorem),
            LeanNode("equality_parameters", "The positive uniform parameters forced by equality", "Product equality forces positive a and b, common across every leaf, with a+b=lambda2 and (m+2)*a*b=lambda2 squared.", DescribeRole.Theorem),
            LeanNode("uniformWeights_edges", "The explicit representative has its prescribed edge restriction", "The original uniformWeights representative has first-hub conductance a and second-hub conductance b on every leaf.", DescribeRole.Theorem),
            LeanNode("splitRatio_facts", "Bounds and square of the splitting ratio", "For m at least three, splitRatio is strictly between zero and one and its square is (m-2)/(m+2).", DescribeRole.Theorem),
            LeanNode("parameter_roots", "Both common-sign quadratic solutions", "For every m at least three, if a+b=t and (m+2)*a*b=t squared, then the ordered pair is t/2*(1+rho),t/2*(1-rho), or the reverse pair.", DescribeRole.Theorem),
            LeanNode("uniform_extremal", "The extremal Rayleigh and harmonic resistance values", "For every m at least three and positive a,b,t satisfying a+b=t and (m+2)*a*b=t squared, any positive K2m weighting with that edge restriction has lambda2=t and totalRes=C_m/t.", DescribeRole.Theorem),
            LeanNode("exchange_edges", "Hub exchange interchanges the two edge families", "The original hub swap maps EdgeRestriction a b to EdgeRestriction b a for arbitrary real a and b.", DescribeRole.Theorem),
            Node("result", "The fixed-resistance maximum and all maximizers", "result", All("m", Nat(), Imp(Leq(D(3), V("m")), All("R", Real(), Imp(Lt(D(0), V("R")), Conclusion())))),
                "The weighted energy is a sum of positive edge squares, so its kernel is exactly the constants. The inverse of L+P, for the constant projection P, constructs the unique harmonic voltage for every distinct boundary pair. Summing its reciprocal-current expression gives R=(m+2) trace(L+) and then the reciprocal-eigenvalue formula. Leaf-difference Rayleigh tests give trace L at least 2m lambda2. The reciprocal eigenvalue estimate gives lambda2 R at most C_m. Equality forces trace equality and makes every leaf difference a lambda2 eigenvector, hence both conductance families are constant across leaves. Exact unit-current solutions give the uniform-case resistance formula and force a+b=t and (m+2)ab=t squared. These equations have exactly the two common-sign solutions. A positive quadratic-form certificate proves lambda2=t on either solution; the resistance formula gives R=R0. Thus the maximum is attained without compactness or zero-conductance relaxation. The proof reuses the original Rayleigh certificate, reciprocal-trace theorem and nonedge invariance.", DescribeRole.Theorem))));

    private static DocumentBlock LeanNode(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fko-supplier-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(DescribeId.Create("fko-" + id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string x) => StrataLint.Scribe.FormulaDsl.Id(x);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula QCall(string owner, string name, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name))), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string n, Formula ty, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), ty, b);
    private static Formula Exists(string n, Formula ty, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), ty, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Par(a), Sp, Cdot, Sp, Par(b));
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Parameters(Formula body) => All("m", Nat(), All("R", Real(), body));
    private static Formula Vertices() => Call("Fin", Add(D(2), V("m")));
    private static Formula PairType() => Call("Sym2", Vertices());
    private static Formula Weights() => Seq(PairType(), Sp, To, Sp, Real());
    private static Formula Graph() => Call("K2m", V("m"));
    private static Formula U() => QCall("Fin", "castAdd", V("m"), D(0));
    private static Formula HubV() => QCall("Fin", "castAdd", V("m"), D(1));
    private static Formula Leaf(Formula i) => QCall("Fin", "natAdd", D(2), i);
    private static Formula Pair(Formula a, Formula b) => Seq(V("s"), Open, a, Comma, b, Close);
    private static Formula T() => Call("maxValue", V("m"), V("R"));
    private static Formula A() => Call("plusConductance", V("m"), V("R"));
    private static Formula B() => Call("minusConductance", V("m"), V("R"));
    private static Formula Lambda(Formula w) => Call("lambda2", Graph(), w);
    private static Formula Resistance(Formula w) => Call("totalRes", Graph(), w);
    private static Formula Edges(Formula a, Formula b, Formula w) => Call("EdgeRestriction", V("m"), a, b, w);
    private static Formula Positive(Formula w) => All("e", PairType(), Imp(In(V("e"), QCall("SimpleGraph", "edgeSet", Graph())), Lt(D(0), App(w, V("e")))));
    private static Formula Attainment(Formula a, Formula b)
    {
        Formula w = Call("uniformWeights", V("m"), a, b);
        return And(Positive(w), And(Eqn(Resistance(w), V("R")), And(Eqn(Lambda(w), T()), Edges(a, b, w))));
    }
    private static Formula Conclusion()
    {
        Formula w = V("w"), z = V("z");
        Formula bound = All("w", Weights(), Imp(Positive(w), Imp(Eqn(Resistance(w), V("R")), Leq(Lambda(w), T()))));
        Formula classification = All("w", Weights(), Imp(Positive(w), Imp(Eqn(Resistance(w), V("R")), Iff(Eqn(Lambda(w), T()), Or(Edges(A(), B(), w), Edges(B(), A(), w))))));
        Formula distinct = new Formula.Not(Exists("w", Weights(), And(Edges(A(), B(), w), Edges(B(), A(), w))));
        Formula exchange(Formula a, Formula b) => All("w", Weights(), Imp(Edges(a, b, w), Edges(b, a, Call("exchangeWeights", V("m"), w))));
        Formula same = All("e", PairType(), Imp(In(V("e"), QCall("SimpleGraph", "edgeSet", Graph())), Eqn(App(w, V("e")), App(z, V("e")))));
        Formula invariance = All("w", Weights(), All("z", Weights(), Imp(same, And(Eqn(Lambda(w), Lambda(z)), Eqn(Resistance(w), Resistance(z))))));
        return And(bound, And(Attainment(A(), B()), And(Attainment(B(), A()), And(classification, And(distinct, And(exchange(A(), B()), And(exchange(B(), A()), invariance)))))));
    }
}
