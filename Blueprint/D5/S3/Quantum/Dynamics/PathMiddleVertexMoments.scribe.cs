using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PathMiddleVertexMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PathMiddleVertexMoments.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/kirkland2019rationalweightspst");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be the Hamiltonian of a weighted path on the 2m + 1 vertices 0, ..., 2m, with positive edge weights and real potentials, whose propagator exp(i pi H) has the entry 1 at the last and first vertices. Then H is invariant under the reversal of the vertices, its eigenvalues are distinct integers that are even on a class A of m + 1 indices and odd on the other m, the eigenvectors of the odd class vanish at the middle vertex c = m, and the eigenvector of index k in A has squared modulus prod_{l not in A} (z k - z l) / prod_{l in A, l != k} (z k - z l) at c. The diagonal entries (H^p)(c, c) are integers congruent to the binomial coefficients C(m, p) modulo 2.",
        H("Middle-vertex spectral weights and integer moments of odd paths with end transfer at time pi"),
        Blocks(
            Node("symmetric", "Transfer with phase one makes the Hamiltonian reversal invariant", SymmetricFormula(),
                "The hypothesis says that the entry of exp(i pi H) at the last and first vertices equals 1; hamiltonianPropagator H s = exp(-i s H) is the repository propagator, taken at s = -pi. This entry has modulus one, so the column of the first vertex of the unitary matrix exp(i pi H) is the last basis vector, and the reversal form of a unitary commuting with the path Hamiltonian gives exp(i pi H) e_i = e_(2m - i) for every vertex i: the propagator is the reversal permutation matrix R. Since H commutes with exp(i pi H), comparing the entries of R H and H R at (x, rev y) gives H(rev x, rev y) = H(x, y), where rev x = 2m - x and last(2m) is the vertex 2m. The source records the underlying fact as known, citing Kay: a symmetric tridiagonal Hamiltonian with perfect state transfer between its end vertices is persymmetric. The statement here is its form for the path Hamiltonian with positive weights and transfer phase one, for the potentials as well as the weights.",
                "reversal_symmetric", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("weights", "Spectral weights at the middle vertex", WeightsFormula(),
                "Let W be the unitary matrix of orthonormal eigenvectors of H and lambda k its eigenvalues, and write E k = exp(i pi lambda_k). The spectral form of exp(i pi H) = R gives W(rev x, k) = E k W(x, k); applying it twice to a nonzero entry of the column k gives (E k)^2 = 1. Let A be the set of indices with E k = 1. Then lambda_k is an even integer for k in A and an odd integer otherwise, and W(c, k) = 0 for k outside A because the middle vertex c is fixed by the reversal. The trace of R is 1, since c is its only fixed vertex, and it equals the sum of the E k, so #A - #A^c = 1 and #A = m + 1. The entries of H^p at the last and first vertices vanish for p < 2m and equal the product of all the weights for p = 2m; by the mirror symmetry of the weights this product is rho^2 with rho = r 0 r 1 ... r (m - 1). The entries of H^p at the middle and first vertices vanish for p < m and equal rho for p = m, and only the indices of A contribute to them. Evaluating these moment relations on nodal polynomials gives |W(0, k)|^2 prod_{l != k} (lambda_k - lambda_l) = rho^2 and W(c, k) conj(W(0, k)) prod_{l in A, l != k} (lambda_k - lambda_l) = rho for k in A. In particular the eigenvalues are distinct, and dividing the squared modulus of the second relation by the first gives the stated formula. In the formal statement eigenvalues and eigenvectorUnitary are the eigenvalues and the eigenvector matrix attached to the Hermitian matrix H, and the middle vertex is a vertex c whose value is m. The source records as known that the eigenvectors of a mirror-symmetric Hamiltonian are symmetric or antisymmetric, citing Cantoni and Butler, and that after a common shift the eigenvalues of a path with perfect state transfer at time pi between its end vertices are integers that alternate between even and odd. The count #A = m + 1 and the formula for the squared modulus at the middle vertex are derived here.",
                "middle_vertex_weights", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("moments", "Integer moments at the middle vertex and their parity", MomentsFormula(),
                "By the spectral theorem (H^p)(c, c) = sum_k |W(c, k)|^2 lambda_k^p, and by the spectral weights at the middle vertex this is the sum over k in A of z_k^p P_B(z k) / prod_{l in A, l != k} (z k - z l), where P_A and P_B are the monic integer polynomials whose roots are the eigenvalues of the even class A and of the odd class. By the Lagrange coefficient formula over the m + 1 nodes of A, this sum is the coefficient of X^m in the remainder of X^p P_B modulo P_A, which is an integer mu p. Modulo 2 the polynomial P_A becomes X^(m+1) and P_B becomes (X + 1)^m, so mu p is congruent to the coefficient of X^m in X^p (X + 1)^m, which is C(m, m - p) = C(m, p) for p <= m and 0 = C(m, p) for p > m. In the formal statement the congruence is the equality of the images of mu p and of C(m, p) in the integers modulo 2. For p = 1 the moment is the potential at the middle vertex, which the source expresses as the alternating sum of the eigenvalues in its corollary on middle weights.",
                "middle_vertex_moments", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("midmoments-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Entry(Formula m, Formula x, Formula y) => App(m, x, y);
    private static Formula PathH(Formula r, Formula q) => Call("pathHamiltonian", r, q);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula NotIn(Formula a, Formula s) =>
        new Formula.Not(Parenthesized(Seq(a, Sp, InMacro, Sp, s)));
    private static Formula BigProd(Formula index, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(index, Sp, InMacro, Sp, set)), Sp, body);

    private static Formula Edges(Formula m) => FinOf(Mul(D(2), m));
    private static Formula Vertices(Formula m) => FinOf(Add(Mul(D(2), m), D(1)));
    private static Formula Positive(Formula m, Formula r) =>
        All("t", Edges(m), Less(D(0), App(r, F.Id("t"))));
    private static Formula PhaseOne(Formula m, Formula h) =>
        Equal(Call("hamiltonianPropagator", h, Neg(Pi), Call("last", Mul(D(2), m)), D(0)), D(1));
    private static Formula OverPaths(Formula body)
    {
        Formula m = F.Id("m");
        return Disp(All("m", Naturals(), All("r", Arrow(Edges(m), Reals()),
            All("q", Arrow(Vertices(m), Reals()), body))));
    }

    private static Formula SymmetricFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), x = F.Id("x"), y = F.Id("y");
        Formula h = PathH(r, q);
        Formula conclusion = All("x", Vertices(m), All("y", Vertices(m),
            Equal(Entry(h, Call("rev", x), Call("rev", y)), Entry(h, x, y))));
        return OverPaths(Implies(Parenthesized(Positive(m, r)), Implies(PhaseOne(m, h), conclusion)));
    }

    private static Formula WeightsFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), c = F.Id("c"), z = F.Id("z"),
            s = F.Id("A"), k = F.Id("k"), l = F.Id("l");
        Formula h = PathH(r, q);
        Formula w = Call("eigenvectorUnitary", h);
        Formula difference = Cast(Cast(Sub(App(z, k), App(z, l)), Integers()), Reals());
        Formula ratio = new Formula.Fraction(
            BigProd(l, Call("compl", s), difference), BigProd(l, Call("erase", s, k), difference));
        Formula weight = All("k", s, Equal(Call("normSq", Entry(w, c, k)), ratio));
        Formula vanish = All("k", Vertices(m), Implies(NotIn(k, s), Equal(Entry(w, c, k), D(0))));
        Formula spectrum = All("k", Vertices(m),
            Equal(Call("eigenvalues", h, k), Cast(App(z, k), Reals())));
        Formula oddOff = All("k", Vertices(m), Implies(NotIn(k, s), Call("Odd", App(z, k))));
        Formula evenOn = All("k", s, Call("Even", App(z, k)));
        Formula classes = Some("z", Arrow(Vertices(m), Integers()), Some("A", Call("Finset", Vertices(m)),
            And(Call("Injective", z), And(Equal(Call("card", s), Add(m, D(1))),
                And(Parenthesized(evenOn), And(Parenthesized(oddOff), And(Parenthesized(spectrum),
                    And(Parenthesized(vanish), Parenthesized(weight)))))))));
        Formula middle = All("c", Vertices(m), Implies(Equal(Cast(c, Naturals()), m), classes));
        return OverPaths(Implies(Call("IsHermitian", h), Implies(Parenthesized(Positive(m, r)),
            Implies(PhaseOne(m, h), middle))));
    }

    private static Formula MomentsFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), c = F.Id("c"), mu = F.Id("mu"),
            p = F.Id("p");
        Formula h = PathH(r, q);
        Formula residues = Call("ZMod", D(2));
        Formula integer = All("p", Naturals(),
            Equal(Entry(new Formula.Power(h, p), c, c), Cast(App(mu, p), Complexes())));
        Formula parity = All("p", Naturals(),
            Equal(Cast(App(mu, p), residues), Cast(Call("choose", m, p), residues)));
        Formula moments = Some("mu", Arrow(Naturals(), Integers()),
            And(Parenthesized(integer), Parenthesized(parity)));
        Formula middle = All("c", Vertices(m), Implies(Equal(Cast(c, Naturals()), m), moments));
        return OverPaths(Implies(Parenthesized(Positive(m, r)), Implies(PhaseOne(m, h), middle)));
    }
}
