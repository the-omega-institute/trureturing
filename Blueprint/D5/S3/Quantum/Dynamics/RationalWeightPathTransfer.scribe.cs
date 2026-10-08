using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class RationalWeightPathTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/RationalWeightPathTransfer.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/kirkland2019rationalweightspst");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kirkland, McLaren, Pereira, Plosker and Zhang (arXiv:1708.03283) conjecture that a weighted path on at least four vertices, with or without potentials, whose edge weights are all rational has no perfect state transfer between its end vertices at readout time pi, and prove it for n = 4 and for n congruent to 3 or 5 modulo 8. For every k >= 1 the statement holds for the paths on n = 2^k + 1 vertices, with arbitrary real potentials and in both directions; for k >= 3 these sizes are congruent to 1 modulo 8.",
        H("No perfect state transfer at time pi on rational paths with 2^k + 1 vertices"),
        Blocks(
            Node("hamiltonian", "The weighted path Hamiltonian", HamiltonianFormula(),
                "The vertices are 0, ..., m and the edge {t, t + 1} carries the weight r t for t in Fin m. The matrix has the real potential q i at the diagonal entry (i, i), the weight r i at the entries (i, i + 1) and (i + 1, i), and zero elsewhere; all entries are real numbers cast to complex numbers. This is the tridiagonal adjacency matrix with potentials of the source, on m + 1 vertices.",
                "pathHamiltonian", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("transfer", "Perfect state transfer", TransferFormula(),
                "Perfect state transfer from vertex a to vertex b at time t means |e_a^T exp(i t H) e_b|^2 = 1, where exp is the matrix exponential and normSq is the squared modulus of a complex number. The formal statement writes exp(i t H) as the repository propagator hamiltonianPropagator H s = exp(-i s H) at s = -t.",
                "HasPST", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mirror", "Transfer from the first vertex forces mirror-symmetric weights", MirrorFormula(),
                "Let U be unitary, commute with the path Hamiltonian H, and send the first basis vector to gamma times the last one, with |gamma| = 1. By induction on j, U e_j = gamma e_(m - j) and r t = r (m - 1 - t) for t < j. Indeed r_j U e_(j+1) = U(H e_j - q_j e_j - r_(j-1) e_(j-1)) = gamma (H e_(m-j) - q_j e_(m-j) - r_(j-1) e_(m-j+1)); by the induction hypothesis only the components at m - j - 1 and m - j remain, orthogonality of the columns j and j + 1 of U removes the second one, and the unit norm of column j + 1 together with the positivity of the weights gives r j = r (m - 1 - j). Here rev t is the mirror index m - 1 - t of the edge t, and last(m) is the vertex m. The source records the underlying fact as known, citing Kay: a symmetric tridiagonal Hamiltonian with perfect state transfer between its end vertices is persymmetric. The statement here is its form for an arbitrary unitary commuting with the path Hamiltonian, restricted to the edge weights.",
                "persymmetric_weights", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("classes", "Spectral parity classes of a transfer at time pi", ClassesFormula(),
                "Let c k = W a k conj(W b k) for the orthonormal eigenvectors W of H with eigenvalues lambda k. The hypotheses on the powers of H give sum_k c k lambda_k^p = 0 for p < m and = P for p = m; evaluating sum_k c k f(lambda k) on the monic polynomial f = prod_{l != k} (X - lambda l) gives c k prod_{l != k} (lambda k - lambda l) = P, so the eigenvalues are distinct and every c k is a nonzero real number. Transfer at time pi forces exp(i pi lambda_k) conj(W b k) = gamma conj(W a k) with gamma = exp(i pi H)(a, b), since the sum of the squared moduli of their differences vanishes. Hence |c k| = |W a k|^2, whose sum is 1, while sum_k c k = 0. The class A of indices with c k > 0 has sum_{k in A} c k = 1/2, and exp(i pi lambda_k) equals gamma on A and -gamma off A. Shifting the eigenvalues by an eigenvalue of the class A gives integers z, even on A and odd off A, with lambda k - lambda l = z k - z l. The source records as known that, after a common shift, the eigenvalues of a path with perfect state transfer at time pi between its end vertices are integers that alternate between even and odd. The identity P sum_{i in A} 1 / prod_{j != i} (z i - z j) = 1/2, stated for a general Hermitian matrix with the given moment data, is derived here.",
                "pst_parity_classes", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The rational weights statement on 2^k + 1 vertices", ClaimFormula(),
                "For k >= 1 and the path on n = 2^k + 1 vertices with edge weights r in Fin(2^k) -> R and potentials q in Fin(2^k + 1) -> R: if every weight is rational and positive, there is no perfect state transfer at time pi from the first vertex 0 to the last vertex 2^k, nor from the last vertex to the first. The rationality hypothesis is written as the existence of a rational number equal to each weight. The source states its conjecture for all n >= 4 and does not single out this family; the statement is the restriction of that conjecture to the sizes n = 2^k + 1, with k = 1 added.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Rational paths on 2^k + 1 vertices have no transfer at time pi", Disp(F.Id("claim")),
                "The propagator exp(i pi H) is symmetric, so both directions reduce to transfer from the last vertex to the first. The entries of H^p in the column of the first vertex vanish beyond distance p, and the entry at the last vertex of H^m is P = prod_t r t with m = 2^k. The spectral parity classes give integers z, even on a class A and odd off A, with P sum_{i in A} 1 / prod_{j != i} (z i - z j) = 1/2, and A is neither empty nor everything. The column of the propagator at the first vertex is gamma times the last basis vector, so the weights are mirror symmetric and P is the square Q^2 of a rational number Q. Since C(2^k - 1, j) is odd for every j < 2^k, the partial divided-difference sum over A has 2-adic valuation 0. Then 2 v_2(Q) = v_2(1/2) = -1, which is impossible. This is partial progress on the conjecture of the source: k = 1 gives n = 3, below the range n >= 4 of the conjecture; k = 2 gives n = 5, one of the cases proved in the source; the new sizes are those with k >= 3, namely n = 9, 17, 33, ...; the other sizes are not addressed.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("ratpath-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula App(Formula f, params Formula[] arguments) => new Formula.Apply(f, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Inst(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Smul(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Word(string word) => Seq(F.Text, Grp(F.Id(word)));
    private static Formula IfThenElse(Formula condition, Formula then, Formula otherwise) =>
        Seq(Word("if"), Sp, condition, Sp, Word("then"), Sp, then, Sp, Word("else"), Sp, otherwise);
    private static Formula Entry(Formula m, Formula x, Formula y) => App(m, x, y);
    private static Formula PathH(Formula r, Formula q) => Call("pathHamiltonian", r, q);
    private static Formula Neg(Formula x) => new Formula.Negate(x);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula HamiltonianFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), i = F.Id("i"), j = F.Id("j");
        Formula value = IfThenElse(Equal(i, j), App(q, i),
            IfThenElse(Equal(Add(i, D(1)), j), App(r, i),
                IfThenElse(Equal(Add(j, D(1)), i), App(r, j), D(0))));
        Formula vertices = FinOf(Add(m, D(1)));
        return Disp(All("m", Naturals(), All("r", Arrow(FinOf(m), Reals()),
            All("q", Arrow(vertices, Reals()), All("i", vertices, All("j", vertices,
                Equal(Entry(PathH(r, q), i, j), value)))))));
    }

    private static Formula TransferFormula()
    {
        Formula v = F.Id("V"), h = F.Id("H"), t = F.Id("t"), a = F.Id("a"), b = F.Id("b");
        Formula body = Iff(Call("HasPST", h, t, a, b),
            Equal(Call("normSq", Call("hamiltonianPropagator", h, Neg(t), a, b)), D(1)));
        return Disp(All("V", F.Id("Type"), Inst(Call("Fintype", v), Inst(Call("DecidableEq", v),
            All("H", Call("Matrix", v, v, Complexes()), All("t", Reals(), All("a", v, All("b", v, body))))))));
    }

    private static Formula MirrorFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), u = F.Id("U"), g = F.Id("gamma"),
            t = F.Id("t"), x = F.Id("x");
        Formula vertices = FinOf(Add(m, D(1)));
        Formula h = PathH(r, q);
        Formula positive = All("t", FinOf(m), Less(D(0), App(r, t)));
        Formula unitary = Equal(Smul(new Formula.Power(u, Star), u), D(1));
        Formula commute = Equal(Smul(u, h), Smul(h, u));
        Formula column = All("x", vertices, Equal(Entry(u, x, D(0)),
            IfThenElse(Equal(x, Call("last", m)), g, D(0))));
        Formula conclusion = All("t", FinOf(m), Equal(App(r, t), App(r, Call("rev", t))));
        Formula body = Implies(Parenthesized(positive), All("U", Call("Matrix", vertices, vertices, Complexes()),
            Implies(unitary, Implies(commute, All("gamma", Complexes(),
                Implies(Equal(Call("normSq", g), D(1)), Implies(Parenthesized(column), conclusion)))))));
        return Disp(All("m", Naturals(), All("r", Arrow(FinOf(m), Reals()),
            All("q", Arrow(vertices, Reals()), body))));
    }

    private static Formula NodalSum(Formula z, Formula a)
    {
        Formula i = F.Id("i"), j = F.Id("j");
        Formula nodal = Seq(new Formula.Subscript(Prod, Seq(j, Sp, InMacro, Sp, Call("erase", Named("univ"), i))),
            Sp, Cast(Cast(Sub(App(z, i), App(z, j)), Integers()), Reals()));
        return Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, a)), Sp,
            new Formula.Power(Parenthesized(nodal), Neg(D(1))));
    }

    private static Formula ClassesFormula()
    {
        Formula v = F.Id("V"), h = F.Id("H"), a = F.Id("a"), b = F.Id("b"), m = F.Id("m"),
            weight = F.Id("P"), p = F.Id("p"), z = F.Id("z"), s = F.Id("A"), i = F.Id("i");
        Formula moments = All("p", Naturals(), Implies(LessEq(p, m),
            Equal(Entry(new Formula.Power(h, p), a, b), IfThenElse(Equal(p, m), weight, D(0)))));
        Formula classes = Some("z", Arrow(v, Integers()), Some("A", Call("Finset", v),
            And(Call("Injective", z), And(Call("Nonempty", s), And(NotEqual(s, Named("univ")),
                And(All("i", s, Call("Even", App(z, i))),
                    And(All("i", v, Implies(new Formula.Not(Parenthesized(Seq(i, Sp, InMacro, Sp, s))),
                            Call("Odd", App(z, i)))),
                        Equal(Mul(weight, NodalSum(z, s)), new Formula.Fraction(D(1), D(2))))))))));
        Formula body = All("a", v, All("b", v, Implies(NotEqual(a, b), All("m", Naturals(),
            Implies(Equal(Call("card", v), Add(m, D(1))), All("P", Reals(), Implies(NotEqual(weight, D(0)),
                Implies(Parenthesized(moments), Implies(Call("HasPST", h, Pi, a, b), classes)))))))));
        return Disp(All("V", F.Id("Type"), Inst(Call("Fintype", v), Inst(Call("DecidableEq", v),
            All("H", Call("Matrix", v, v, Complexes()), Implies(Call("IsHermitian", h), body))))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), q = F.Id("q"), j = F.Id("j"), x = F.Id("x");
        Formula n = new Formula.Power(D(2), k);
        Formula vertices = FinOf(Add(n, D(1)));
        Formula h = PathH(r, q);
        Formula rational = All("j", FinOf(n), Some("x", Rationals(), Equal(App(r, j), x)));
        Formula positive = All("j", FinOf(n), Less(D(0), App(r, j)));
        Formula noTransfer = And(new Formula.Not(Call("HasPST", h, Pi, D(0), Call("last", n))),
            new Formula.Not(Call("HasPST", h, Pi, Call("last", n), D(0))));
        Formula body = All("k", Naturals(), Implies(LessEq(D(1), k), All("r", Arrow(FinOf(n), Reals()),
            All("q", Arrow(vertices, Reals()),
                Implies(Parenthesized(rational), Implies(Parenthesized(positive), noTransfer))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
