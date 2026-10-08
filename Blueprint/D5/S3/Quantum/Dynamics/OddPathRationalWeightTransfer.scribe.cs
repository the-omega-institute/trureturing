using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OddPathRationalWeightTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/OddPathRationalWeightTransfer.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/kirkland2019rationalweightspst");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kirkland, McLaren, Pereira, Plosker and Zhang (arXiv:1708.03283) conjecture that a weighted path on at least four vertices, with or without potentials, whose edge weights are all rational has no perfect state transfer between its end vertices at readout time pi, and prove it for n = 4 and for n congruent to 3 or 5 modulo 8. The statement holds for every odd number of vertices n = 2m + 1 with m >= 1, with arbitrary real potentials and in both directions. The conjecture is not settled for the even sizes n >= 6.",
        H("No perfect state transfer at time pi on rational paths with an odd number of vertices"),
        Blocks(
            Node("gram", "Gram determinant of the middle-vertex moments", GramFormula(),
                "Let H be the path Hamiltonian on the vertices 0, ..., 2m, invariant under the reversal rev x = 2m - x, and let c be the middle vertex m. Since H is real symmetric, (H^(a+b))(c, c) = sum_i (H^a)(i, c) (H^b)(i, c). The column of H^a at c is invariant under the reversal, vanishes at the vertices at distance more than a from c, and its entry at the vertex m + a is the product w_a = r(m) r(m + 1) ... r(m + a - 1) of the a edge weights following c. Pairing each vertex below c with its mirror image gives (H^(a+b))(c, c) = T(a, 0) T(b, 0) + 2 sum_{d >= 1} T(a, d) T(b, d) with T(a, d) = (H^a)(m + d, c). For a, d <= j the matrix T is lower triangular with diagonal entries w_a, so the Hankel matrix of the moments is T diag(1, 2, ..., 2) T^T and its determinant is 2^j (w_0 w_1 ... w_j)^2. In the formal statement the matrix is indexed by a, b in Fin(j + 1), and r(m + t), for t < a <= j <= m, is the weight of the edge {m + t, m + t + 1} cast to a complex number. The source obtains the weight next to the middle vertex of a mirror-symmetric path with an odd number of vertices from the eigenvalues, through the orthogonal similarity of Cantoni and Butler between a mirror-symmetric matrix and a direct sum of two blocks of about half the size; the case j = 1 of the identity, (H^2)(c, c) - (H(c, c))^2 = 2 r(m)^2, expresses the same weight by the first two moments at the middle vertex. The identity is the expression of the Hankel determinants of the moments of a Jacobi matrix by its off-diagonal entries, for the block acting on the reversal-invariant vectors, whose first off-diagonal entry is sqrt(2) r(m); it is derived here directly for the path Hamiltonian.",
                "middle_moment_gram_det", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The rational weights statement on an odd number of vertices", ClaimFormula(),
                "For m >= 1 and the path on n = 2m + 1 vertices with edge weights r in Fin(2m) -> R and potentials q in Fin(2m + 1) -> R: if every weight is rational and positive, there is no perfect state transfer at time pi from the first vertex 0 to the last vertex 2m, nor from the last vertex to the first. The rationality hypothesis is written as the existence of a rational number equal to each weight. The source states its conjecture for all n >= 4; the statement is the restriction of that conjecture to the odd sizes, with n = 3 added.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Rational paths with an odd number of vertices have no transfer at time pi", Disp(F.Id("claim")),
                "The propagator exp(i pi H) is symmetric, so both directions reduce to transfer from the last vertex to the first. If the entry gamma of exp(i pi H) at the last and first vertices has modulus one, write gamma = exp(i pi theta) with theta real; subtracting theta from every potential keeps the weights and multiplies the propagator by exp(-i pi theta), so one may assume gamma = 1. Then H is invariant under the reversal, and the moments (H^p)(c, c) at the middle vertex c = m are integers mu p congruent to C(m, p) modulo 2. For j <= m the integer Hankel determinant D_j = det [mu(a + b)], a, b <= j, equals 2^j Q^2, where Q is the product over a <= j of the products of the a weights following c, a nonzero rational number. Modulo 2 the matrix is [C(m, a + b)]. If m is odd, take j = m: the entries with a + b > m vanish and those with a + b = m equal 1, so the matrix is anti-triangular with unit anti-diagonal and D_m is odd. If m is even, write m = 2^v s with s odd and v >= 1 and take j = 2^v - 1: over the field with two elements (1 + X)^m = (1 + X^(2^v))^s, so for a + b < 2^(v+1) the coefficient C(m, a + b) is odd exactly when a + b is 0 or 2^v, the matrix is the permutation matrix of 0 -> 0, a -> 2^v - a, and D_j is odd. In both cases j is odd, and comparing 2-adic valuations in D_j = 2^j Q^2 gives 0 = j + 2 v_2(Q), which is impossible. The source proves the conjecture for n = 4 and, for odd n, for n congruent to 3 or 5 modulo 8, from the irrationality of the weight next to the middle vertex; these are the sizes for which the determinant D_1 is odd. This is partial progress on the conjecture of the source: m = 1 gives n = 3, below the range n >= 4 of the conjecture; every odd n >= 5 is covered, the sizes beyond the cases of the source being those congruent to 1 or 7 modulo 8; the even sizes n >= 6 are not addressed.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("oddpath-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call("Fin", n);
    private static Formula Entry(Formula m, Formula x, Formula y) => App(m, x, y);
    private static Formula PathH(Formula r, Formula q) => Call("pathHamiltonian", r, q);
    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula BigProd(Formula index, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(index, Sp, InMacro, Sp, set)), Sp, body);

    private static Formula Edges(Formula m) => FinOf(Mul(D(2), m));
    private static Formula Vertices(Formula m) => FinOf(Add(Mul(D(2), m), D(1)));

    private static Formula GramFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), x = F.Id("x"), y = F.Id("y"),
            c = F.Id("c"), j = F.Id("j"), a = F.Id("a"), b = F.Id("b"), t = F.Id("t");
        Formula h = PathH(r, q);
        Formula size = FinOf(Add(j, D(1)));
        Formula invariant = All("x", Vertices(m), All("y", Vertices(m),
            Equal(Entry(h, Call("rev", x), Call("rev", y)), Entry(h, x, y))));
        Formula hankel = Seq(
            new Formula.Subscript(Named("det"), Seq(a, Comma, Sp, b, Sp, InMacro, Sp, size)), Sp,
            Entry(new Formula.Power(h, Add(a, b)), c, c));
        Formula weights = BigProd(a, size, BigProd(t, FinOf(a), Cast(App(r, Add(m, t)), Complexes())));
        Formula value = Mul(new Formula.Power(D(2), j), new Formula.Power(Parenthesized(weights), D(2)));
        Formula body = Implies(Parenthesized(invariant), All("c", Vertices(m),
            Implies(Equal(Cast(c, Naturals()), m), All("j", Naturals(),
                Implies(LessEq(j, m), Equal(hankel, value))))));
        return Disp(All("m", Naturals(), All("r", Arrow(Edges(m), Reals()),
            All("q", Arrow(Vertices(m), Reals()), body))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), r = F.Id("r"), q = F.Id("q"), j = F.Id("j"), x = F.Id("x");
        Formula h = PathH(r, q);
        Formula last = Call("last", Mul(D(2), m));
        Formula rational = All("j", Edges(m), Some("x", Rationals(), Equal(App(r, j), x)));
        Formula positive = All("j", Edges(m), Less(D(0), App(r, j)));
        Formula noTransfer = And(new Formula.Not(Call("HasPST", h, Pi, D(0), last)),
            new Formula.Not(Call("HasPST", h, Pi, last, D(0))));
        Formula body = All("m", Naturals(), Implies(LessEq(D(1), m), All("r", Arrow(Edges(m), Reals()),
            All("q", Arrow(Vertices(m), Reals()),
                Implies(Parenthesized(rational), Implies(Parenthesized(positive), noTransfer))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
