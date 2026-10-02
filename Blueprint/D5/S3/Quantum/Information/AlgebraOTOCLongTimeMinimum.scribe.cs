using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class AlgebraOTOCLongTimeMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/AlgebraOTOCLongTimeMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/andreadakis2024scrambling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a block structure with sectors of type (n_J, d_J), J = 1, ..., r, and D = sum_J n_J d_J, the non-resonant long-time average of the algebra OTOC over all eigenbases of the D-dimensional Hilbert space is at least 1 - (sum_J d_J + sum_J n_J - r) / D, and the product basis attains this value. This proves the conjecture of F. Andreadakis, E. Dallas and P. Zanardi (arXiv:2312.13386, Section IV).",
        H("The minimum of the long-time algebra OTOC"),
        Blocks(
            Node("proj", "The projection onto the algebra", ProjFormula(F.Id("projA"),
                    F.Id("partialTraceLeft"), F.Id("n"), true),
                "The Hilbert space is the direct sum over J of C^{n_J} tensor C^{d_J}, indexed by Idx(n, d), the pairs (J, (a, b)) with a < n_J and b < d_J. The algebra A acts as the identity on each C^{n_J} and arbitrarily on each C^{d_J}. Its Hilbert-Schmidt projection keeps the diagonal block X_J of X, traces out the first factor and spreads the result evenly over it: P_A(X) is the block-diagonal matrix with blocks (1/n_J) I_{n_J} tensor Tr_{n_J}(X_J).",
                "projA", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("projp", "The projection onto the commutant", ProjFormula(F.Id("projAc"),
                    F.Id("partialTraceRight"), F.Id("d"), false),
                "The commutant A' acts arbitrarily on each C^{n_J} and as the identity on each C^{d_J}. Its Hilbert-Schmidt projection is the block-diagonal matrix with blocks Tr_{d_J}(X_J) tensor (1/d_J) I_{d_J}.",
                "projAc", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ket", "Rank-one operators of an eigenbasis", KetFormula(),
                "For a matrix U whose columns phi_k form the eigenbasis, ketBra(U, k, l) is the operator |phi_k><phi_l|, with entries U(i, k) times the complex conjugate of U(j, l).",
                "ketBra", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("r0", "The first kernel", R0Formula(),
                "R^(0)(P, U) has (l, k) entry the squared Hilbert-Schmidt norm of P(|phi_k><phi_l|).",
                "R0", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("r1", "The second kernel", R1Formula(),
                "R^(1)(P, U) has (k, l) entry the Hilbert-Schmidt inner product of P(Pi_k) and P(Pi_l), with Pi_k = |phi_k><phi_k|. For the two projections above both images are Hermitian, so the inner product is real and equals the real part of the trace.",
                "R1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("term", "One summand of the long-time average", TermFormula(),
                "For real square matrices R and S, term(R, S) is Tr(R S) minus one half of the trace of the product of the diagonal matrices carrying the diagonals of R and S.",
                "term", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lta", "The non-resonant long-time average", LtaFormula(),
                "The long-time average of the A-OTOC under the non-resonance condition, the paper's Eq. (6), for the Hamiltonian whose eigenbasis is given by the columns of U. The sum runs over the two orders (A, A') and (A', A) of the algebra and its commutant, and D = sum_J n_J d_J is the dimension.",
                "lta", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "The paper fixes the algebra class and asks for the algebra of that class that minimizes the long-time average for a given Hamiltonian; by the algebra-Hamiltonian duality used in its Section IV A this is the same as fixing the algebra in its distinguished basis and varying the eigenbasis U over the unitary group. The conjecture states that the least value is 1 - (sum_J d_J + sum_J n_J - r) / D, attained by the eigenbasis of product vectors in the distinguished basis. Here r is the number of sectors, d_Z in the paper.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds", Disp(F.Id("claim")),
                "Write the J block of phi_k as an n_J x d_J matrix C, its weight q = |C|^2 (squared Frobenius norm) and its purity p = Tr((C C^*)^2). Let F be D times one minus the long-time average. The (k, l) entry of R^(1) for the commutant projection is a sum over J of Tr(Tr_{d_J}(Pi_k) Tr_{d_J}(Pi_l)) / d_J. For any coefficients c_k this quadratic form equals the sum over J of the squared Frobenius norm of Tr_{d_J}(Y_J) divided by d_J, where Y = U diag(c) U^*; by Cauchy-Schwarz in each block this is at most the squared Frobenius norm of Y, which is the sum of |c_k|^2 because U is unitary. So that kernel lies below the identity, and the same holds for the other projection. The matching R^(0) is a sum of Gram matrices, so each cross trace Tr(R^(0) R^(1)) is at most the trace of R^(0), and the diagonal entries of R^(0) are sums of purities divided by n_J or d_J, at most the corresponding sums of q^2. With x + y - x y increasing on the unit square and q summing to 1 over J for each k and to n_J d_J over k for each J, F is at most the sum over J of ((n_J + d_J) sum_k q^2 - sum_k q^4) / (n_J d_J). For n_J + d_J = M at least 3, (M - 1) x - M x^2 + x^4 = x (1 - x) (M - 1 - x - x^2) is nonnegative on [0, 1], so the J term is at most n_J + d_J - 1; for n_J = d_J = 1, 2 x^2 - x^4 is superadditive on the simplex, so the term is at most 1. Hence F is at most sum_J (n_J + d_J - 1), which is the lower bound. At U = 1 the entries of the four kernels are indicator functions of equal first or second coordinates within a block, scaled by 1/n_J or 1/d_J, and the two cross traces equal sum_J d_J and sum_J n_J while both diagonal traces equal r; so the identity attains the bound.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("andreadakis-2024-algebra-otoc-long-time-minimum"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("aot-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula EqTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffTo(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Plus2(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula At(Formula family, Formula index) =>
        new Formula.Subscript(family, index);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula size) => Call(F.Id("Fin"), size);
    private static Formula Family(Formula r) => Seq(Fin(r), Sp, To, Sp, Nat());
    private static Formula Index(Formula n, Formula d) => Call(F.Id("Idx"), n, d);
    private static Formula Square(Formula field, Formula n, Formula d) =>
        Seq(field, Caret, Grp(Index(n, d), Sp, F.Times, Sp, Index(n, d)));
    private static Formula Complex(Formula n, Formula d) =>
        Square(Seq(Mathbb, Grp(F.Id("C"))), n, d);
    private static Formula Adjoint(Formula value) => Seq(value, Caret, Grp(Star));
    private static Formula Trace(Formula value) => Call(F.Id("Tr"), value);
    private static Formula ReTrace(Formula left, Formula right) =>
        Call(F.Id("Re"), Trace(Seq(Adjoint(left), Sp, right)));

    // Binds r, n and d, then the given body.
    private static Formula Blocks3(Formula body)
    {
        Formula r = F.Id("r"), n = F.Id("n"), d = F.Id("d");
        return All(r, Nat(), All(n, Family(r), All(d, Family(r), body)));
    }

    private static Formula ProjFormula(Formula name, Formula trace, Formula scale, bool left)
    {
        Formula n = F.Id("n"), d = F.Id("d"), x = F.Id("X"), j = F.Id("J");
        Formula block = Call(trace, Call(F.Id("blockDiag"), x, j));
        Formula identity = Call(F.Id("I"), At(scale, j));
        Formula product = left
            ? Call(F.Id("kronecker"), identity, block)
            : Call(F.Id("kronecker"), block, identity);
        Formula blocks = Parenthesized(Seq(j, Sp, Mapsto, Sp,
            Mul(Frac(D(1), At(scale, j)), product)));
        return Disp(Blocks3(All(x, Complex(n, d),
            EqTo(Call(name, n, d, x), Call(F.Id("blockDiagonal"), blocks)))));
    }

    private static Formula KetFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), u = F.Id("U"), k = F.Id("k"), l = F.Id("l"),
            i = F.Id("i"), j = F.Id("j");
        Formula entry = Call(F.Id("entry"), Call(F.Id("ketBra"), u, k, l), i, j);
        Formula value = Mul(Call(u, i, k), Seq(Overline, Grp(Call(u, j, l))));
        return Disp(Blocks3(All(u, Complex(n, d), All(k, Index(n, d), All(l, Index(n, d),
            All(i, Index(n, d), All(j, Index(n, d), EqTo(entry, value))))))));
    }

    private static Formula KernelFormula(Formula name, Formula row, Formula column,
        Formula left, Formula right)
    {
        Formula n = F.Id("n"), d = F.Id("d"), p = F.Id("P"), u = F.Id("U");
        Formula entry = Call(F.Id("entry"), Call(name, p, u), row, column);
        return Disp(Blocks3(All(p, Seq(Complex(n, d), Sp, To, Sp, Complex(n, d)),
            All(u, Complex(n, d), All(row, Index(n, d), All(column, Index(n, d),
                EqTo(entry, ReTrace(Call(p, left), Call(p, right)))))))));
    }

    private static Formula R0Formula()
    {
        Formula u = F.Id("U"), k = F.Id("k"), l = F.Id("l");
        Formula ket = Call(F.Id("ketBra"), u, k, l);
        return KernelFormula(F.Id("R0"), l, k, ket, ket);
    }

    private static Formula R1Formula()
    {
        Formula u = F.Id("U"), k = F.Id("k"), l = F.Id("l");
        return KernelFormula(F.Id("R1"), k, l, Call(F.Id("ketBra"), u, k, k),
            Call(F.Id("ketBra"), u, l, l));
    }

    private static Formula DiagonalPart(Formula m) =>
        Call(F.Id("diagonal"), Call(F.Id("diag"), m));

    private static Formula TermFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), r = F.Id("R"), s = F.Id("S");
        Formula value = Sub(Trace(Seq(r, Sp, s)),
            Mul(Frac(D(1), D(2)), Trace(Seq(DiagonalPart(r), Sp, DiagonalPart(s)))));
        return Disp(Blocks3(All(r, Square(Real(), n, d), All(s, Square(Real(), n, d),
            EqTo(Call(F.Id("term"), r, s), value)))));
    }

    private static Formula Dimension(Formula n, Formula d)
    {
        Formula j = F.Id("J");
        return SumOver(j, Mul(At(n, j), At(d, j)));
    }

    private static Formula LtaFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), u = F.Id("U");
        Formula pa = Call(F.Id("projA"), n, d), pc = Call(F.Id("projAc"), n, d);
        Formula first = Call(F.Id("term"), Call(F.Id("R0"), pa, u), Call(F.Id("R1"), pc, u));
        Formula second = Call(F.Id("term"), Call(F.Id("R0"), pc, u), Call(F.Id("R1"), pa, u));
        Formula value = Sub(D(1), Mul(Frac(D(1), Dimension(n, d)),
            Parenthesized(Plus2(first, second))));
        return Disp(Blocks3(All(u, Complex(n, d), EqTo(Call(F.Id("lta"), n, d, u), value))));
    }

    private static Formula ClaimFormula()
    {
        Formula r = F.Id("r"), n = F.Id("n"), d = F.Id("d"), j = F.Id("J"), u = F.Id("U");
        Formula positiveN = All(j, Fin(r), Less(D(0), At(n, j)));
        Formula positiveD = All(j, Fin(r), Less(D(0), At(d, j)));
        Formula unitary = Call(F.Id("unitaryGroup"), Index(n, d), Seq(Mathbb, Grp(F.Id("C"))));
        Formula values = Seq(Esc, OpenBrace, Call(F.Id("lta"), n, d, u), Sp, Mid, Sp, u, Sp,
            InMacro, Sp, unitary, Esc, CloseBrace);
        Formula bound = Sub(D(1), Frac(Sub(Plus2(SumOver(j, At(d, j)), SumOver(j, At(n, j))), r),
            Dimension(n, d)));
        Formula body = Imp(positiveN, Imp(positiveD, Call(F.Id("IsLeast"), values, bound)));
        return Disp(IffTo(F.Id("claim"),
            All(r, Nat(), All(n, Family(r), All(d, Family(r), body)))));
    }
}
