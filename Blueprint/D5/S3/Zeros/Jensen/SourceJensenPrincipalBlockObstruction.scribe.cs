using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class SourceJensenPrincipalBlockObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/SourceJensenPrincipalBlockObstruction.";
    private static Formula Dd => F.Id("d");
    private static Formula K => F.Id("K");
    private static Formula Hh => F.Id("H");
    private static Formula E => F.Id("e");
    private static Formula Qq => F.Id("q");
    private static Formula Rr => F.Id("r");
    private static Formula Ii => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula W => F.Id("w");
    private static Formula U => F.Id("u");
    private static Formula Next => Seq(Dd, Plus, D(1));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Call(Formula f, params Formula[] args) => Seq(f, Open,
        Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, a }).ToArray()), Close);
    private static Formula Op(string name, params Formula[] args) => Call(Seq(Operatorname, Grp(F.Id(name))), args);
    private static Formula P(Formula n) => Sub(F.Id("P"), n);
    private static Formula A(Formula n) => Sub(F.Id("a"), n);
    private static Formula Q(Formula a) => Call(F.Id("Q"), a);
    private static Formula EntryOf(Formula a, Formula i, Formula j) => Sub(a, Seq(i, Comma, j));
    private static Formula Block(Formula a, Formula f) => Seq(a, OpenBracket, f, Comma, f, CloseBracket);
    private static Formula Fin(Formula n) => Op("Fin", n);
    private static Formula MatrixDomain(Formula a, Formula n) => Seq(a, InMacro, Sp,
        Pow(Complexes, Seq(Open, n, Close, Times, Sp, Open, n, Close)));
    private static Formula Degree => Seq(Forall, Sp, Dd, InMacro, Sp, Nat, Comma, Dd, Ge, Sp, D(1), Colon);
    private static Formula Psd(Formula a) => Op("PosSemidef", a);
    private static Formula PositiveCoefficients => Seq(Forall, Sp, F.Id("k"), InMacro, Sp, Nat,
        Colon, D(0), Lt, Sp, A(F.Id("k")));
    private static Formula Chain(Formula w) => Seq(Widehat, Grp(Sub(F.Id("C"), w)));
    private static Formula Total(Formula w, Formula end) => Seq(Sum,
        Underscore, Grp(J, Eq, D(0)), Caret, Grp(end), Sub(w, J));
    private static Formula PrefixWeights => Seq(Forall, Sp, D(0), Le, Sp, J, Lt, Sp,
        D(2), Dd, Minus, D(1), Colon, Sub(U, J), Eq, Sub(W, J));
    private static Formula Nonnegative(Formula w) => Seq(Forall, Sp, J, Colon, Sub(w, J), Ge, Sp, D(0));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed literal Jensen coefficients obstruct unchanged positive principal extensions.",
        H("Literal Jensen Principal-Block Obstruction"),
        Blocks(
            Paragraph(Text("P_d is sourceJensenPolynomial d, with the actual coefficients "
                + "a(k)=sourceThetaMoment(k)/(2k)! and density Phi(x)/Re(xiReading(1/2)). "
                + "Q(A)=det(I+X A) is the complex matrix pencil polynomial, with entries "
                + "embedded as constant polynomials. It is distinct from the infinite reflected "
                + "xi series. A hat on C_w denotes the real forbiddenPartition polynomial "
                + "mapped coefficientwise to Complex. Fin n has indices 0 through n-1.")),
            Entry("source_jensen_coeff_edges", "The four edge coefficients", new Formula.Aligned([
                Seq(Degree, Op("coeff", P(Dd), D(0)), Eq, A(D(0)), Land, Sp,
                    Op("coeff", P(Dd), D(1)), Eq, A(D(1))),
                Seq(Land, Sp, Op("coeff", P(Dd), Next), Eq, D(0), Land, Sp,
                    Op("coeff", P(Dd), Dd), Eq, Frac,
                    Grp(Dd, Bang), Grp(Pow(Dd, Dd)), A(Dd))
            ]), "The independent finite sum has falling-factorial weights. The constant and "
                + "linear coefficients are a(0) and a(1); the next coefficient vanishes. "
                + "The leading weight is d!/d^d. Real a(k) are embedded in Complex here."),
            Entry("source_jensen_matching_normalization", "Matching fixes normalization and trace", Seq(
                Degree, MatrixDomain(K, Dd), Comma, Q(K), Eq, P(Dd), Implies, Sp,
                A(D(0)), Eq, D(1), Land, Sp, Op("Tr", K), Eq, A(D(1)), Land, Sp,
                Open, PositiveCoefficients, Close),
                "No positivity assumption on K is needed for this bridge. The constant "
                    + "determinant coefficient is one and its linear coefficient is the trace. "
                    + "The literal raw-moment bounds then determine the actual positive "
                    + "denominator and all positive coefficients from a(0)=1."),
            Entry("source_jensen_leading_coefficient_pos", "Strictly positive leading coefficient", Seq(
                Degree, A(D(0)), Eq, D(1), Implies, Sp, D(0), Lt, Sp, Op("coeff", P(Dd), Dd)),
                "The coefficient is (d!/d^d)a(d), with all factors strictly positive. "
                    + "The displayed complex inequality uses the real-axis order: the coefficient "
                    + "has zero imaginary part and strictly positive real part. Both obstruction "
                    + "proofs obtain a(0)=1 from exact matching before applying this result."),
            Entry("fixed_trace_principal_collapse", "Collapse at fixed trace", new Formula.Aligned([
                Seq(Forall, Sp, Dd, InMacro, Sp, Nat, Comma, MatrixDomain(K, Dd), Comma,
                    MatrixDomain(Hh, Next), Comma, E, Colon, Fin(Dd), To, Sp, Fin(Next), Colon),
                Seq(Op("Injective", E), Land, Sp, Psd(Hh), Land, Sp, Block(Hh, E), Eq, K,
                    Land, Sp, Op("Tr", Hh), Eq, Op("Tr", K), Implies),
                Seq(Exists, Sp, Qq, Colon, Op("Sum", Fin(Dd), Fin(D(1))), Equiv, Sp, Fin(Next), Comma,
                    Open, Forall, Sp, Ii, InMacro, Sp, Fin(Dd), Colon,
                    Call(Qq, Op("inl", Ii)), Eq, Call(E, Ii), Close),
                Seq(Land, Sp, EntryOf(Hh, Rr, Rr), Eq, D(0), Land, Sp,
                    Open, Forall, Sp, Ii, InMacro, Sp, Fin(Dd), Colon,
                    EntryOf(Hh, Call(E, Ii), Rr), Eq, D(0), Land, Sp,
                    EntryOf(Hh, Rr, Call(E, Ii)), Eq, D(0), Close),
                Seq(Land, Sp, Block(Hh, Qq), Eq, Op("diag", K, D(0)), Land, Sp, Q(Hh), Eq, Q(K))
            ]), "Here r=q(inr(0)), and Sum is the disjoint sum of index types. The equivalence "
                + "q extends the given injection itself. Equal traces make the unique complement "
                + "diagonal zero. The zero-weight support-face theorem for its diagonal projection "
                + "annihilates both new row and column. Thus the reindexed matrix is exactly "
                + "diag(K,0), where the zero block has size one, and the determinant polynomial "
                + "is unchanged. These hypotheses are consistent, for example for zero extensions; "
                + "the argument does not use a contradiction or source polynomial matching."),
            Entry("source_jensen_principal_block_obstruction", "No adjacent unchanged exact models",
                new Formula.Aligned([
                    Seq(Degree, Neg, Sp, Exists, Sp, MatrixDomain(K, Dd), Comma,
                        MatrixDomain(Hh, Next), Comma, E, Colon, Fin(Dd), To, Sp, Fin(Next), Colon),
                    Seq(Psd(K), Land, Sp, Psd(Hh), Land, Sp, Op("Injective", E), Land, Sp,
                        Block(Hh, E), Eq, K, Land, Sp, Q(K), Eq, P(Dd), Land, Sp, Q(Hh), Eq, P(Next))
                ]), "This holds for every positive degree and every injective principal inclusion. "
                    + "Both exact matches fix the trace at a(1). The generic collapse keeps the "
                    + "determinant unchanged, while coefficient d+1 vanishes in P_d and is nonzero "
                    + "in P_(d+1). Its positivity is derived from the literal moments and the "
                    + "matching constant coefficient. No independent analytic or normalization "
                    + "premise is present, and no existence of either model is asserted."),
            Entry("source_jensen_unchanged_family_obstruction", "No unchanged family", new Formula.Aligned([
                Seq(Neg, Sp, Exists, Sp, Open, Sub(K, Dd), Close, Comma, Open, Sub(E, Dd), Close, Colon,
                    Forall, Sp, Dd, InMacro, Sp, Nat, Comma, Dd, Ge, Sp, D(1), Colon),
                Seq(Psd(Sub(K, Dd)), Land, Sp, Op("Injective", Sub(E, Dd)), Land, Sp,
                    Block(Sub(K, Next), Sub(E, Dd)), Eq, Sub(K, Dd), Land, Sp,
                    Q(Sub(K, Dd)), Eq, P(Dd))
            ]), "The quantified family has K_d a complex Fin d by Fin d matrix and "
                + "e_d:Fin d -> Fin(d+1) for every natural d. Exact matching and unchanged "
                + "inclusion are required for every d>=1. Applying the adjacent obstruction "
                + "at d=1 already contradicts such a family."),
            Entry("source_jensen_chain_matching", "Matching fixes the actual weight sum", Seq(
                Degree, W, InMacro, Sp, Pow(Reals, Seq(D(2), Dd, Minus, D(1))), Comma,
                Open, Nonnegative(W), Close, Land, Sp, Chain(W), Eq, P(Dd), Implies, Sp,
                A(D(0)), Eq, D(1), Land, Sp, Total(W, Seq(D(2), Dd, Minus, D(2))), Eq, A(D(1)),
                Land, Sp, Open, PositiveCoefficients, Close),
                "Use the actual determinant identity for L_w^T L_w. Coefficient zero fixes "
                    + "a(0), and coefficient one together with cyclic trace gives the displayed "
                    + "total weight. The normalized coefficient signs follow from the literal "
                    + "analytic bounds. Nonnegative weights include zero and repeated weights."),
            Entry("source_jensen_unchanged_weights_obstruction", "No unchanged exact chain extension",
                new Formula.Aligned([
                    Seq(Degree, Neg, Sp, Exists, Sp, W, InMacro, Sp, Pow(Reals, Seq(D(2), Dd, Minus, D(1))),
                        Comma, U, InMacro, Sp, Pow(Reals, Seq(D(2), Dd, Plus, D(1))), Colon),
                    Seq(Open, Nonnegative(W), Close, Land, Sp, Open, Nonnegative(U), Close,
                        Land, Sp, Open, PrefixWeights, Close, Land, Sp,
                        Chain(W), Eq, P(Dd), Land, Sp, Chain(U), Eq, P(Next))
                ]), "The two exact matches give the same total a(1). An unchanged numerical "
                    + "prefix forces the appended weights u(2d-1) and u(2d) to zero. The "
                    + "actual bidiagonal matrix becomes diag(L_w,0), and two endpoint recurrences "
                    + "give C_u=C_w. The strictly positive next source coefficient contradicts "
                    + "that equality. This also covers d=1 and singular chains."))));

    private static DocumentBlock.Describe Entry(string name, string title, Formula formula,
        string prose) => Describe.Lean(DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
