using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class NormalizedJensenDegreeLoweringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed theta-moment Jensen polynomials satisfy exact degree lowering.",
        H("Normalized Jensen Degree Lowering"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-theta-kernel"),
                DeclarationHandle.Create(Prefix + "sourceThetaKernel"),
                H("Fixed even theta kernel"),
                StatementSource.FromAuthor(KernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "K denotes sourceThetaKernel. The natural index starts at zero, so n+1 "
                    + "runs over the positive integers. Absolute value specifies the even "
                    + "extension of the positive half-line expression. The primed sum denotes "
                    + "Lean's totalized tsum; this definition asserts no convergence theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-theta-density"),
                DeclarationHandle.Create(Prefix + "sourceThetaDensity"),
                H("Fixed density expression"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Xx, Real()), Call(F.Id("p"), Xx), Eq,
                    Fraction(Call(F.Id("K"), Xx), Call(Re, XiCenter()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "p denotes sourceThetaDensity, with the real part of the frozen xiReading "
                    + "at one half as its exact denominator. Private checked consequences of "
                    + "xi_reading_conj identify that real part with the complex central value "
                    + "and identify the complex coercion of p with K divided by that value. "
                    + "No nonzero-denominator or probability-mass theorem is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-theta-moment"),
                DeclarationHandle.Create(Prefix + "sourceThetaMoment"),
                H("Even density moments"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Kk, Natural()), Sub(F.Id("m"), Twice(Kk)), Eq,
                    Int, Underscore, Grp(Real()), Sp, Pow(Xx, Twice(Kk)), Sp,
                    Call(F.Id("p"), Xx), Thin, F.Id("d"), Xx))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "sourceThetaMoment(k) is m at index 2k. The integral is the real "
                    + "Lebesgue integral of x^(2k) times the displayed density. It uses Lean's "
                    + "totalized integral and does not assert integrability."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-theta-coefficient"),
                DeclarationHandle.Create(Prefix + "sourceThetaCoefficient"),
                H("Fixed moment coefficients"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Kk, Natural()), Sub(F.Id("a"), Kk), Eq,
                    Fraction(Sub(F.Id("m"), Twice(Kk)), Seq(Open, Twice(Kk), Close, Bang))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "a denotes the fixed sequence sourceThetaCoefficient. Its denominator "
                    + "is (2k)!, not k!. No Taylor-coefficient correspondence or assertion "
                    + "that a at zero is one is used."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-jensen"),
                DeclarationHandle.Create(Prefix + "normalizedJensen"),
                H("Canonical Jensen adapter"),
                StatementSource.FromAuthor(AdapterFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "N(b,d) denotes normalizedJensen b d for any real coefficient sequence b. "
                    + "J is the frozen jensenPolynomial: its coefficients are choose(d,k) "
                    + "times gamma(n+k), for k from zero through d. Here gamma(k)=k!b(k), "
                    + "the shift is zero, and polynomial composition scales the variable "
                    + "by the real inverse of d. The final map is the coefficient embedding "
                    + "from real to complex polynomials. X is the polynomial indeterminate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-jensen-polynomial"),
                DeclarationHandle.Create(Prefix + "sourceJensenPolynomial"),
                H("Independent finite source polynomial"),
                StatementSource.FromAuthor(Disp(Seq(
                    Domain(Dd, Natural()), Sub(F.Id("P"), Dd), Eq, FallingSum(F.Id("a"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P at index d denotes sourceJensenPolynomial d, defined independently "
                    + "by this finite sum in Complex[X]. descFactorial(d,k) is the natural "
                    + "falling factorial d(d-1)...(d-k+1), with value one at k=0; its "
                    + "quotient by d^k is the prescribed weight. Natural factors and real "
                    + "coefficients are coerced to Complex. The upper limit is exactly d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-jensen-falling-factorial"),
                DeclarationHandle.Create(Prefix + "normalizedJensen_eq_fallingFactorial_sum"),
                H("Exact canonical normalization"),
                StatementSource.FromAuthor(Disp(Seq(
                    GenericDomain(D(1)), N(Dd), Eq, FallingSum(F.Id("b"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real sequence and every natural d at least one, the canonical "
                    + "adapter equals the finite falling-factorial sum. The proof distributes "
                    + "composition and coefficient mapping and uses the exact identity "
                    + "descFactorial(d,k)=k! choose(d,k)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-jensen-degree-lowering"),
                DeclarationHandle.Create(Prefix + "normalizedJensen_degree_lowering"),
                H("Universal polynomial degree lowering"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    GenericDomain(D(2)),
                    Seq(N(Dd), Minus, Fraction(D(1), Dd), Sp, F.Id("X"), Sp,
                        N(Dd), Apos, Eq, N(Previous()), Circ,
                        Open, Fraction(Previous(), Dd), Sp, F.Id("X"), Close)
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is an equality of complex polynomials for every real sequence b. "
                    + "The prime denotes Polynomial.derivative and the circle denotes "
                    + "polynomial composition. Comparing coefficients reduces it to the "
                    + "falling-factorial recurrence, including the top index k=d and all "
                    + "indices beyond d. The degree bound makes both d and d-1 nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-jensen-canonical-bridge"),
                DeclarationHandle.Create(Prefix + "sourceJensenPolynomial_eq_normalizedJensen"),
                H("Source and canonical polynomial equality"),
                StatementSource.FromAuthor(Disp(Seq(
                    DegreeDomain(D(1)), Sub(F.Id("P"), Dd), Eq,
                    Call(F.Id("N"), F.Id("a"), Dd)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent literal source polynomial equals the canonical adapter "
                    + "at the fixed density-moment coefficient sequence. This is the preceding "
                    + "normalization theorem specialized to a and read in the reverse direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-jensen-degree-lowering"),
                DeclarationHandle.Create(Prefix + "source_jensen_degree_lowering"),
                H("Exact source degree lowering at every complex argument"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(DegreeDomain(D(2)), Domain(F.Id("v"), Complex())),
                    Seq(Call(Sub(F.Id("P"), Dd), F.Id("v")), Minus,
                        Fraction(F.Id("v"), Dd), Sp,
                        Call(Seq(Sub(F.Id("P"), Dd), Apos), F.Id("v")), Eq,
                        Call(Sub(F.Id("P"), Previous()),
                            Seq(Fraction(Previous(), Dd), Sp, F.Id("v"))))
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P'(v) means Polynomial.derivative evaluated at v. The proof uses the "
                    + "named source-to-canonical equality at d and d-1, then evaluates the "
                    + "universal lowering identity at v. All subtraction of natural degrees "
                    + "is interpreted in Nat before coercion; d at least two supplies the "
                    + "required bounds. No root-reality, RH, positivity, analytic convergence, "
                    + "or exact polynomial-degree premise is imposed."))),
                DescribeRole.Theorem))));

    private static Formula Xx => F.Id("x");
    private static Formula Kk => F.Id("k");
    private static Formula Dd => F.Id("d");
    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Previous() => Seq(Dd, Minus, D(1));
    private static Formula Twice(Formula f) => Seq(D(2), Sp, f);
    private static Formula Fraction(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Call(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula N(Formula degree) => Call(F.Id("N"), F.Id("b"), degree);
    private static Formula Domain(Formula v, Formula type) =>
        Seq(Forall, Sp, v, InMacro, type, Comma, Sp);
    private static Formula DegreeDomain(Formula lower) =>
        Seq(Domain(Dd, Natural()), lower, Leq, Sp, Dd, Rightarrow, Sp);
    private static Formula GenericDomain(Formula lower) => Seq(
        Forall, Sp, F.Id("b"), Colon, Natural(), To, Real(), Comma, Sp, DegreeDomain(lower));
    private static Formula XiCenter() =>
        Call(F.Id("xiReading"), Fraction(D(1), D(2)));

    private static Formula FallingSum(Formula coefficient) => Seq(
        Sum, Underscore, Grp(Kk, Eq, D(0)), Caret, Grp(Dd), Sp,
        Fraction(Call(F.Id("descFactorial"), Dd, Kk), Pow(Dd, Kk)), Sp,
        Sub(coefficient, Kk), Sp, Pow(F.Id("X"), Kk));

    private static Formula AdapterFormula() => Disp(Seq(
        Forall, Sp, F.Id("b"), Colon, Natural(), To, Real(), Comma, Sp,
        Domain(Dd, Natural()), N(Dd), Eq,
        Call(Sub(Seq(Operatorname, Grp(F.Id("map"))), Seq(Real(), To, Complex())),
            Seq(Call(F.Id("J"), Seq(Kk, Mapsto, Sp, Kk, Bang, Sp, Sub(F.Id("b"), Kk)),
                    Dd, D(0)), Circ, Open, Fraction(D(1), Dd), Sp, F.Id("X"), Close))));

    private static Formula KernelFormula()
    {
        Formula positiveIndex = Seq(Open, F.Id("n"), Plus, D(1), Close);
        Formula abs = Seq(Bar, Xx, Bar);
        Formula first = Seq(D(4), Sp, Pow(Pi, D(2)), Sp, Pow(positiveIndex, D(4)), Sp,
            Call(Exp, Fraction(Seq(D(9), Sp, abs), D(2))));
        Formula second = Seq(D(6), Sp, Pi, Sp, Pow(positiveIndex, D(2)), Sp,
            Call(Exp, Fraction(Seq(D(5), Sp, abs), D(2))));
        Formula decay = Call(Exp, Seq(Minus, Pi, Sp, Pow(positiveIndex, D(2)), Sp,
            Call(Exp, Twice(abs))));
        return Disp(Seq(Domain(Xx, Real()), Call(F.Id("K"), Xx), Eq,
            Sum, Apos, Underscore, Grp(F.Id("n"), InMacro, Natural()), Sp,
            Open, first, Minus, second, Close, Sp, decay));
    }
}
