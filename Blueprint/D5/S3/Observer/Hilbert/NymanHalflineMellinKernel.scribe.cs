using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class NymanHalflineMellinKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.";
    private static Formula Rho => F.Rho;
    private static Formula Beta => F.Beta;
    private static Formula K => Seq(F.Id("k"), Underscore, Grp(Rho));
    private static Formula J => Seq(F.Id("J"), Underscore, Grp(Rho));
    private static Formula SqNorm(Formula x) => Seq(Vert, Sp, x, Vert, Sp, Caret, Grp(D(2)));
    private static Formula Energy => Seq(Frac, Grp(D(1)), Grp(D(2), Beta, Minus, D(1)),
        Plus, Frac, Grp(D(1)), Grp(SqNorm(Seq(Rho, Minus, D(1)))));
    private static Formula Bind => Seq(Forall, Sp, Rho, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma,
        Beta, Eq, Re, Sp, Rho, Gt, Sp, Frac, Grp(D(1)), Grp(D(2)), Comma, Rho, Neq, D(1), Comma, Sp);
    private static Formula Indicator(Formula lo, Formula hi) => Seq(D(1), Underscore,
        Grp(Open, lo, Comma, hi, Close));
    private static Formula Raw => Seq(Indicator(D(0), D(1)), Open, F.Id("x"), Close,
        Overline, Grp(F.Id("x"), Caret, Grp(Rho, Minus, D(1))), Minus,
        Indicator(D(1), Infty), Open, F.Id("x"), Close, Frac,
        Grp(Overline, Grp(Open, Rho, Minus, D(1), Close, Caret, Grp(Minus, D(1)))), Grp(F.Id("x")));
    private static Formula Mellin => Seq(Int, Underscore, Grp(D(0)), Caret, Grp(D(1)),
        F.Id("g"), Open, F.Id("x"), Close, F.Id("x"), Caret, Grp(Rho, Minus, D(1)), Thin, F.Id("dx"));
    private static Formula Tail => Seq(Int, Underscore, Grp(D(1)), Caret, Grp(Infty),
        Frac, Grp(F.Id("g"), Open, F.Id("x"), Close), Grp(F.Id("x")), Thin, F.Id("dx"));
    private static Formula Integrable(Formula body, Formula lo, Formula hi) => Seq(
        Operatorname, Grp(F.Id("IntegrableOn")), Open, Open, F.Id("x"), Mapsto, Sp, body,
        Close, Comma, Open, lo, Comma, hi, Close, Close);

    private static Formula A => F.Id("a");
    private static Formula X => F.Id("x");
    private static Formula Source(Formula a) => Seq(F.Id("F"), Underscore, Grp(a));
    private static Formula FracPart => Seq(Operatorname, Grp(F.Id("fract")), Open,
        Frac, Grp(D(1)), Grp(A, X), Close);
    private static Formula RealBind => Seq(Forall, Sp, A, InMacro, Sp, Mathbb, Grp(F.Id("R")),
        Comma, Sp, A, Ge, Sp, D(1), Comma, Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact Mellin separator kernel and dual norm on the positive half-line.",
        H("Half-Line Mellin Kernel"), Blocks(
            Paragraph(Text("Work in H=Lp(C,2,volume restricted to (0,infinity)). "
                + "Let beta=Re(rho)>1/2 and rho differ from one. Positive real bases use the "
                + "principal complex power. The kernel is conjugated because the first argument "
                + "of the complex inner product is conjugate-linear.")),
            Describe.Lean(DescribeId.Create("halfline-real-source-vector"),
                DeclarationHandle.Create(Prefix + "realSourceVector"), H("Real source vector"),
                StatementSource.FromAuthor(Disp(Seq(RealBind, Source(A), InMacro, Sp, F.Id("H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "F_a is the Lp class of x |-> ofReal(fract(1/(a*x))). "
                    + "The construction proves square integrability before taking the quotient."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("halfline-real-source-representative"),
                DeclarationHandle.Create(Prefix + "realSourceVector_coe_ae"),
                H("Actual representative"), StatementSource.FromAuthor(Disp(Seq(RealBind,
                    Source(A), Open, X, Close, Eq, FracPart, Quad,
                    Mathrm, Grp(F.Id("a"), Dot, F.Id("e"), Dot), Sp, Open, D(0), Comma, Infty, Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The equality is almost everywhere for positiveMeasure. Real values are "
                    + "embedded into C, and the measure and exponent remain those of H."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("halfline-real-source-natural"),
                DeclarationHandle.Create(Prefix + "realSourceVector_nat"),
                H("Natural sources agree"), StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                    F.Id("n"), Ge, Sp, D(1), Comma, Source(F.Id("n")), Eq,
                    Operatorname, Grp(F.Id("sourceVector")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Equality in the Lp quotient identifies the real-parameter construction "
                    + "with the original natural source family, including n=1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("halfline-real-source-tail"),
                DeclarationHandle.Create(Prefix + "realSourceVector_tail"),
                H("Reciprocal tail"), StatementSource.FromAuthor(Disp(Seq(RealBind,
                    Forall, Sp, X, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    X, Gt, Sp, D(1), Rightarrow, Sp, FracPart, Eq, Frac, Grp(D(1)), Grp(A, X)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Since 0 < 1/(a*x) < 1 on this tail, taking fractional part changes nothing. "
                    + "This is a pointwise identity for every real a at least one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("halfline-mellin-kernel"),
                DeclarationHandle.Create(Prefix + "halflineKernel"), H("Kernel vector"),
                StatementSource.FromAuthor(Disp(Seq(Bind, K, InMacro, Sp, F.Id("H")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The near-zero piece has square norm x^(2*beta-2); the tail has square norm "
                    + "norm(rho-1)^(-2)*x^(-2). Their integrability constructs the Lp vector."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("halfline-mellin-kernel-representative"),
                DeclarationHandle.Create(Prefix + "halflineKernel_coe_ae"), H("Conjugated representative"),
                StatementSource.FromAuthor(Disp(Seq(Bind, K, Open, F.Id("x"), Close,
                    Eq, Raw, Quad, Mathrm, Grp(F.Id("a"), Dot, F.Id("e"), Dot)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "This representative identity is almost everywhere for positiveMeasure. "
                    + "The two open intervals are disjoint; values at endpoints have measure zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("halfline-mellin-kernel-energy"),
                DeclarationHandle.Create(Prefix + "halflineKernel_norm_sq"), H("Exact kernel energy"),
                StatementSource.FromAuthor(Disp(Seq(Bind, SqNorm(K), Eq, Energy))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Disjoint support makes the square norm a sum. The power integral over (0,1) "
                    + "is 1/(2*beta-1); the integral of x^(-2) over (1,infinity) is one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("halfline-mellin-functional"),
                DeclarationHandle.Create(Prefix + "halflineFunctional"), H("Continuous complex-linear functional"),
                StatementSource.FromAuthor(Disp(Seq(Bind, Forall, Sp, F.Id("f"), InMacro, Sp, F.Id("H"),
                    Comma, J, Open, F.Id("f"), Close, Eq, Langle, Sp, K, Comma, F.Id("f"), Rangle))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The Riesz inner-product map defines J as a continuous C-linear map from H to C."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("halfline-mellin-functional-integrals"),
                DeclarationHandle.Create(Prefix + "halflineFunctional_integral"), H("Representative-independent integral formula"),
                StatementSource.FromAuthor(Disp(Seq(Bind, Forall, Sp, F.Id("f"), InMacro, Sp, F.Id("H"), Comma,
                    Forall, Sp, F.Id("g"), Colon, Mathbb, Grp(F.Id("R")), To, Sp, Mathbb, Grp(F.Id("C")), Comma,
                    F.Id("g"), Eq, Underscore, Grp(Mathrm, Grp(F.Id("a"), Dot, F.Id("e"), Dot)),
                    F.Id("f"), Rightarrow, Sp, Begin, Grp(F.Id("gathered")),
                    Integrable(Seq(F.Id("g"), Open, F.Id("x"), Close, F.Id("x"), Caret,
                        Grp(Rho, Minus, D(1))), D(0), D(1)), RowBreak, Land, Sp,
                    Integrable(Seq(Frac, Grp(F.Id("g"), Open, F.Id("x"), Close),
                        Grp(F.Id("x"))), D(1), Infty), RowBreak, Land, Sp,
                    J, Open, F.Id("f"), Close, Eq, Mellin, Minus,
                    Open, Rho, Minus, D(1), Close, Caret, Grp(Minus, D(1)), Tail,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every g equal to the Lp representative almost everywhere for positiveMeasure, "
                    + "g(x)*x^(rho-1) is integrable on (0,1), and g(x)/x is integrable on (1,infinity). "
                    + "The displayed identity holds for every such g, so it is independent of the "
                    + "chosen representative. Cauchy-Schwarz gives integrability, and rho-1 nonzero "
                    + "allows cancellation of the tail coefficient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("halfline-mellin-functional-norm"),
                DeclarationHandle.Create(Prefix + "halflineFunctional_norm_sq"), H("Exact operator norm"),
                StatementSource.FromAuthor(Disp(Seq(Bind, SqNorm(J), Eq, Energy))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The isometry of the Riesz map identifies the operator norm with the kernel norm. "
                    + "The result is an equality, with both support contributions retained."))), DescribeRole.Theorem))));
}
