using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class SourceThetaMomentBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/SourceThetaMomentBounds.";
    private static Formula N => F.Id("n");
    private static Formula Xx => F.Id("x");
    private static Formula K => F.Id("k");
    private static Formula M => Seq(Open, N, Plus, D(1), Close);
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Call(Formula f, Formula a) => Seq(f, Open, a, Close);
    private static Formula Ex(Formula a) => Call(Exp, a);
    private static Formula Fr(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula AbsX => Seq(Bar, Xx, Bar);
    private static Formula T => Call(Sub(F.Id("T"), N), Xx);
    private static Formula B => Sub(F.Id("b"), N);
    private static Formula SumB => Seq(Sum, Underscore, Grp(N, Eq, D(0)),
        Caret, Grp(Infty), B);
    private static Formula Gauss => Ex(Seq(Minus, Pow(Xx, D(2))));
    private static Formula Moment => Seq(Int, Underscore, Grp(R),
        Pow(Xx, Seq(D(2), K)), Call(Phi, Xx), Thin, F.Id("d"), Xx);
    private static Formula Domains => Seq(Forall, Sp, N, InMacro, Sp, Nat, Comma, Xx, InMacro, Sp, R, Colon);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal theta moments are positive and finite under a summable Gaussian bound.",
        H("Literal Theta Moment Bounds"),
        Blocks(
            Paragraph(Text("Phi is sourceThetaKernel, the fixed even theta series. The symbols "
                + "a(k) and p(x) denote sourceThetaCoefficient(k) and sourceThetaDensity(x). "
                + "Z is the real part of xiReading(1/2), and p(x)=Phi(x)/Z. No central-value "
                + "integral identity is assumed in the analytic estimates.")),
            Entry("thetaSummand", "Literal summand", Seq(Domains, T, Eq,
                Open, D(4), Pow(Pi, D(2)), Pow(M, D(4)),
                Ex(Fr(Seq(D(9), AbsX), D(2))), Minus, D(6), Pi, Pow(M, D(2)),
                Ex(Fr(Seq(D(5), AbsX), D(2))), Close,
                Ex(Seq(Minus, Pi, Pow(M, D(2)), Ex(Seq(D(2), AbsX))))),
                "The index n starts at zero, so n+1 runs over the positive integers. "
                    + "This is exactly the summand of the fixed kernel.", DescribeRole.Definition),
            Entry("thetaMajorant", "Gaussian coefficients", Seq(Forall, Sp, N, InMacro, Sp, Nat,
                Colon, B, Eq, D(4), Pow(Pi, D(2)), Pow(M, D(4)),
                Ex(Fr(Seq(Minus, Pi, Pow(M, D(2))), D(2)))),
                "These positive real coefficients give a bound independent of x.", DescribeRole.Definition),
            Entry("source_theta_summand_bounds", "Positive summand estimate", Seq(Domains,
                D(0), Lt, Sp, T, Land, Sp, T, Le, Sp, B, Gauss),
                "For t=|x| and m=n+1, factor the difference using exp(9t/2)=exp(5t/2)exp(2t). "
                    + "Positivity follows from pi>3 and m>=1. For the upper bound, drop the negative "
                    + "term and use m^2 exp(2t)>=(m^2+exp(2t))/2 and "
                    + "exp(2t)>=1+2t+2t^2. The remaining quadratic is "
                    + "2(t-3/8)^2+39/32, which is positive."),
            Entry("source_theta_majorant_summable", "Summable majorant", Seq(
                Call(Seq(Operatorname, Grp(F.Id("Summable"))), Seq(N, Mapsto, Sp, B))),
                "Summability is over n in the natural numbers. Compare b(n) with "
                    + "4 pi^2 (n+1)^4 exp(-pi(n+1)/2), a shifted polynomial times a geometric sequence."),
            Entry("source_theta_summable", "Pointwise convergence", Seq(Forall, Sp, Xx, InMacro, Sp, R,
                Colon, Call(Seq(Operatorname, Grp(F.Id("Summable"))), Seq(N, Mapsto, Sp, T))),
                "For every fixed real x, the entire natural-indexed summand sequence is summable "
                    + "by the positive majorant. This verifies convergence of the literal tsum."),
            Entry("source_theta_continuous", "Continuity", Seq(
                Phi, InMacro, Sp, Pow(F.Id("C"), D(0)), Open, R, Comma, R, Close),
                "Every summand is continuous. Since exp(-x^2)<=1, the summable b(n) bound "
                    + "is uniform on the whole real line; uniform summability gives continuity."),
            Entry("source_theta_even", "Evenness", Seq(Forall, Sp, Xx, InMacro, Sp, R, Colon,
                Call(Phi, Seq(Minus, Xx)), Eq, Call(Phi, Xx)),
                "Absolute value is unchanged by negation, so every literal summand and the sum are even."),
            Entry("source_theta_gaussian_bound", "Positive Gaussian bound", Seq(
                Forall, Sp, Xx, InMacro, Sp, R, Colon, D(0), Lt, Sp, Call(Phi, Xx), Land, Sp,
                Call(Phi, Xx), Le, Sp, Open, SumB, Close, Gauss),
                "One strictly positive summand gives positivity of Phi. Summing the estimates "
                    + "gives the displayed bound with the finite explicit constant sum b(n). "
                    + "At x=0 the same inequality also shows that this constant is strictly positive."),
            Entry("source_theta_raw_moments", "All raw even moments", Seq(
                Forall, Sp, K, InMacro, Sp, Nat, Colon,
                Open, Xx, Mapsto, Sp, Pow(Xx, Seq(D(2), K)), Call(Phi, Xx), Close,
                InMacro, Sp, Pow(F.Id("L"), D(1)), Open, R, Close, Land, Sp, D(0), Lt, Sp, Moment),
                "Integrability is with respect to real Lebesgue measure. Polynomial-Gaussian "
                    + "integrability and the kernel bound dominate each even moment. The integrand "
                    + "is continuous and nonnegative and is strictly positive at x=1, so its integral is positive."),
            Entry("source_theta_normalization", "Normalization from the constant coefficient", Seq(
                Sub(F.Id("a"), D(0)), Eq, D(1), Implies, Sp,
                F.Id("Z"), Eq, Int, Underscore, Grp(R), Call(Phi, Xx), Thin, F.Id("d"), Xx,
                Land, Sp, D(0), Lt, Sp, F.Id("Z"), Land, Sp,
                Int, Underscore, Grp(R), Call(F.Id("p"), Xx), Thin, F.Id("d"), Xx, Eq, D(1),
                Land, Sp, Open, Forall, Sp, K, InMacro, Sp, Nat, Colon, D(0), Lt, Sp, Sub(F.Id("a"), K), Close),
                "Here Z=Re(xiReading(1/2)) and a(k) is the actual density moment divided by (2k)!. "
                    + "The unit constant coefficient first excludes Z=0. Pulling the constant "
                    + "denominator through the integral yields Z equal to the positive raw mass. "
                    + "All raw even moments and factorial denominators are positive. This result "
                    + "is conditional on a(0)=1; it does not independently establish a xi/theta integral identity."))));

    private static DocumentBlock.Describe Entry(string name, string title, Formula formula,
        string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
