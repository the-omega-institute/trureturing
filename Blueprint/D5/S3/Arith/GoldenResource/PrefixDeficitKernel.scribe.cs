using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class PrefixDeficitKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite geometric-prefix deficit has an exact positive-kernel integral and uniform two-sided bounds.",
        H("Finite Prefix Deficit Kernel"),
        Blocks(
            Paragraph(Text("For a natural exponent a, write S_a(t) = sum from k = 0 to a of t^k, "
                + "Q_a(t) = sum from k = 1 to a of t^k/k, and P_a(t) = sum from k = 0 to a "
                + "of (a-k)t^k. Let D_a(t) = Q_a(t) - log S_a(t), and K_a(t) = t^a P_a(t)/S_a(t). "
                + "Interval integrability below is with respect to real Lebesgue measure.")),
            Describe.Lean(
                DescribeId.Create("finite-geometric-prefix-identity"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/PrefixDeficitKernel.geometric_prefix_mul"),
                H("Finite geometric identity"),
                StatementSource.FromAuthor(PrefixIdentity()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplying the finite prefix by one minus the "
                    + "ratio cancels its adjacent terms and leaves one minus the first "
                    + "omitted power. This identity holds for every real ratio."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-geometric-prefix-unit-bound"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/PrefixDeficitKernel.geometric_prefix_one_le"),
                H("Initial unit term"),
                StatementSource.FromAuthor(PrefixLower()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a nonnegative ratio every power is "
                    + "nonnegative, and the exponent-zero term equals one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prefix-deficit-integral-reserve"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/PrefixDeficitKernel.result"),
                H("Exact integral and uniform reserve"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The exponent is arbitrary and at least one; the real ratio is "
                        + "strictly between zero and one. The triangular recurrence P_(a+1) = P_a + S_a "
                        + "gives (1-t)P_a(t) = a+1-S_a(t). Differentiating the finite geometric identity "
                        + "and subtracting the logarithmic derivative gives D'_a(t) = K_a(t). "
                        + "The geometric normalization is positive on the entire integration interval, "
                        + "so the continuous kernel is integrable and the fundamental theorem of calculus "
                        + "gives the exact integral.")),
                    Paragraph(Text("The inequality a S_a(t) <= (1+t)P_a(t) follows by induction: "
                        + "the increment is t S_a(t) - (a+1)t^(a+1), a sum of nonnegative power "
                        + "differences for 0 <= t <= 1. Termwise comparison also gives P_a(t) <= a S_a(t). "
                        + "Using the constant lower denominator 1+z on the interval and integrating t^a gives the bounds. "
                        + "The lower bound implies a z^(a+1)/(2(a+1)) <= D_a(z).")),
                    Paragraph(Text("For 0 <= t <= 1, the factor P_a(t)/S_a(t) is the "
                        + "mean remaining exponent in the truncated geometric weights t^k/S_a(t). "
                        + "At a prime ratio z = 1/p, D_a(z) is the finite prefix deficit, "
                        + "distinct from the optimizer reserve R_p(x). Its upper bound does not bound "
                        + "R_p(x) unless the additional optimizer gap is separately controlled. "
                        + "Only a finite local deficit is estimated. No signed-tail cancellation, "
                        + "Taylor coefficient positivity, Weil quadratic-form positivity, Robin "
                        + "inequality, or Riemann hypothesis follows from this statement."))),
                DescribeRole.Theorem))));

    private static Formula PrefixIdentity()
    {
        Formula b = F.Id("b");
        Formula t = F.Id("t");
        Formula prefix = new Formula.Apply(Seq(F.Id("S"), Underscore, Grp(b)), [t]);
        return Disp(Seq(Forall, Sp, b, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, t, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Open, D(1), Minus, t, Close, prefix, Sp, Eq, Sp,
            D(1), Minus, new Formula.Power(t, Seq(b, Plus, D(1)))));
    }

    private static Formula PrefixLower()
    {
        Formula b = F.Id("b");
        Formula t = F.Id("t");
        Formula prefix = new Formula.Apply(Seq(F.Id("S"), Underscore, Grp(b)), [t]);
        return Disp(Seq(Forall, Sp, b, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, t, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(0), Sp, Le, Sp, t, Sp, Rightarrow, Sp, D(1), Sp, Le, Sp, prefix));
    }

    private static Formula Statement()
    {
        Formula a = F.Id("a");
        Formula z = F.Id("z");
        Formula t = F.Id("t");
        Formula deficit = new Formula.Apply(Seq(F.Id("D"), Underscore, a), [z]);
        Formula kernel = new Formula.Fraction(
            Seq(new Formula.Power(t, a), Sp,
                new Formula.Apply(Seq(F.Id("P"), Underscore, a), [t])),
            new Formula.Apply(Seq(F.Id("S"), Underscore, a), [t]));
        Formula numerator = Seq(a, Sp, new Formula.Power(z, Seq(a, Plus, D(1))));
        Formula lower = new Formula.Fraction(numerator,
            Seq(Open, a, Plus, D(1), Close, Open, D(1), Plus, z, Close));
        Formula upper = new Formula.Fraction(numerator, Seq(a, Plus, D(1)));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, a, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                Sp, z, Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma),
            Seq(D(1), Sp, Le, Sp, a, Sp, Land, Sp, D(0), Sp, Lt, Sp, z,
                Sp, Land, Sp, z, Sp, Lt, Sp, D(1), Sp, Rightarrow),
            Seq(new Formula.Apply(F.Id("IntervalIntegrable"),
                [Seq(F.Id("K"), Underscore, a), D(0), z]), Sp, Land),
            Seq(deficit, Sp, Eq, Sp, Int, Underscore, Grp(D(0)), Caret, Grp(z),
                Sp, kernel, Sp, F.Id("dt"), Sp, Land),
            Seq(lower, Sp, Le, Sp, deficit, Sp, Le, Sp, upper)
        ]));
    }
}
