using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GlampeSixPeriodMultipliersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GlampeSixPeriodMultipliers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scaled six-period recurrence has literal sign-restricted identities exactly for multipliers congruent to one modulo six.",
        H("Polynomial Multipliers of a Scaled Six-Period Recurrence"),
        Blocks(
            Paragraph(Text("Equation (10) of Glampe, Joshi, Malla, Richey and Wright, "
                + "arXiv:2610.15131v1, asks which multipliers admit a polynomial identity "
                + "with an optional index-dependent sign on each coefficient.")),
            Describe.Lean(DescribeId.Create("glampe-scaled-six-period-sequence"),
                DeclarationHandle.Create(Prefix + "scaledGibonacci"),
                H("The scaled sequence"),
                StatementSource.FromAuthor(Disp(Recurrence())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer scale t, the integer sequence G has seeds "
                    + "1 and 0. The solution of the order-two recurrence is G(n)=t^n h(n), "
                    + "where h repeats (1,0,-1,-1,0,1). The table has the same seeds and satisfies "
                    + "h(n+2)=h(n+1)-h(n), which gives the formula by recurrence uniqueness."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("glampe-six-period-multipliers"),
                DeclarationHandle.Create(Prefix + "multipliers_iff"),
                H("Classification with a fixed sign bit per degree"),
                StatementSource.FromAuthor(Disp(Classification())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix any characteristic-zero field K, an integer t with "
                        + "absolute value at least two, and a positive natural multiplier k. "
                        + "Each G value in the identity is cast from the integers into K. The "
                        + "coefficients and bits are fixed for all natural indices, including zero, "
                        + "and the bound k includes every smaller degree.")),
                    Paragraph(Text("At indices 1 and 7, the inputs are both zero and the two signs "
                        + "agree for each bit. The outputs must therefore agree. Since h(7k)=h(k) "
                        + "and the powers of t have distinct values at distinct exponents, h(k)=0. "
                        + "Only residues 1 and 4 modulo six give that value.")),
                    Paragraph(Text("Every sign factor is one at an even index. At indices 6j, the "
                        + "resulting even-index polynomial agrees with X^k at the infinitely many "
                        + "distinct points t^(6j), so it equals X^k. If k is congruent to four, "
                        + "then G(2k)=-t^(2k) while G(2)^k=t^(2k). The scale bound and characteristic "
                        + "zero make those values distinct.")),
                    Paragraph(Text("If k is congruent to one, then h(kn)=h(n) and k is odd. "
                        + "Each entry of the period is fixed by raising it to the kth power, "
                        + "so G(kn)=G(n)^k. Take the coefficient of degree k to be one, "
                        + "every other coefficient to be zero, and every sign bit to be zero."))),
                DescribeRole.Theorem))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula G(Formula index) => Sub(F.Id("G"), index);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);

    private static Formula Recurrence()
    {
        var n = F.Id("n");
        var t = F.Id("t");
        return Seq(Forall, Sp, t, Sp, InMacro, Sp, Integers, Comma, Sp,
            G(D(0)), Eq, D(1), Comma, Sp, G(D(1)), Eq, D(0), Comma, Sp,
            Forall, Sp, n, Sp, InMacro, Sp, Naturals, Comma, Sp,
            G(Seq(n, Plus, D(2))), Eq, t, G(Seq(n, Plus, D(1))), Minus, Pow(t, D(2)), G(n));
    }

    private static Formula Classification()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var i = F.Id("i");
        var t = F.Id("t");
        var c = F.Id("c");
        var field = F.Id("K");
        var bits = Seq(OpenBrace, D(0), Comma, D(1), CloseBrace);
        var indices = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Fin"))), [Seq(k, Plus, D(1))]);
        var signedSum = Seq(Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(k), Sp,
            Sub(c, i), Pow(Par(Seq(Minus, D(1))), Seq(n, Sub(Varepsilon, i))), Pow(G(n), i));
        var identity = Seq(Exists, Sp, c, InMacro, Pow(field, Seq(k, Plus, D(1))), Comma, Sp,
            Exists, Sp, Varepsilon, Colon, Sp, indices, Sp, To, Sp, bits, Comma, Sp,
            Forall, Sp, n, InMacro, Naturals, Comma, Sp, G(Seq(k, n)), Eq, signedSum);
        return Seq(Forall, Sp, t, InMacro, Integers, Comma, Sp, Forall, Sp, k, InMacro, Naturals,
            Comma, Sp, Par(Seq(D(2), Leq, Lvert, t, Rvert, Land, k, Gt, D(0))), Sp, Rightarrow, Sp,
            Par(Seq(Par(identity), Sp, Iff, Sp, k, Equiv, D(1), Pmod, Grp(D(6)))));
    }
}
