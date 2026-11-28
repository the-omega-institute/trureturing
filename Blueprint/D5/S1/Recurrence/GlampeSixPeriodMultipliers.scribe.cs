using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GlampeSixPeriodMultipliersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/GlampeSixPeriodMultipliers.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/glampe2026polynomial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For integer scales of absolute value at least two, a scaled six-period recurrence admits fixed-sign polynomial identities over any characteristic-zero field exactly for positive multipliers congruent to one modulo six.",
        H("Polynomial Multipliers of a Scaled Six-Period Recurrence"),
        Blocks(
            Paragraph(Text("The source's equation (10) asks which multipliers admit a polynomial "
                + "identity with an optional parity sign on each coefficient. The family considered "
                + "here has G(0)=1, G(1)=0 and (r,s)=(t,-t²) in equation (9). "
                + "The general classification for equation (9) remains open in this development.")),
            Describe.Lean(DescribeId.Create("glampe-scaled-six-period-sequence"),
                DeclarationHandle.Create(Prefix + "scaledGibonacci"),
                H("The scaled sequence"),
                StatementSource.FromAuthor(Disp(Recurrence())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every integer scale t, write G(t,n) for scaledGibonacci t n, "
                    + "the integer sequence with seeds "
                    + "1 and 0. The solution of the order-two recurrence is G(n)=t^n h(n), "
                    + "where h repeats (1,0,-1,-1,0,1). The table has the same seeds and satisfies "
                    + "h(n+2)=h(n+1)-h(n), which gives the formula by recurrence uniqueness."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("glampe-six-period-multipliers"),
                DeclarationHandle.Create(Prefix + "multipliers_iff"),
                H("Classification with a fixed sign bit per degree"),
                StatementSource.FromAuthor(Disp(Classification())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Fix any characteristic-zero field K, an integer t with "
                        + "absolute value at least two, and a positive natural multiplier k. "
                        + "IntCast_K is the canonical integer-to-K cast, and the sign base -1 "
                        + "is an element of K. Each bit is zero for the false Boolean mask value "
                        + "and one for true. The coefficients and bits are fixed for all natural "
                        + "indices, including zero, and the bound k includes every smaller degree.")),
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
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("glampe-2026-six-period-multipliers"),
                    ResolutionKind.Proved)))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula G(Formula index) => Sub(F.Id("G"), Seq(F.Id("t"), Comma, index));
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula CastTo(Formula value, Formula field) =>
        new Formula.Apply(Sub(Seq(Operatorname, Grp(F.Id("IntCast"))), field), [value]);

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
        var fieldHypothesis = new Formula.Apply(Seq(Operatorname, Grp(F.Id("Field"))), [field]);
        var charZeroHypothesis = new Formula.Apply(Seq(Operatorname, Grp(F.Id("CharZero"))), [field]);
        var signBase = Par(Seq(Minus, D(1), Colon, Sp, field));
        var signedSum = Seq(Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(k), Sp,
            Sub(c, i), Pow(signBase, Seq(n, Sub(Varepsilon, i))), Pow(CastTo(G(n), field), i));
        var identity = Seq(Exists, Sp, c, Colon, Sp, indices, Sp, To, Sp, field, Comma, Sp,
            Exists, Sp, Varepsilon, Colon, Sp, indices, Sp, To, Sp, bits, Comma, Sp,
            Forall, Sp, n, InMacro, Naturals, Comma, Sp, CastTo(G(Seq(k, n)), field), Eq, signedSum);
        return Seq(Forall, Sp, field, Colon, Sp, F.Id("Type"), Star, Comma, Sp,
            OpenBracket, fieldHypothesis, CloseBracket, Sp,
            OpenBracket, charZeroHypothesis, CloseBracket, Comma, Sp,
            Forall, Sp, t, InMacro, Integers, Comma, Sp, Forall, Sp, k, InMacro, Naturals,
            Comma, Sp, Par(Seq(D(2), Sp, Leq, Sp, Lvert, Sp, t, Rvert, Sp, Land, Sp, k, Gt, D(0))),
            Sp, Rightarrow, Sp,
            Par(Seq(Par(identity), Sp, Iff, Sp, k, Equiv, D(1), Pmod, Grp(D(6)))));
    }
}
