using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class LonelyRunnerFourteenOfTwentyDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S1/Phase/LonelyRunnerFourteenOfTwenty.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflected finite certificate supplies a rational lonely time for every fourteen speeds chosen from one through twenty.",
        H("Lonely Runner: Fourteen of Twenty"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("torus-distance-rational-time-residue-window"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "torusDist_nat_ratio_ge_iff_nat_residue_window"),
                H("Rational torus distance is an exact residue window"),
                StatementSource.FromAuthor(ResidueWindowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural s, a, and positive d, Mathlib's fractional-part division "
                            + "identity rewrites the torus distance at time a/d as the residue "
                            + "of sa modulo d divided by d. Clearing the positive denominator "
                            + "gives the two natural-number window inequalities exactly.")),
                    Paragraph(Text(
                        "This equivalence is the arithmetic bridge used by every reflected mask "
                            + "computation below; it is not a restatement of the final existence claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fifteen-mask-certificate-package"),
                DeclarationHandle.Create(DeclarationPrefix + "certificate_package"),
                H("Fifteen masks cover every fourteen-speed selection"),
                StatementSource.FromAuthor(CertificatePackageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first fifteen conjuncts are the exact safe masks at the listed "
                            + "rational times. Each equality is checked by kernel reduction after "
                            + "transport through the residue-window theorem.")),
                    Paragraph(Text(
                        "The next conjunct exhausts the seven six-element subsets of the residual "
                            + "seven-speed set. The last conjunct lifts those computations by a "
                            + "complement argument to every fourteen-element subset of the full "
                            + "twenty-speed universe."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lonely-runner-fourteen-of-twenty"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "lonely_runner_fourteen_of_twenty"),
                H("Every fourteen of the twenty speeds have a rational lonely time"),
                StatementSource.FromAuthor(LonelyRunnerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every fourteen-element subset S of speeds one through twenty, the "
                            + "finite certificate supplies a rational time in the unit interval "
                            + "whose exact safe mask contains S. Membership in that mask gives "
                            + "torus distance at least 1/15 for every selected speed.")),
                    Paragraph(Text(
                        "The theorem covers all 38,760 such subsets through the structured "
                            + "complement proof; it does not rely on the impractical direct "
                            + "powerset reduction and does not assert the unrestricted Lonely "
                            + "Runner conjecture."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula RationalNumbers() =>
        Seq(Mathbb, Grp(F.Id("Q")));

    private static Formula Ratio(int numerator, int denominator) =>
        Seq(Frac, Grp(Number(numerator)), Grp(Number(denominator)));

    private static Formula Number(int value) => value switch
    {
        1 => D(1),
        2 => D(2),
        3 => D(3),
        4 => D(4),
        5 => D(5),
        6 => D(6),
        7 => D(7),
        8 => D(8),
        9 => D(9),
        10 => D(1, 0),
        11 => D(1, 1),
        12 => D(1, 2),
        13 => D(1, 3),
        14 => D(1, 4),
        15 => D(1, 5),
        18 => D(1, 8),
        20 => D(2, 0),
        22 => D(2, 2),
        23 => D(2, 3),
        25 => D(2, 5),
        26 => D(2, 6),
        29 => D(2, 9),
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    private static Formula FinsetOf(Formula carrier) =>
        Call("Finset", carrier);

    private static Formula SetLiteral(params int[] values)
    {
        var items = new List<Formula> { OpenBrace };
        for (var index = 0; index < values.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(Number(values[index]));
        }
        items.Add(CloseBrace);
        return Seq([.. items]);
    }

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Residue(Formula value, Formula modulus) =>
        Seq(Open, value, Sp, Operatorname, Grp(F.Id("mod")), Sp, modulus, Close);

    private static Formula ResidueWindowFormula()
    {
        Formula s = F.Id("s");
        Formula a = F.Id("a");
        Formula d = F.Id("d");
        Formula product = Product(s, a);
        Formula residue = Residue(product, d);
        Formula time = RatioExpression(a, d);
        Formula distance = Call("torusDist", Product(s, time));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, s, Comma, Sp, a, Comma, Sp, d, Sp, InMacro, Sp,
                NaturalNumbers(), Comma, Sp, D(0), Sp, Lt, Sp, d, Sp,
                Rightarrow, Sp),
            Seq(
                Ratio(1, 15), Sp, Leq, Sp, distance, Sp, Iff, Sp),
            Seq(
                d, Sp, Leq, Sp, Product(D(1, 5), residue), Sp, Land, Sp,
                Product(D(1, 5), residue), Sp, Leq, Sp, Product(D(1, 4), d), Dot),
        ]));
    }

    private static Formula RatioExpression(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Removed(Formula universe, params int[] values) =>
        Seq(universe, Sp, Setminus, Sp, SetLiteral(values));

    private static Formula MaskEquality(
        Formula universe,
        int numerator,
        int denominator,
        params int[] removed) =>
        Seq(
            Call("safeMask", Ratio(numerator, denominator)), Sp, Eq, Sp,
            Removed(universe, removed));

    private static Formula CertificatePackageFormula()
    {
        Formula universe = F.Id("speedUniverse");
        Formula residual = F.Id("residualSpeeds");
        Formula covered = F.Id("residualCoveredSixSubsets");
        Formula selected = F.Id("S");
        Formula time = F.Id("t");
        Formula mask = F.Id("M");
        Formula pair = Seq(Open, time, Comma, Sp, mask, Close);
        Formula packageConclusion = Seq(
            Forall, Sp, selected, Colon, Sp, FinsetOf(NaturalNumbers()), Comma, Sp,
            Open, selected, Sp, Subseteq, Sp, universe, Sp, Land, Sp,
            Lvert, Sp, selected, Sp, Rvert, Sp, Eq, Sp, D(1, 4), Close, Sp,
            Rightarrow, Sp, Exists, Sp, pair, Sp, InMacro, Sp, F.Id("certificate"),
            Comma, Sp, selected, Sp, Subseteq, Sp, mask, Dot);

        return Disp(new Formula.Aligned([
            Seq(MaskEquality(universe, 1, 11, 11), Sp, Land),
            Seq(MaskEquality(universe, 1, 12, 12), Sp, Land),
            Seq(MaskEquality(universe, 1, 13, 13), Sp, Land),
            Seq(MaskEquality(universe, 1, 14, 14), Sp, Land),
            Seq(MaskEquality(universe, 1, 15, 15), Sp, Land),
            Seq(MaskEquality(universe, 1, 22, 1), Sp, Land),
            Seq(MaskEquality(universe, 11, 23, 2), Sp, Land),
            Seq(MaskEquality(universe, 6, 25, 4), Sp, Land),
            Seq(MaskEquality(universe, 8, 25, 3), Sp, Land),
            Seq(MaskEquality(universe, 5, 26, 5), Sp, Land),
            Seq(MaskEquality(universe, 4, 29, 7), Sp, Land),
            Seq(MaskEquality(universe, 5, 29, 6), Sp, Land),
            Seq(MaskEquality(universe, 11, 29, 8), Sp, Land),
            Seq(MaskEquality(universe, 1, 9, 9, 18), Sp, Land),
            Seq(MaskEquality(universe, 1, 10, 10, 20), Sp, Land),
            Seq(
                Call("powersetCard", D(6), residual), Sp, Subseteq, Sp,
                covered, Sp, Land),
            packageConclusion,
        ]));
    }

    private static Formula LonelyRunnerFormula()
    {
        Formula universe = F.Id("speedUniverse");
        Formula selected = F.Id("S");
        Formula time = F.Id("t");
        Formula speed = F.Id("s");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, selected, Colon, Sp, FinsetOf(NaturalNumbers()), Comma, Sp,
                Open, selected, Sp, Subseteq, Sp, universe, Sp, Land, Sp,
                Lvert, Sp, selected, Sp, Rvert, Sp, Eq, Sp, D(1, 4), Close, Sp,
                Rightarrow, Sp),
            Seq(
                Exists, Sp, time, Sp, InMacro, Sp, RationalNumbers(), Comma, Sp,
                D(0), Sp, Leq, Sp, time, Sp, Leq, Sp, D(1), Comma, Sp),
            Seq(
                Forall, Sp, speed, Sp, InMacro, Sp, selected, Comma, Sp,
                Ratio(1, 15), Sp, Leq, Sp,
                Call("torusDist", Product(speed, time)), Dot),
        ]));
    }
}
