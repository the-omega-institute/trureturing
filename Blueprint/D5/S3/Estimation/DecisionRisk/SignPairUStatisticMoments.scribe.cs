using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class SignPairUStatisticMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent signs with common mean have explicit first and second moments for their "
            + "normalized pair statistic.",
        H("Moments of the sign pair U-statistic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sign-pair-product-weight"),
                DeclarationHandle.Create(Prefix + "signPairWeight"),
                H("Product weight of a sign vector"),
                StatementSource.FromAuthor(WeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each coordinate assigns masses (1 + mu eta_i) / 2 to its two signs. The "
                        + "weight of a sign vector is the product of these coordinate masses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sign-pair-u-statistic"),
                DeclarationHandle.Create(Prefix + "signPairUStatistic"),
                H("Normalized second-order sign statistic"),
                StatementSource.FromAuthor(StatisticFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The statistic subtracts the diagonal contribution from the square of the "
                        + "sign sum and normalizes by the number of ordered distinct pairs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sign-pair-u-statistic-moments"),
                DeclarationHandle.Create(Prefix + "sign_pair_u_statistic_moments"),
                H("Pair representation, mean, and variance"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Expanding the square identifies the statistic with the average product "
                            + "over unordered coordinate pairs. Product factorization gives the "
                            + "expectation of every sign character as mu raised to the number of "
                            + "coordinates in that character.")),
                    Paragraph(Text(
                        "For the second moment, equal pairs contribute the squared centered second "
                            + "moment. Pairs sharing one coordinate and disjoint pairs vanish after "
                            + "centering. Counting the surviving pairs and simplifying yields the "
                            + "stated variance."))),
                DescribeRole.Theorem))));

    private static Formula WeightFormula()
    {
        Formula k = F.Id("k"), mu = F.Id("mu"), eta = F.Id("eta"), i = F.Id("i");
        Formula sign = At(eta, i);

        return Disp(Seq(
            Forall, Sp, Typed(k, Nat()), Comma, Sp,
            Typed(mu, Real()), Comma, Sp,
            Typed(eta, SignVector(k)), Comma, RowBreak, Grp(),
            Call("signPairWeight", mu, eta), Sp, Eq, Sp,
            Product(Seq(i, Sp, InMacro, Sp, Call("Fin", k)),
                Fraction(Seq(D(1), Plus, mu, Sp, sign), D(2))), Dot));
    }

    private static Formula StatisticFormula()
    {
        Formula k = F.Id("k"), eta = F.Id("eta"), i = F.Id("i");
        Formula signSum = Summation(Seq(i, Sp, InMacro, Sp, Call("Fin", k)), At(eta, i));

        return Disp(Seq(
            Forall, Sp, Typed(k, Nat()), Comma, Sp,
            Typed(eta, SignVector(k)), Comma, RowBreak, Grp(),
            Call("signPairUStatistic", eta), Sp, Eq, Sp,
            Fraction(
                Seq(Power(Grp(signSum), D(2)), Minus, k),
                Seq(k, Open, k, Minus, D(1), Close)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula k = F.Id("k"), mu = F.Id("mu"), eta = F.Id("eta");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula uEta = Call("signPairUStatistic", eta);
        Formula weightEta = Call("signPairWeight", mu, eta);
        Formula allSigns = SignVector(k);
        Formula pairAverage = Fraction(
            Summation(
                Seq(i, Lt, j, Comma, Sp, i, Comma, j, Sp, InMacro, Sp, Call("Fin", k)),
                Seq(At(eta, i), At(eta, j))),
            Call("choose", k, D(2)));
        Formula mean = Summation(
            Seq(eta, Sp, InMacro, Sp, allSigns),
            Seq(weightEta, Sp, uEta));
        Formula secondMoment = Summation(
            Seq(eta, Sp, InMacro, Sp, allSigns),
            Seq(weightEta, Sp, Power(uEta, D(2))));
        Formula variance = Seq(secondMoment, Minus, Power(Grp(mean), D(2)));
        Formula varianceValue = Seq(
            Fraction(
                Seq(D(4), mu, Caret, Grp(D(2)), Open, D(1), Minus,
                    mu, Caret, Grp(D(2)), Close),
                k),
            Plus,
            Fraction(
                Seq(D(2), Power(Grp(Seq(D(1), Minus, mu, Caret, Grp(D(2)))), D(2))),
                Seq(k, Open, k, Minus, D(1), Close)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(k, Nat()), Comma, Sp, Typed(mu, Real()), Comma, RowBreak, Grp(),
            D(2), Leq, Sp, k, Comma, Sp,
            Minus, D(1), Leq, Sp, mu, Comma, Sp, mu, Leq, Sp, D(1), Sp,
            Rightarrow, RowBreak, Grp(),
            Open, Forall, Sp, Typed(eta, allSigns), Comma, Sp,
            uEta, Sp, Eq, Sp, pairAverage, Close,
            Sp, Land, RowBreak, Grp(),
            mean, Sp, Eq, Sp, Power(mu, D(2)),
            Sp, Land, RowBreak, Grp(),
            variance, Sp, Eq, Sp, varianceValue, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula SignVector(Formula k) =>
        Seq(Open, Call("Fin", k), Sp, To, Sp, Call("Units", Seq(Mathbb, Grp(F.Id("Z")))), Close);

    private static Formula Product(Formula index, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Grp(index)), Sp, Grp(body));

    private static Formula Summation(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, Grp(index)), Sp, Grp(body));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));
}
