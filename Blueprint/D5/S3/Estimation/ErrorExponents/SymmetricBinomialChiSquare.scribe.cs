using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class SymmetricBinomialChiSquareDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ErrorExponents/SymmetricBinomialChiSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric binomial mixture has an exact even-power chi-square defect, a hyperbolic-cosine envelope, and a root-fidelity bound.",
        H("Symmetric Binomial Chi-Square Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-binomial-mixture-law"),
                DeclarationHandle.Create(Prefix + "p_z"),
                H("Symmetric binomial mixture"),
                StatementSource.FromAuthor(PzFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The law averages the binomial mass with success parameters (1+z)/2 and (1-z)/2. "
                        + "Exchanging the two parameters leaves the mixture unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("central-binomial-reference-law"),
                DeclarationHandle.Create(Prefix + "p_0"),
                H("Central binomial reference law"),
                StatementSource.FromAuthor(PzeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reference law is the binomial distribution with success probability one half."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-chi-square-defect"),
                DeclarationHandle.Create(Prefix + "chiSquare"),
                H("Finite chi-square defect"),
                StatementSource.FromAuthor(ChiSquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The chi-square defect is the second likelihood-ratio moment under the central law, minus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-symmetric-binomial-chi-square-defect"),
                DeclarationHandle.Create(Prefix + "symmetric_binomial_chi_square"),
                H("Exact symmetric-binomial chi-square defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For absolute bias at most one, the symmetric mixture is nonnegative and normalized. "
                            + "Its likelihood ratio has the closed symmetric sign-product form. Its chi-square "
                            + "defect is both the average of two binomial powers minus one and the finite sum "
                            + "of its positive even terms.")),
                    Paragraph(Text(
                        "The even terms are bounded by the corresponding hyperbolic-cosine series. For the "
                            + "quadratic parameterization z squared equals 2 delta minus delta squared, the "
                            + "small-argument series comparison gives a quadratic defect bound.")),
                    Paragraph(Text(
                        "In the strict interior, every mixture mass and the Bhattacharyya affinity are positive. "
                            + "The squared affinity loss is no larger than the chi-square defect, by comparing "
                            + "the squared root likelihood-ratio gap with the squared likelihood-ratio gap."))),
                DescribeRole.Theorem))));

    private static Formula Fn(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Pow(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula Mul(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Abs(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert, Sp);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Range(Formula block) =>
        Fn("range", Seq(block, Sp, Plus, Sp, D(1)));

    private static Formula Fin(Formula size) => Fn("Fin", size);

    private static Formula Lambda(Formula binder, Formula domain, Formula body) =>
        Seq(Open, binder, Colon, Sp, domain, Close, Sp, Mapsto, Sp, body);

    private static Formula FiniteSum(Formula index, Formula block, Formula summand) =>
        Seq(Sum, Sp, Underscore,
            Grp(index, Sp, InMacro, Sp, Range(block)), Sp, summand);

    private static Formula Pz(Formula block, Formula bias, Formula index) =>
        Seq(Grp(F.Id("p"), Underscore, Grp(F.Id("z"))),
            Open, block, Comma, Sp, bias, Comma, Sp, index, Close);

    private static Formula Pzero(Formula block, Formula index) =>
        Seq(Grp(F.Id("p"), Underscore, Grp(D(0))),
            Open, block, Comma, Sp, index, Close);

    private static Formula Chi(Formula block, Formula bias) =>
        Fn("chiSquare", block, bias);

    private static Formula Choose(Formula block, Formula index) =>
        Fn("choose", block, index);

    private static Formula Affinity(Formula block, Formula bias, Formula index)
    {
        Formula domain = Fin(Seq(block, Sp, Plus, Sp, D(1)));
        return Fn("bhattacharyya",
            Lambda(index, domain, Pzero(block, index)),
            Lambda(index, domain, Pz(block, bias, index)));
    }

    private static Formula PzRight(Formula block, Formula bias, Formula index)
    {
        Formula plusHalf = Div(Seq(D(1), Sp, Plus, Sp, bias), D(2));
        Formula minusHalf = Div(Seq(D(1), Sp, Minus, Sp, bias), D(2));
        Formula complement = Seq(block, Sp, Minus, Sp, index);
        Formula first = Mul(Pow(plusHalf, index), Pow(minusHalf, complement));
        Formula second = Mul(Pow(minusHalf, index), Pow(plusHalf, complement));
        return Mul(Mul(Div(D(1), D(2)), Choose(block, index)),
            Grp(first, Sp, Plus, Sp, second));
    }

    private static Formula PzFormula()
    {
        Formula block = F.Id("B"), bias = F.Id("z"), index = F.Id("k");
        return Disp(Seq(
            Forall, Sp, Typed(block, Naturals()), Comma, Sp,
            Typed(bias, Reals()), Comma, Sp, Typed(index, Naturals()), Comma, Sp,
            Pz(block, bias, index), Sp, Eq, Sp, PzRight(block, bias, index), Dot));
    }

    private static Formula PzeroFormula()
    {
        Formula block = F.Id("B"), index = F.Id("k");
        return Disp(Seq(
            Forall, Sp, Typed(block, Naturals()), Comma, Sp,
            Typed(index, Naturals()), Comma, Sp,
            Pzero(block, index), Sp, Eq, Sp,
            Div(Choose(block, index), Pow(D(2), block)), Dot));
    }

    private static Formula ChiSquareFormula()
    {
        Formula block = F.Id("B"), bias = F.Id("z"), index = F.Id("k");
        Formula summand = Div(Pow(Pz(block, bias, index), D(2)), Pzero(block, index));
        return Disp(Seq(
            Forall, Sp, Typed(block, Naturals()), Comma, Sp,
            Typed(bias, Reals()), Comma, Sp,
            Chi(block, bias), Sp, Eq, Sp,
            FiniteSum(index, block, summand), Sp, Minus, Sp, D(1), Dot));
    }

    private static Formula LikelihoodRight(Formula block, Formula bias, Formula index)
    {
        Formula complement = Seq(block, Sp, Minus, Sp, index);
        Formula first = Mul(
            Pow(Seq(D(1), Sp, Plus, Sp, bias), index),
            Pow(Seq(D(1), Sp, Minus, Sp, bias), complement));
        Formula second = Mul(
            Pow(Seq(D(1), Sp, Minus, Sp, bias), index),
            Pow(Seq(D(1), Sp, Plus, Sp, bias), complement));
        return Div(Seq(first, Sp, Plus, Sp, second), D(2));
    }

    private static Formula TheoremFormula()
    {
        Formula block = F.Id("B"), bias = F.Id("z"), index = F.Id("k");
        Formula evenIndex = F.Id("j"), delta = DeltaLower;
        Formula biasSquared = Pow(bias, D(2));
        Formula chi = Chi(block, bias);
        Formula closed = Seq(
            Div(Seq(
                Pow(Grp(D(1), Sp, Plus, Sp, biasSquared), block), Sp, Plus, Sp,
                Pow(Grp(D(1), Sp, Minus, Sp, biasSquared), block)), D(2)),
            Sp, Minus, Sp, D(1));
        Formula halfBlock = Div(block, D(2));
        Formula evenSum = Seq(
            Sum, Sp, Underscore,
            Grp(evenIndex, Sp, InMacro, Sp, Fn("Icc", D(1), halfBlock)), Sp,
            Mul(Choose(block, Mul(D(2), evenIndex)), Pow(bias, Mul(D(4), evenIndex))));
        Formula blockBiasSquared = Mul(block, biasSquared);
        Formula likelihoodRatio = Seq(
            Forall, Sp, Typed(index, Naturals()), Comma, Sp,
            index, Sp, Le, Sp, block, Sp, Rightarrow, Sp,
            Div(Pz(block, bias, index), Pzero(block, index)),
            Sp, Eq, Sp, LikelihoodRight(block, bias, index));
        Formula deltaPremises = Seq(
            D(0), Sp, Lt, Sp, delta, Sp, Land, Sp,
            delta, Sp, Le, Sp, Div(D(1), D(4)), Sp, Land, Sp,
            Mul(block, delta), Sp, Le, Sp, D(1), Sp, Land, Sp,
            biasSquared, Sp, Eq, Sp,
            Seq(Mul(D(2), delta), Sp, Minus, Sp, Pow(delta, D(2))));
        Formula deltaBound = Seq(
            Forall, Sp, Typed(delta, Reals()), Comma, Sp,
            Open, deltaPremises, Close, Sp, Rightarrow, Sp,
            chi, Sp, Le, Sp, Mul(D(3), Pow(Mul(block, delta), D(2))));
        Formula affinity = Affinity(block, bias, index);
        Formula strictPositive = Seq(
            Abs(bias), Lt, Sp, D(1), Sp, Rightarrow, Sp, Open,
            Open, Forall, Sp, index, Sp, InMacro, Sp, Range(block), Comma, Sp,
            D(0), Sp, Lt, Sp, Pz(block, bias, index), Close, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, affinity, Close);
        Formula fidelityBound = Seq(
            D(1), Sp, Minus, Sp, Pow(affinity, D(2)),
            Sp, Le, Sp, chi);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(block, Naturals()), Comma, Sp,
                Typed(bias, Reals()), Comma),
            Seq(Grp(), Abs(bias), Le, Sp, D(1), Sp, Rightarrow, Sp, OpenBracket),
            Seq(Grp(), Open, Forall, Sp, index, Sp, InMacro, Sp,
                Range(block), Comma, Sp,
                D(0), Sp, Le, Sp, Pz(block, bias, index), Close, Sp, Land, Sp),
            Seq(Grp(), FiniteSum(index, block, Pz(block, bias, index)),
                Sp, Eq, Sp, D(1), Sp, Land, Sp),
            Seq(Grp(), Open, likelihoodRatio, Close, Sp, Land, Sp),
            Seq(Grp(), chi, Sp, Eq, Sp, closed, Sp, Land, Sp),
            Seq(Grp(), chi, Sp, Eq, Sp, evenSum, Sp, Land, Sp),
            Seq(Grp(), chi, Sp, Le, Sp, Fn("cosh", blockBiasSquared),
                Sp, Minus, Sp, D(1), Sp, Land, Sp),
            Seq(Grp(), Open, deltaBound, Close, Sp, Land, Sp),
            Seq(Grp(), Open, strictPositive, Close, Sp, Land, Sp),
            Seq(Grp(), fidelityBound, CloseBracket, Dot)
        ]));
    }
}
