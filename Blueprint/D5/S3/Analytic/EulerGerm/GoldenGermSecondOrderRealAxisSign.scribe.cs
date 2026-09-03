using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermSecondOrderRealAxisSignDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderRealAxisSign."
            + "golden_germ_second_order_real_axis_negative";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit second-order golden germ continuation is real and strictly "
            + "negative between the structural and golden boundaries.",
        H("Golden Germ Second-Order Real-Axis Sign"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-second-order-real-axis-negative"),
            DeclarationHandle.Create(Declaration),
            H("The second-order continuation is negative between its two boundaries"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This is the next real-axis sign step in the golden Euler germ "
                        + "extraction ladder of OACTC parts 580 and 581. It advances the "
                        + "open interval between one over phi cubed and one over phi "
                        + "squared by determining the sign of the explicit second-order "
                        + "continuation throughout that interval.")),
                Paragraph(Text(
                    "Every real second-normalized Euler factor is strictly positive: "
                        + "the cubed mode lies below one, the inverse squared-mode factor "
                        + "is positive, and the local germ series is a convergent sum of "
                        + "positive terms. Frozen deviation summability carries this "
                        + "positivity through the multipliable infinite product.")),
                Paragraph(Text(
                    "For the remaining factors, the paired Dirichlet eta series proves "
                        + "that zeta is negative on the real interval from zero to one. "
                        + "The cubed and doubled-squared zeta arguments exceed one and "
                        + "therefore contribute positive real factors.")),
                Paragraph(Text(
                    "The theorem is confined to the strict real interval and to the "
                        + "displayed second-order continuation. It does not establish "
                        + "O-5 or RH, a complex zero-free region, or any all-order "
                        + "extraction statement."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermSecondNormalizedFactorRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermRealAxisPositivity")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula sigma = F.Id("sigma");
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula lower = Fraction(F.D(1), phiCubed);
        Formula upper = Fraction(F.D(1), phiSquared);
        Formula normalized = NormalizedFactor(s, p, phiSquared, phiCubed);
        Formula hAtS = Call("H", s);
        Formula fAtS = Call("F2", s);
        Formula hDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, hAtS, F.Sp, F.Colon, F.Eq, F.Sp,
            PrimeProduct(normalized));
        Formula zetaSquared = Call(
            "riemannZeta",
            F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s));
        Formula zetaCubed = Call(
            "riemannZeta",
            F.Seq(phiCubed, F.Sp, F.Times, F.Sp, s));
        Formula zetaDoubleSquared = Call(
            "riemannZeta",
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
                F.Sp, F.Times, F.Sp, s));
        Formula fDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, fAtS, F.Sp, F.Colon, F.Eq, F.Sp,
            zetaSquared, F.Sp, F.Times, F.Sp,
            zetaCubed, F.Sp, F.Times, F.Sp,
            Power(
                F.Seq(F.Open, zetaDoubleSquared, F.Close),
                F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, hAtS);
        Formula interval = F.Seq(
            lower, F.Sp, F.Lt, F.Sp, sigma,
            F.Sp, F.Lt, F.Sp, upper);
        Formula conclusion = And(
            Equal(ImaginaryPart(Call("F2", sigma)), F.D(0)),
            LessThan(RealPart(Call("F2", sigma)), F.D(0)));
        Formula sign = F.Seq(
            F.Forall, F.Sp, sigma, F.InMacro, F.Sp, RealNumbers(),
            F.Comma, F.Sp, interval, F.Sp, F.Rightarrow, F.Sp, conclusion);

        return F.Disp(new Formula.Aligned([
            F.Seq(hDefinition, F.Comma),
            F.Seq(fDefinition, F.Comma),
            F.Seq(sign, F.Dot),
        ]));
    }

    private static Formula NormalizedFactor(
        Formula s,
        Formula p,
        Formula phiSquared,
        Formula phiCubed)
    {
        Formula cubedMode = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed));
        Formula squaredMode = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared));
        Formula inverse = Power(
            F.Seq(
                F.Open, F.D(1), F.Sp, F.Plus, F.Sp,
                squaredMode, F.Close),
            F.Seq(F.Minus, F.D(1)));

        return F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, cubedMode, F.Close,
            F.Sp, F.Times, F.Sp, inverse,
            F.Sp, F.Times, F.Sp, LocalFactor(s, p));
    }

    private static Formula LocalFactor(Formula s, Formula p) =>
        F.Seq(
            F.Sum, F.Underscore,
            F.Grp(F.Id("v"), F.InMacro, F.Sp, NaturalNumbers()),
            Power(p, F.Seq(
                F.Minus, s, F.Sp, F.Times, F.Sp,
                Call("o5Beta", F.Id("v")))));

    private static Formula PrimeProduct(Formula body) =>
        F.Seq(
            F.Prod, F.Underscore,
            F.Grp(F.Id("p"), F.InMacro, F.Sp, Call("Primes", NaturalNumbers())),
            body);

    private static Formula RealPart(Formula value) =>
        F.Seq(F.Re, F.Open, value, F.Close);

    private static Formula ImaginaryPart(Formula value) =>
        Call("Im", value);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula RealNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
