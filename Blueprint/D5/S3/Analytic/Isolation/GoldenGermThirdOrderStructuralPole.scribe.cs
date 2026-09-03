using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermThirdOrderStructuralPoleDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermThirdOrderStructuralPole."
            + "golden_germ_third_order_structural_pole";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The next third-order golden structural pole has an explicit positive residue.",
        H("Golden Germ Third-Order Structural Pole"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-order-structural-pole"),
            DeclarationHandle.Create(Declaration),
            H("The next structural residue is explicit and positive"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Set B equal to twice phi squared plus phi cubed and b equal "
                        + "to one over B. The frozen third-order factorization isolates "
                        + "zeta at B times s as the next pole factor. Its other four "
                        + "zeta factors together with G3 form the regular multiplier.")),
                Paragraph(Text(
                    "The identity B equals phi to the fourth plus phi squared gives "
                        + "B less than phi to the fifth, so b lies inside the domain "
                        + "where the frozen regularity theorem makes G3 analytic. The "
                        + "frozen real-axis theorem also makes G3 at b real and strictly "
                        + "positive.")),
                Paragraph(Text(
                    "At b the four regular zeta arguments are phi squared over B, phi "
                        + "cubed over B, twice phi squared over B, and twice phi cubed "
                        + "over B. Each lies strictly between zero and one. The frozen "
                        + "positive-real zeta sign theorem therefore makes every one of "
                        + "their zeta values real and negative. The two direct factors "
                        + "and two reciprocal factors contribute four negative signs, "
                        + "so the regular multiplier is real and positive.")),
                Paragraph(Text(
                    "Transporting the residue-one extension of Riemann zeta through "
                        + "multiplication by B yields the factor one over B. The "
                        + "punctured normal form used by the frozen first- and "
                        + "second-pole templates then proves meromorphy, exact order "
                        + "minus one, and convergence of the cancelled germ to the "
                        + "displayed residue R.")),
                Paragraph(Text(
                    "This node advances the golden Euler germ extraction ladder of "
                        + "OACTC parts 580 and 581 by closing the next local residue and "
                        + "sign boundary. It does not assert O-5, the Riemann hypothesis, "
                        + "any implication toward either statement, complex "
                        + "nonvanishing on a half-plane, or an all-order extraction."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRealPositivity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/RiemannZetaPositiveRealSign")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermStructuralSimplePole")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermSecondOrderStructuralResidue")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula kp = F.Id("Kp");
        Formula g = F.Id("G3");
        Formula scale = F.Id("B");
        Formula point = F.Id("b");
        Formula regular = F.Id("regular");
        Formula germ = F.Id("F3");
        Formula residue = F.Id("R");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula scaleValue = F.Seq(
            F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp, phiCubed);
        Formula pointValue = Fraction(F.D(1), scale);
        Formula xValue = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared));
        Formula yValue = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed));
        Formula local = LocalFactor(s, p);
        Formula normalized = NormalizedFactor(local, x, y);
        Formula kpDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
            F.Sp, p, F.InMacro, F.Sp, Call("Primes", NaturalNumbers()), F.Comma,
            F.Sp, x, F.Sp, F.Colon, F.Eq, F.Sp, xValue, F.Comma, F.Sp,
            y, F.Sp, F.Colon, F.Eq, F.Sp, yValue, F.Comma, F.Sp,
            Call("Kp", s, p), F.Sp, F.Colon, F.Eq, F.Sp, normalized);
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            Call("G3", s), F.Sp, F.Colon, F.Eq, F.Sp,
            PrimeProduct(Call("Kp", s, p)));
        Formula scaleDefinition = F.Seq(
            scale, F.Sp, F.Colon, F.Eq, F.Sp, scaleValue);
        Formula pointDefinition = F.Seq(
            point, F.Sp, F.Colon, F.Eq, F.Sp, pointValue);
        Formula regularAtS = RegularValue(s, phiSquared, phiCubed);
        Formula regularDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            Call("regular", s), F.Sp, F.Colon, F.Eq, F.Sp, regularAtS);
        Formula germDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(), F.Comma, F.Sp,
            Call("F3", s), F.Sp, F.Colon, F.Eq, F.Sp,
            Call("riemannZeta", F.Seq(scale, F.Sp, F.Times, F.Sp, s)),
            F.Sp, F.Times, F.Sp, Call("regular", s));
        Formula residueDefinition = F.Seq(
            residue, F.Sp, F.Colon, F.Eq, F.Sp,
            Fraction(Call("regular", point), scale));
        Formula meromorphic = Call("MeromorphicAt", germ, point);
        Formula simpleOrder = Equal(
            Call("meromorphicOrderAt", germ, point),
            F.Seq(F.Minus, F.D(1)));
        Formula cancelledGerm = F.Seq(
            F.Open, s, F.Sp, F.Minus, F.Sp, point, F.Close,
            F.Sp, F.Times, F.Sp, Call("F3", s));
        Formula residueLimit = Call(
            "Tendsto",
            F.Seq(F.Open, s, F.Colon, F.Sp, ComplexNumbers(), F.Close,
                F.Sp, F.Mapsto, F.Sp, cancelledGerm),
            PuncturedNhood(point),
            Call("nhds", residue));
        Formula residueReal = Equal(ImaginaryPart(residue), F.D(0));
        Formula residuePositive = LessThan(F.D(0), RealPart(residue));

        return F.Disp(new Formula.Aligned([
            F.Seq(kpDefinition, F.Comma),
            F.Seq(gDefinition, F.Comma),
            F.Seq(scaleDefinition, F.Comma, F.Sp, pointDefinition, F.Comma),
            F.Seq(regularDefinition, F.Comma),
            F.Seq(germDefinition, F.Comma, F.Sp, residueDefinition, F.Comma),
            F.Seq(meromorphic, F.Sp, F.Land),
            F.Seq(simpleOrder, F.Sp, F.Land),
            F.Seq(residueLimit, F.Sp, F.Land),
            F.Seq(residueReal, F.Sp, F.Land, F.Sp, residuePositive, F.Dot),
        ]));
    }

    private static Formula RegularValue(
        Formula s,
        Formula phiSquared,
        Formula phiCubed)
    {
        Formula squared = F.Seq(phiSquared, F.Sp, F.Times, F.Sp, s);
        Formula cubed = F.Seq(phiCubed, F.Sp, F.Times, F.Sp, s);
        Formula doubleSquared = F.Seq(
            F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Times, F.Sp, s);
        Formula doubleCubed = F.Seq(
            F.D(2), F.Sp, F.Times, F.Sp, phiCubed,
            F.Sp, F.Times, F.Sp, s);
        Formula inverseDoubleSquared = Power(
            F.Seq(F.Open, Call("riemannZeta", doubleSquared), F.Close),
            F.Seq(F.Minus, F.D(1)));
        Formula inverseDoubleCubed = Power(
            F.Seq(F.Open, Call("riemannZeta", doubleCubed), F.Close),
            F.Seq(F.Minus, F.D(1)));

        return F.Seq(
            Call("riemannZeta", squared), F.Sp, F.Times, F.Sp,
            Call("riemannZeta", cubed), F.Sp, F.Times, F.Sp,
            inverseDoubleSquared, F.Sp, F.Times, F.Sp,
            inverseDoubleCubed, F.Sp, F.Times, F.Sp, Call("G3", s));
    }

    private static Formula NormalizedFactor(
        Formula local,
        Formula x,
        Formula y)
    {
        Formula oneMinusYSquared = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(y, F.D(2)), F.Close);
        Formula oneMinusXSquaredY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(x, F.D(2)), F.Sp, F.Times, F.Sp, y, F.Close);
        Formula oneMinusY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp, y, F.Close);
        Formula onePlusX = F.Seq(
            F.Open, F.D(1), F.Sp, F.Plus, F.Sp, x, F.Close);

        return F.Seq(
            Power(oneMinusYSquared, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, oneMinusXSquaredY,
            F.Sp, F.Times, F.Sp, oneMinusY,
            F.Sp, F.Times, F.Sp,
            Power(onePlusX, F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp, local);
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

    private static Formula PuncturedNhood(Formula point) =>
        Call(
            "nhdsWithin",
            point,
            F.Seq(
                ComplexNumbers(), F.Sp, F.Setminus, F.Sp,
                F.OpenBrace, point, F.CloseBrace));

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

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

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
