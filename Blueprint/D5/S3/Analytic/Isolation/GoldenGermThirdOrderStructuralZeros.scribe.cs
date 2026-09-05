using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenGermThirdOrderStructuralZerosDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenGermThirdOrderStructuralZeros."
            + "golden_germ_third_order_structural_zeros";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two reciprocal zeta factors in the third-order golden germ create "
            + "genuine simple structural zeros.",
        H("Golden Germ Third-Order Structural Zeros"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-third-order-structural-zeros"),
            DeclarationHandle.Create(Declaration),
            H("Both third-order denominator factors create simple zeros"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem is the next local divisor step in the golden Euler "
                        + "germ extraction ladder of OACTC parts 580 and 581. It advances "
                        + "the third-order continuation by resolving the two structural "
                        + "points introduced by its reciprocal zeta factors.")),
                Paragraph(Text(
                    "At one over twice phi squared, the transported zeta arguments are "
                        + "one half, phi over two, phi, and one plus phi over two. At one "
                        + "over twice phi cubed, they are one over twice phi, one half, "
                        + "one over phi, and one over phi plus one half. The paired eta "
                        + "series supplies the positive-real nonvanishing facts below one.")),
                Paragraph(Text(
                    "The third normalized product is analytic and nonzero at both real "
                        + "points by the frozen regularity theorem. The golden auxiliary "
                        + "nonvanishing theorem handles the reciprocal factor at one over "
                        + "phi, while standard right-half-plane nonvanishing handles the "
                        + "transported arguments at least one.")),
                Paragraph(Text(
                    "The removable numerator riemannZeta1 rewrites each active reciprocal "
                        + "zeta factor as the first power of the local coordinate times an "
                        + "analytic nonzero multiplier. This proves meromorphy and exact "
                        + "order one, rather than relying on the totalized value at the pole.")),
                Paragraph(Text(
                    "STOPPING JUSTIFICATION: the conclusion concerns only these two local "
                        + "structural zeros of the displayed third-order continuation. It "
                        + "does not establish O-5, RH, a global zero classification, or an "
                        + "all-order extraction statement."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderFactorization")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Regularity/GoldenGermThirdNormalizedFactorRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/Isolation/GoldenGermStructuralSimplePole")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula x = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiSquared));
        Formula y = Power(p, F.Seq(
            F.Minus, s, F.Sp, F.Times, F.Sp, phiCubed));
        Formula kp = NormalizedFactor(s, p, x, y);
        Formula gAtS = Call("G3", s);
        Formula gDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, gAtS, F.Sp, F.Colon, F.Eq, F.Sp,
            PrimeProduct(kp));
        Formula fDefinition = F.Seq(
            F.Forall, F.Sp, s, F.InMacro, F.Sp, ComplexNumbers(),
            F.Comma, F.Sp, Call("F3", s), F.Sp, F.Colon, F.Eq, F.Sp,
            Factorization(s, phiSquared, phiCubed, gAtS));
        Formula z2 = Fraction(
            F.D(1),
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiSquared));
        Formula z3 = Fraction(
            F.D(1),
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiCubed));
        Formula z2Definition = F.Seq(
            F.Id("z2"), F.Sp, F.Colon, F.Eq, F.Sp, z2);
        Formula z3Definition = F.Seq(
            F.Id("z3"), F.Sp, F.Colon, F.Eq, F.Sp, z3);
        Formula f = F.Id("F3");
        Formula z2Id = F.Id("z2");
        Formula z3Id = F.Id("z3");
        Formula z2Order = F.Seq(
            Call("meromorphicOrderAt", f, z2Id),
            F.Sp, F.Eq, F.Sp, F.D(1));
        Formula z3Order = F.Seq(
            Call("meromorphicOrderAt", f, z3Id),
            F.Sp, F.Eq, F.Sp, F.D(1));
        Formula conclusion = F.Seq(
            Call("MeromorphicAt", f, z2Id), F.Sp, F.Land, F.Sp,
            z2Order, F.Sp, F.Land, F.Sp,
            Call("MeromorphicAt", f, z3Id), F.Sp, F.Land, F.Sp,
            z3Order);

        return F.Disp(new Formula.Aligned([
            F.Seq(gDefinition, F.Comma),
            F.Seq(fDefinition, F.Comma),
            F.Seq(z2Definition, F.Comma, F.Sp, z3Definition, F.Comma),
            F.Seq(conclusion, F.Dot),
        ]));
    }

    private static Formula Factorization(
        Formula s,
        Formula phiSquared,
        Formula phiCubed,
        Formula gAtS)
    {
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
        Formula zetaDoubleCubed = Call(
            "riemannZeta",
            F.Seq(F.D(2), F.Sp, F.Times, F.Sp, phiCubed,
                F.Sp, F.Times, F.Sp, s));
        Formula mixedScale = F.Seq(
            F.Open,
            F.D(2), F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp, phiCubed,
            F.Close);
        Formula zetaMixed = Call(
            "riemannZeta",
            F.Seq(mixedScale, F.Sp, F.Times, F.Sp, s));

        return F.Seq(
            zetaSquared, F.Sp, F.Times, F.Sp,
            zetaCubed, F.Sp, F.Times, F.Sp,
            Power(F.Seq(F.Open, zetaDoubleSquared, F.Close),
                F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp,
            Power(F.Seq(F.Open, zetaDoubleCubed, F.Close),
                F.Seq(F.Minus, F.D(1))),
            F.Sp, F.Times, F.Sp,
            zetaMixed, F.Sp, F.Times, F.Sp, gAtS);
    }

    private static Formula NormalizedFactor(
        Formula s,
        Formula p,
        Formula x,
        Formula y)
    {
        Formula oneMinusYSquared = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(F.Seq(F.Open, y, F.Close), F.D(2)), F.Close);
        Formula oneMinusXSquaredY = F.Seq(
            F.Open, F.D(1), F.Sp, F.Minus, F.Sp,
            Power(F.Seq(F.Open, x, F.Close), F.D(2)),
            F.Sp, F.Times, F.Sp, y, F.Close);
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
            F.Grp(F.Id("p"), F.InMacro, F.Sp,
                Call("Primes", NaturalNumbers())),
            body);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

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
