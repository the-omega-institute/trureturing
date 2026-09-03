using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermFourthOrderExponentCensusDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus."
            + "golden_germ_fourth_order_exponent_census";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The next two golden Euler exponents have explicit phi-polynomial values, and the "
            + "mixed phi-squared and phi-cubed weights through beta six form a finite census.",
        H("Golden Germ Fourth-Order Exponent Census"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-fourth-order-exponent-census"),
            DeclarationHandle.Create(Declaration),
            H("Beta six and beta seven delimit the finite fourth-ledger candidate census"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The exact floor values at six, seven, and eight times the golden ratio "
                        + "give beta five equal to phi to the fifth power, beta six equal to "
                        + "twice phi to the fourth power, and beta seven equal to phi to the "
                        + "fifth plus phi-cubed. In particular beta five is below beta six, "
                        + "which is below beta seven, and both new exponents lie above the "
                        + "phi-fifth threshold.")),
                Paragraph(Text(
                    "The displayed alternatives enumerate every natural pair whose mixed "
                        + "weight a phi-squared plus b phi-cubed is at most beta six. The "
                        + "boundary pair a equal to two and b equal to two is retained because "
                        + "its weight is exactly twice phi to the fourth power. The frozen "
                        + "third-order ledger is the direct predecessor; its local floor and "
                        + "power lemmas are private, so this module reuses the public o5Beta "
                        + "definition and reconstructs those arithmetic evaluations locally.")),
                Paragraph(Text(
                    "This finite ledger advances the open exponent-accounting boundary on the "
                        + "golden Euler germ extraction staircase used in OACTC parts 580 and "
                        + "581. It only identifies candidate "
                        + "weights for selecting signed fourth-order zeta factors. It does not "
                        + "assert fourth-order cancellation, a wider continuation or "
                        + "summability region, O-5, or the Riemann Hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermThirdOrderLedger")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula betaFive = Call("o5Beta", F.D(5));
        Formula betaSix = Call("o5Beta", F.D(6));
        Formula betaSeven = Call("o5Beta", F.D(7));
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula phiFourth = Power(F.Varphi, F.D(4));
        Formula phiFifth = Power(F.Varphi, F.D(5));
        Formula censusCases = F.Seq(
            CensusCase(b, F.D(0), a, F.D(5), false), F.Sp, F.Lor, F.Sp,
            CensusCase(b, F.D(1), a, F.D(3), false), F.Sp, F.Lor, F.Sp,
            CensusCase(b, F.D(2), a, F.D(2), false), F.Sp, F.Lor, F.Sp,
            CensusCase(b, F.D(3), a, F.D(0), true));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                betaSix, F.Sp, F.Eq, F.Sp,
                F.D(2), F.Sp, F.Times, F.Sp, phiFourth, F.Comma),
            F.Seq(
                betaSeven, F.Sp, F.Eq, F.Sp,
                phiFifth, F.Sp, F.Plus, F.Sp, phiCubed, F.Comma),
            F.Seq(
                betaFive, F.Sp, F.Lt, F.Sp, betaSix,
                F.Sp, F.Lt, F.Sp, betaSeven, F.Comma),
            F.Seq(
                phiFifth, F.Sp, F.Lt, F.Sp, betaSix,
                F.Sp, F.Land, F.Sp,
                phiFifth, F.Sp, F.Lt, F.Sp, betaSeven, F.Comma),
            F.Seq(
                F.Forall, F.Sp, a, F.Comma, F.Sp, b,
                F.InMacro, F.Sp, NaturalNumbers(), F.Comma),
            F.Seq(
                MixedWeight(a, b, phiSquared, phiCubed),
                F.Sp, F.Leq, F.Sp, betaSix,
                F.Sp, F.Iff, F.Sp, censusCases, F.Dot),
        ]));
    }

    private static Formula CensusCase(
        Formula b,
        Formula bValue,
        Formula a,
        Formula aBound,
        bool exact)
    {
        Formula aCondition = F.Seq(
            a, F.Sp, exact ? F.Eq : F.Leq, F.Sp, aBound);
        return F.Seq(
            F.Open,
            b, F.Sp, F.Eq, F.Sp, bValue,
            F.Sp, F.Land, F.Sp, aCondition,
            F.Close);
    }

    private static Formula MixedWeight(
        Formula a,
        Formula b,
        Formula phiSquared,
        Formula phiCubed) =>
        F.Seq(
            a, F.Sp, F.Times, F.Sp, phiSquared,
            F.Sp, F.Plus, F.Sp,
            b, F.Sp, F.Times, F.Sp, phiCubed);

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

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
