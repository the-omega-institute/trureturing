using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class GoldenGermNextExponentPatternDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/GoldenGermNextExponentPattern."
            + "golden_germ_next_exponent_pattern";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every consecutive golden beta gap is phi or phi-squared, while beta eight, beta "
            + "nine, and the mixed-weight census below beta seven are explicit.",
        H("Golden Germ Next Exponent Pattern"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-germ-next-exponent-pattern"),
            DeclarationHandle.Create(Declaration),
            H("All beta gaps and the next finite exponent census"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every natural mode, the floor increment between consecutive "
                        + "golden multiples is one or two. Unfolding the frozen o5Beta "
                        + "definition converts these two integer cases into consecutive "
                        + "beta gaps equal to phi or phi-squared.")),
                Paragraph(Text(
                    "The floor values at nine and ten times phi give beta eight equal to "
                        + "phi to the sixth power and beta nine equal to phi-sixth plus "
                        + "phi-squared. The frozen fourth-order census supplies beta seven. "
                        + "Together these values prove the two strict inequalities and the "
                        + "complete natural-pair census below beta seven; the pair a equal "
                        + "to one and b equal to three is the boundary equality.")),
                Paragraph(Text(
                    "This theorem advances the next exponent-accounting boundary in the "
                        + "golden Euler germ extraction ladder of OACTC parts 580 and 581. "
                        + "It classifies exponent gaps and finite candidate weights only. "
                        + "It does not assert factor cancellation, an all-order extraction, "
                        + "analytic continuation, O-5, or the Riemann Hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/EulerGerm/GoldenGermFourthOrderExponentCensus")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula v = F.Id("v");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula betaSeven = Call("o5Beta", F.D(7));
        Formula betaEight = Call("o5Beta", F.D(8));
        Formula betaNine = Call("o5Beta", F.D(9));
        Formula phiSquared = Power(F.Varphi, F.D(2));
        Formula phiCubed = Power(F.Varphi, F.D(3));
        Formula phiSixth = Power(F.Varphi, F.D(6));
        Formula nextMode = F.Seq(v, F.Sp, F.Plus, F.Sp, F.D(1));
        Formula betaGap = F.Seq(
            Call("o5Beta", nextMode), F.Sp, F.Minus, F.Sp, Call("o5Beta", v));
        Formula censusCases = F.Seq(
            CensusCase(b, F.D(0), a, F.D(5)), F.Sp, F.Lor, F.Sp,
            CensusCase(b, F.D(1), a, F.D(4)), F.Sp, F.Lor, F.Sp,
            CensusCase(b, F.D(2), a, F.D(2)), F.Sp, F.Lor, F.Sp,
            CensusCase(b, F.D(3), a, F.D(1)));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Forall, F.Sp, v, F.InMacro, F.Sp, NaturalNumbers(), F.Comma, F.Sp,
                F.Open,
                betaGap, F.Sp, F.Eq, F.Sp, F.Varphi,
                F.Sp, F.Lor, F.Sp,
                betaGap, F.Sp, F.Eq, F.Sp, phiSquared,
                F.Close, F.Sp, F.Land),
            F.Seq(
                betaEight, F.Sp, F.Eq, F.Sp, phiSixth,
                F.Sp, F.Land),
            F.Seq(
                betaNine, F.Sp, F.Eq, F.Sp,
                phiSixth, F.Sp, F.Plus, F.Sp, phiSquared,
                F.Sp, F.Land),
            F.Seq(
                betaSeven, F.Sp, F.Lt, F.Sp, betaEight,
                F.Sp, F.Lt, F.Sp, betaNine,
                F.Sp, F.Land),
            F.Seq(
                F.Forall, F.Sp, a, F.Comma, F.Sp, b,
                F.InMacro, F.Sp, NaturalNumbers(), F.Comma),
            F.Seq(
                MixedWeight(a, b, phiSquared, phiCubed),
                F.Sp, F.Leq, F.Sp, betaSeven,
                F.Sp, F.Iff, F.Sp, censusCases, F.Dot),
        ]));
    }

    private static Formula CensusCase(
        Formula b,
        Formula bValue,
        Formula a,
        Formula aBound) =>
        F.Seq(
            F.Open,
            b, F.Sp, F.Eq, F.Sp, bValue,
            F.Sp, F.Land, F.Sp,
            a, F.Sp, F.Leq, F.Sp, aBound,
            F.Close);

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
