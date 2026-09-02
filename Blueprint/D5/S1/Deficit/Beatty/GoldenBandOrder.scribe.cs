using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class GoldenBandOrderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S1/Deficit/Beatty/GoldenBandOrder.golden_band_order";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The structural zero and pole occur in strict order inside the golden band.",
        H("Golden Band Strict Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-band-strict-order"),
            DeclarationHandle.Create(Declaration),
            H("The golden structural zero and pole are strictly ordered"),
            StatementSource.FromAuthor(GoldenBandFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The module imports phi from the frozen S1 GoldenObserverRoute and does not "
                        + "define a second golden ratio. It transcribes only the two constants "
                        + "used here from Hearts: structuralZero=1/(2*phi^2) and "
                        + "structuralPole=1/phi^3. The frontier Hearts module is not imported.")),
                Paragraph(Text(
                    "Pinned Mathlib gives 1<phi<2, positivity of powers, and reversal of strict "
                        + "order under positive reciprocals. Those facts prove all three strict "
                        + "comparisons by ordered-field arithmetic, without using either open "
                        + "heart.")),
                Paragraph(Text(
                    "The resulting order places the structural zero and structural pole inside "
                        + "the factorization window required by the golden observer route."))),
            DescribeRole.Theorem))));

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula GoldenBandFormula()
    {
        Formula phiSquared = Seq(Varphi, Caret, Grp(D(2)));
        Formula phiCubed = Seq(Varphi, Caret, Grp(D(3)));
        Formula lower = Seq(Frac, Grp(D(1)), Grp(D(2), Times, phiCubed));
        Formula structuralZero = F.Id("structuralZero");
        Formula structuralPole = F.Id("structuralPole");
        Formula upper = Seq(Frac, Grp(D(1)), Grp(phiSquared));

        return Disp(And(
            LessThan(lower, structuralZero),
            And(
                LessThan(structuralZero, structuralPole),
                LessThan(structuralPole, upper))));
    }
}
