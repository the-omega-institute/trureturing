using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class CaptureCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var cardA = Call("card", Id("A"));
        var cardY = Call("card", Id("Y"));
        var cardS = Call("card", Id("S"));
        var fixedPoints = Call("card", Call("Fix", Id("f")));
        var captured = Call("card", Call("capturedListings", Id("f"), Id("S")));
        var allListings = new Formula.Power(cardY, new Formula.Power(cardA, Num(2)));
        var capturedCount = Multiply(
            new Formula.Power(fixedPoints, cardS),
            new Formula.Power(cardY, Multiply(cardA, Subtract(cardA, cardS))));
        var singleCaptureCount = Multiply(
            fixedPoints,
            new Formula.Power(cardY, Multiply(cardA, Subtract(cardA, Num(1)))));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Diagonal/CaptureCount",
                "Finite diagonal capture intersections have exact counts and factor independently."),
            H("Diagonal Capture Count"),
            Blocks(
                DocumentBlock.Describe.Lemma(
                    DescribeId.Create("simultaneous-captures-have-an-exact-cardinality"),
                    H("Simultaneous captures have an exact cardinality"),
                    LeanTheorem("D5/S0/Diagonal/CaptureCount.capture_inter_card"),
                    FormulaDsl.Disp(Equal(captured, capturedCount)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a finite set of selected rows, each selected diagonal entry is "
                        + "chosen from the fixed points of the twist. All rows outside the "
                        + "selection remain free, and the selected rows are then determined.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("capture-intersections-factor-in-integer-form"),
                    H("Capture intersections factor in integer form"),
                    LeanTheorem("D5/S0/Diagonal/CaptureCount.capture_independent"),
                    FormulaDsl.Disp(Equal(
                        Multiply(captured, new Formula.Power(allListings, cardS)),
                        Multiply(
                            new Formula.Power(singleCaptureCount, cardS),
                            allListings))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "After clearing every denominator, the count of a simultaneous capture "
                        + "times the corresponding power of the full listing count equals the "
                        + "product of the single-row capture counts.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("fixed-point-free-twists-have-the-full-escape-count"),
                    H("Fixed-point-free twists have the full escape count"),
                    LeanTheorem("D5/S0/Diagonal/CaptureCount.escaped_card_of_fixfree"),
                    FormulaDsl.Disp(new Formula.Logic(
                        Equal(fixedPoints, Num(0)),
                        FormulaLogicOperator.Implies,
                        Equal(
                            Call("card", Call("escapedListings", Id("f"))),
                            allListings))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "When the twist has no fixed point, the previously established exact "
                        + "escape count reduces to the cardinality of the full finite listing "
                        + "space.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("fixed-point-free-twists-escape-every-listing"),
                    H("Fixed-point-free twists escape every listing"),
                    LeanTheorem("D5/S0/Diagonal/CaptureCount.escape_all_of_fixfree"),
                    FormulaDsl.Disp(new Formula.Logic(
                        Equal(fixedPoints, Num(0)),
                        FormulaLogicOperator.Implies,
                        Call("allListingsEscaped", Id("f")))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The full escape count equals the size of the ambient listing type, so "
                        + "any unescaped listing would force a strict cardinality deficit. Thus "
                        + "every listing is escaped.")))
                ))));
    }
}
