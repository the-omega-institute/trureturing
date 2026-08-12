using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class CaptureCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Lawvere =
        LibraryNoteRef.Create("D5/L/Diagonal/lawvere1969diagonal");

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

        return DocumentDefinition.Create(ScribeNode.Create(
            "Finite diagonal capture intersections have exact counts and factor independently.",
            H("Diagonal Capture Count"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("simultaneous-captures-have-an-exact-cardinality"),
                    DeclarationHandle.Create("D5/S0/Diagonal/CaptureCount.capture_inter_card"),
                    H("Simultaneous captures have an exact cardinality"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(captured, capturedCount))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a finite set of selected rows, each selected diagonal entry is "
                        + "chosen from the fixed points of the twist. All rows outside the "
                        + "selection remain free, and the selected rows are then determined."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("capture-intersections-factor-in-integer-form"),
                    DeclarationHandle.Create("D5/S0/Diagonal/CaptureCount.capture_independent"),
                    H("Capture intersections factor in integer form"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(
                        Multiply(captured, new Formula.Power(allListings, cardS)),
                        Multiply(
                            new Formula.Power(singleCaptureCount, cardS),
                            allListings)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "After clearing every denominator, the count of a simultaneous capture "
                        + "times the corresponding power of the full listing count equals the "
                        + "product of the single-row capture counts."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("fixed-point-free-twists-have-the-full-escape-count"),
                    DeclarationHandle.Create("D5/S0/Diagonal/CaptureCount.escaped_card_of_fixfree"),
                    H("Fixed-point-free twists have the full escape count"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Logic(
                        Equal(fixedPoints, Num(0)),
                        FormulaLogicOperator.Implies,
                        Equal(
                            Call("card", Call("escapedListings", Id("f"))),
                            allListings)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "When the twist has no fixed point, the previously established exact "
                        + "escape count reduces to the cardinality of the full finite listing "
                        + "space."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("fixed-point-free-twists-escape-every-listing"),
                    DeclarationHandle.Create("D5/S0/Diagonal/CaptureCount.escape_all_of_fixfree"),
                    H("Fixed-point-free twists escape every listing"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Logic(
                        Equal(fixedPoints, Num(0)),
                        FormulaLogicOperator.Implies,
                        Call("allListingsEscaped", Id("f"))))),
                    AssessedProvenance.FromLiterature(Lawvere),
                    Blocks(Paragraph(Text(
                        "The full escape count equals the size of the ambient listing type, so "
                        + "any unescaped listing would force a strict cardinality deficit. Thus "
                        + "every listing is escaped."))),
                    DescribeRole.Theorem))));
    }
}
