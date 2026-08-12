using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalGoldenBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connect the reusable lower-mechanical floor kernel to the frozen golden word.",
        H("Golden Bridge for Lower Mechanical Words"),
        Blocks(
            Paragraph(Text(
                "Specialize the general lower-mechanical kernel at slope one over the golden "
                + "ratio and intercept zero. The existing one-index shift is retained, and "
                + "irrationality is not used by the balance proof.")),
            Describe.Lean(
                DescribeId.Create("golden-letter-bridge"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalLetter_golden"),
                H("The golden slope specializes the generic letter"),
                StatementSource.FromAuthor(Equal(Call("goldenWord", Id("i")), Call("mechanicalReadout", Call("inv", Id("phi")), Num(0), Add(Id("i"), Num(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the frozen golden slope and zero intercept, the generic floor "
                    + "difference is exactly the existing golden mechanical letter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-word-shift"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalGoldenBridge.lowerMechanicalWord_golden"),
                H("The generic readout agrees with the shifted golden word"),
                StatementSource.FromAuthor(Equal(Call("goldenMechanicalLetter", Add(Id("i"), Num(1))), Call("lowerMechanicalLetter", Call("inv", Id("phi")), Num(0), Add(Id("i"), Num(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Boolean generic readout agrees with the frozen golden word at the "
                    + "repository's established one-index shift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-window-bridge"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWindowTrueCount_eq_lowerMechanicalWindowTrueCount"),
                H("Golden windows are shifted generic windows"),
                StatementSource.FromAuthor(Equal(Call("goldenWindowTrueCount", Id("i"), Id("n")), Call("windowTrueCount", Call("inv", Id("phi")), Num(0), Add(Id("i"), Num(1)), Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen golden true-count function is equal to the generic lower-"
                    + "mechanical count beginning one position later."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-balance-bridge"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalGoldenBridge.goldenWord_balanced_one_mechanical"),
                H("Frozen golden balance follows from the generic theorem"),
                StatementSource.FromAuthor(new Formula.Logic(Equal(Subtract(Call("goldenWindowTrueCount", Id("i"), Id("n")), Call("goldenWindowTrueCount", Id("j"), Id("n"))), Subtract(Num(0), Num(1))), FormulaLogicOperator.Or, new Formula.Logic(Equal(Subtract(Call("goldenWindowTrueCount", Id("i"), Id("n")), Call("goldenWindowTrueCount", Id("j"), Id("n"))), Num(0)), FormulaLogicOperator.Or, Equal(Subtract(Call("goldenWindowTrueCount", Id("i"), Id("n")), Call("goldenWindowTrueCount", Id("j"), Id("n"))), Num(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing golden balanced-one statement is obtained directly from "
                    + "the generic equal-window theorem through the shift bridge."))),
                DescribeRole.Theorem))));
}
