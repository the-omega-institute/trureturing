using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalBalanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extract the reusable floor kernel behind lower mechanical word balance.",
        H("Balance of Lower Mechanical Words"),
        Blocks(
            Paragraph(Text(
                "Fix a real slope alpha in the half-open interval from zero to one and an arbitrary "
                + "real intercept rho. Irrationality is not required for any result in this module.")),
            Describe.Lean(
                DescribeId.Create("lower-mechanical-letter"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter"),
                H("Lower mechanical letters are consecutive floor differences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The letter at n is the floor at rho+(n+1)alpha minus the floor at "
                    + "rho+n alpha. Its Boolean readout is true exactly when this integer is one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-letter"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalLetter_eq_zero_or_one"),
                H("Every letter is zero or one"),
                StatementSource.FromAuthor(new Formula.Logic(Equal(Call("lowerMechanicalLetter", Id("alpha"), Id("rho"), Id("n")), Num(0)), FormulaLogicOperator.Or, Equal(Call("lowerMechanicalLetter", Id("alpha"), Id("rho"), Id("n")), Num(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two standard floor-add inequalities trap each consecutive floor "
                    + "difference between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-telescope"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWindowTrueCount_eq_floor"),
                H("Window counts telescope to endpoint floors"),
                StatementSource.FromAuthor(Equal(Call("windowTrueCount", Id("alpha"), Id("rho"), Id("i"), Id("n")), Subtract(Call("floor", Add(Id("rho"), Multiply(Add(Id("i"), Id("n")), Id("alpha")))), Call("floor", Add(Id("rho"), Multiply(Id("i"), Id("alpha"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Replacing each Boolean indicator by its zero-or-one letter makes the finite "
                    + "sum telescope, leaving only the two floors at the window endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-balance"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWord_balanced_one"),
                H("Equal-length windows are balanced by one"),
                StatementSource.FromAuthor(new Formula.Logic(Equal(Subtract(Call("windowTrueCount", Id("alpha"), Id("rho"), Id("i"), Id("n")), Call("windowTrueCount", Id("alpha"), Id("rho"), Id("j"), Id("n"))), Subtract(Num(0), Num(1))), FormulaLogicOperator.Or, new Formula.Logic(Equal(Subtract(Call("windowTrueCount", Id("alpha"), Id("rho"), Id("i"), Id("n")), Call("windowTrueCount", Id("alpha"), Id("rho"), Id("j"), Id("n"))), Num(0)), FormulaLogicOperator.Or, Equal(Subtract(Call("windowTrueCount", Id("alpha"), Id("rho"), Id("i"), Id("n")), Call("windowTrueCount", Id("alpha"), Id("rho"), Id("j"), Id("n"))), Num(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every pair of starting positions, the integer true-count difference of "
                    + "equal-length windows has absolute value at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-specialization"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalBalance.goldenWord_balanced_one_mechanical"),
                H("The golden balance theorem is a shifted mechanical specialization"),
                StatementSource.FromAuthor(Equal(Call("goldenWord", Id("i")), Call("mechanicalReadout", Call("inv", Id("phi")), Num(0), Add(Id("i"), Num(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At slope one over the golden ratio and intercept zero, the generic Boolean "
                    + "readout agrees with the frozen golden word after its existing one-index "
                    + "shift. The generic balance theorem therefore proves the same balanced-one "
                    + "statement without an irrationality hypothesis."))),
                DescribeRole.Theorem))));
}
