using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class EscapeThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var x = Id("x");
        var d = Id("d");
        var conj = Id("betaThirteenConjugate");
        var thr = Id("escapeThreshold");
        var reals = Id("R");

        var expanding = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("d"), reals),
            ],
            new Formula.Logic(
                new Formula.Relation(thr, FormulaRelationOperator.LessThan,
                    new Formula.Absolute(x)),
                FormulaLogicOperator.Implies,
                new Formula.Relation(new Formula.Absolute(x),
                    FormulaRelationOperator.LessThan,
                    new Formula.Absolute(Subtract(Multiply(conj, x), d)))));

        var spec = Equal(
            Multiply(Subtract(new Formula.Absolute(conj), Num(1)), thr), Num(2));

        var statement = new Formula.Logic(spec, FormulaLogicOperator.And, expanding);

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/EscapeThreshold.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Past three plus the square root of thirteen, one conjugate step cannot be undone "
                + "by subtracting a digit.",
            H("Escape Threshold"),
            Blocks(
                Paragraph(Text(
                    "The threshold is two divided by the excess of the conjugate modulus over "
                        + "one, which in closed form is three plus the square root of thirteen. "
                        + "Past it the image of one step is strictly farther from the origin "
                        + "than its source, for every digit between zero and two.")),
                Describe.Lean(
                    DescribeId.Create("the-escape-threshold-is-a-threshold"),
                    DeclarationHandle.Create(
                        declarationPrefix + "escape_threshold_is_a_threshold"),
                    H("The escape threshold is a threshold"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the general half of the coefficient-growth argument. The other "
                            + "half is exhibiting one point of the orbit past the threshold; "
                            + "measurement puts the conjugate orbit exactly at the threshold on "
                            + "the third step and one beyond it on the fourth, but that is not "
                            + "proved here."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/ConjugateBridge")),
            ]));
    }
}
