using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class BinarySimplestTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var Q = Id("Q");
        var naturals = Id("N");

        var statement = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("Q"), naturals)],
            new Formula.Logic(
                new Formula.Relation(Num(1), FormulaRelationOperator.LessThanOrEqual, Q),
                FormulaLogicOperator.Implies,
                Equal(
                    Multiply(
                        new Formula.Power(Num(2), Q),
                        Call("radixDistance", Num(2), Q,
                            new Formula.Fraction(Num(1), Num(3)))),
                    new Formula.Fraction(Num(1), Num(3)))));

        const string declarationPrefix = "D5/S1/Depth/BinarySimplestTail.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "One third is the binary tower's constant arm, and the golden tail is the rational "
                + "tower's counterpart.",
            H("Binary Simplest Tail"),
            Blocks(
                Paragraph(Text(
                    "One third keeps the same normalised distance from the binary grid at every "
                        + "window, which is what makes its expansion the simplest periodic tail "
                        + "there. The arm stays fixed for an arithmetic reason: three and two "
                        + "are coprime, so the numerator of the distance never vanishes and the "
                        + "champion cannot drift toward a grid point.")),
                Paragraph(Text(
                    "The all-ones continued-fraction tail of the golden ratio is the rational "
                        + "tower's counterpart of the same phenomenon. Both statements already "
                        + "existed; neither is restated here.")),
                Paragraph(Text(
                    "The remark's remaining sentence — that a random point's normalised distance "
                        + "is near-uniform on the lower half interval, with liminf almost surely "
                        + "zero — is a numerical experiment, marked as machine-checked in the "
                        + "source rather than proved. It is deliberately absent from the "
                        + "conjunction, following the six covered atoms in the repository that "
                        + "carry such annotations and are covered by their provable part only.")),
                Describe.Lean(
                    DescribeId.Create("one-third-is-the-binary-constant-arm"),
                    DeclarationHandle.Create(
                        declarationPrefix + "binary_simplest_tail_package"),
                    H("One third is the binary constant arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed conjunct is the constant arm; the others are the golden "
                            + "tail and the exact distance formula behind the constancy. An "
                            + "earlier draft carried coprimality alone in that third slot, which "
                            + "decides trivially and mentions no window — a quantified constant "
                            + "rather than content."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/ConstantArms")),
            ]));
    }
}
