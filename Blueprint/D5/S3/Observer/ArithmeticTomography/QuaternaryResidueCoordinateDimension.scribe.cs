using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class QuaternaryResidueCoordinateDimensionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/ArithmeticTomography/QuaternaryResidueCoordinateDimension."
            + "quaternary_statistical_dimension_eq_three";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-state residue carrier has three explicit pair collisions and statistical "
            + "dimension three.",
        H("Quaternary Residue Coordinate Dimension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quaternary-residue-coordinate-dimension-is-three"),
                DeclarationHandle.Create(Declaration),
                H("Every fixed coordinate pair is incomplete on the four-state carrier"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem is stated directly on the finite residue-state carrier "
                            + "{0,10,15,21}; it has no ambient-state carrier parameter.")),
                    Paragraph(Text(
                        "On this carrier, q2 with q3 merges 15 with 21, q2 with q5 merges 0 "
                            + "with 10, and q3 with q5 merges 0 with 15. These three public "
                            + "clauses force every two-coordinate selection to be incomplete.")),
                    Paragraph(Text(
                        "All three coordinates are jointly injective on the same carrier. "
                            + "Together with the three collision clauses, this makes the least "
                            + "complete coordinate count exactly three."))),
                DescribeRole.Theorem))));

    private static Formula.Logic And(Formula left, Formula right) =>
        new(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("quaternaryCarrier");

        Formula coordinates(Formula first, Formula second) =>
            Seq(OpenBrace, first, Comma, Sp, second, CloseBrace);
        Formula collision(
            Formula first,
            Formula second,
            string leftState,
            string rightState) =>
            Call(
                "MergesOn",
                carrier,
                coordinates(first, second),
                F.Id(leftState),
                F.Id(rightState));

        Formula q2 = F.Id("q2");
        Formula q3 = F.Id("q3");
        Formula q5 = F.Id("q5");
        Formula firstCollision = collision(q2, q3, "state15", "state21");
        Formula secondCollision = collision(q2, q5, "state0", "state10");
        Formula thirdCollision = collision(q3, q5, "state0", "state15");
        Formula dimension = new Formula.Relation(
            Call("statisticalDimensionOn", carrier),
            FormulaRelationOperator.Equal,
            D(3));
        Formula conclusion = And(
            firstCollision,
            And(secondCollision, And(thirdCollision, dimension)));

        return Disp(conclusion);
    }
}
