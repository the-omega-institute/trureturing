using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenFiberCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var v = Id("v");
        var shiftedIndex = Add(v, Num(1));
        var phi = new Formula.Phi();
        var firstReading = new Formula.Floor(new Formula.Fraction(shiftedIndex, phi));
        var secondReading = new Formula.Floor(new Formula.Fraction(
            shiftedIndex,
            new Formula.Power(phi, Num(2))));
        var coordinateA = Call("fiberA", v);
        var coordinateB = Call("fiberB", v);
        var identities = new Formula.Logic(
            Equal(coordinateA, Subtract(firstReading, secondReading)),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(coordinateB, secondReading),
                FormulaLogicOperator.And,
                Equal(Add(coordinateA, coordinateB), firstReading)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Golden fiber coordinates are explicit differences of two Beatty readings.",
            H("Golden Fiber Coordinates"),
            Blocks(
                                Describe.Lean(
                    DescribeId.Create("golden-fiber-coordinates-as-beatty-readings"),
                    DeclarationHandle.Create(
                        "D5/S1/Words/GoldenFiberCoordinates.golden_fiber_coordinates"),
                    H("Fiber coordinates are golden Beatty readings"),
                    StatementSource.FromAuthor(identities),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every positive index v, begin with the shifted reading "
                            + "S(v) = floor((v+1) phi) - 1 and define the integral coordinates "
                            + "a(v) = 2 S(v) - 3v and b(v) = 2v - S(v). The second coordinate "
                            + "is floor((v+1)/phi^2), the first is the difference between the "
                            + "floor readings at 1/phi and 1/phi^2, and their sum is the reading "
                            + "at 1/phi. These are one coupled coordinate identity: the first and "
                            + "sum equations follow algebraically once the second is known.")),
                        Paragraph(Text(
                            "Pinned Mathlib was searched before proving. It supplies the exact "
                            + "golden-ratio square, inverse, and irrationality declarations, its "
                            + "generic Beatty-sequence development, and the integer floor and "
                            + "ceiling laws. It contains no declaration for these fiber-coordinate "
                            + "formulas. The proof is therefore new assembly: it rewrites "
                            + "1/phi as phi-1 and 1/phi^2 as 2-phi, then uses irrationality to turn "
                            + "the ceiling of a positive integer multiple of phi into its floor "
                            + "plus one."))),
                    DescribeRole.Theorem))));
    }
}
