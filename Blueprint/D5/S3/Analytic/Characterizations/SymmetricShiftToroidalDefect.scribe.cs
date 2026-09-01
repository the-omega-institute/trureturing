using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class SymmetricShiftToroidalDefectDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Characterizations/SymmetricShiftToroidalDefect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Xi reflection and conjugation identify the symmetric readings by the "
            + "Hermite-Biehler sharp, while nonzero toroidal frames cancel from "
            + "their normalized energies.",
        H("Symmetric-Shift Toroidal Hermite-Biehler Defect"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetric-shift-toroidal-hermite-biehler-defect"),
                DeclarationHandle.Create(
                    Prefix + "symmetric_shift_toroidal_hermite_biehler_defect"),
                H("The normalized frame defect is the shifted-xi norm defect"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an upper-half-plane point and a positive shift, each nonzero "
                            + "frame contributes the same squared norm to numerator and "
                            + "denominator, so its factor cancels.")),
                    Paragraph(Text(
                        "The frozen reflection and conjugation theorems for the completed "
                            + "xi reading identify the minus shift with the Hermite-Biehler "
                            + "sharp of the plus shift.")),
                    Paragraph(Text(
                        "A concrete one-dimensional frame evaluates the defect to three. "
                            + "Setting the plus frame to zero instead evaluates it to minus "
                            + "one, recording why frame nonvanishing is required."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula PowerTwo(Formula value) =>
        new Formula.Power(value, D(2));

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula z = F.Id("z");
        Formula omega = F.Omega;
        Formula plusFrame = F.Id("Tplus");
        Formula minusFrame = F.Id("Tminus");
        Formula shiftBase = Call("s", z);
        Formula plusReading = Call("xi", Add(shiftBase, omega));
        Formula minusReading = Call("xi", Subtract(shiftBase, omega));
        Formula sharpIdentity = EqualTo(
            minusReading, Call("sharp", Call("Eplus", omega), z));
        Formula premise = And(
            LessThan(D(0), Call("Im", z)),
            And(
                LessThan(D(0), omega),
                And(NotEqualTo(plusFrame, D(0)), NotEqualTo(minusFrame, D(0)))));
        Formula halfPlane = LessThan(
            new Formula.Fraction(D(1), D(2)), Call("Re", shiftBase));
        Formula defect = EqualTo(
            Call("toroidalHermiteBiehlerDefect", z, omega, plusFrame, minusFrame),
            Subtract(PowerTwo(new Formula.Norm(plusReading)),
                PowerTwo(new Formula.Norm(minusReading))));

        return Disp(Seq(
            Forall, Sp, z, Comma, Sp, omega, Comma, Sp,
            plusFrame, Comma, Sp, minusFrame, Comma, Sp,
            Implies(premise, And(sharpIdentity, And(halfPlane, defect)))));
    }
}
