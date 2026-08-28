using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Observation;

internal sealed class PowerTraceCharacteristicPolynomialSaturationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Observation/PowerTraceCharacteristicPolynomialSaturation."
            + "power_trace_characteristic_polynomial_saturation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cayley-Hamilton bounds the recurrence depth of every matrix power trace.",
        H("Characteristic-Polynomial Saturation of Power Traces"),
        Blocks(Describe.Lean(
            DescribeId.Create("power-trace-characteristic-polynomial-saturation"),
            DeclarationHandle.Create(Declaration),
            H("The first dimension-many traces determine all later traces"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an n-by-n matrix over any field, its monic characteristic "
                        + "polynomial and Cayley-Hamilton identity express the nth power "
                        + "as the negative coefficient-weighted sum of lower powers.")),
                Paragraph(Text(
                    "Multiplication by a further power and linearity of the matrix trace "
                        + "give the displayed recurrence at every offset. Strong induction "
                        + "then shows that two matrices with the same characteristic "
                        + "polynomial and the same first n positive-power traces have all "
                        + "positive-power traces equal.")),
                Paragraph(Text(
                    "The formal result strengthens the source context: characteristic zero "
                        + "is unnecessary for this Cayley-Hamilton consequence. Pinned "
                        + "Mathlib supplies the canonical Cayley-Hamilton theorem; repository "
                        + "and library searches found no exact result packaging all three "
                        + "public clauses."))),
            DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula MatrixSpace(Formula dimension, Formula field) =>
        Call("Matrix", Call("Fin", dimension), Call("Fin", dimension), field);

    private static Formula Charpoly(Formula matrix) =>
        Call("charpoly", matrix);

    private static Formula Coeff(Formula matrix, Formula index) =>
        Call("coeff", Charpoly(matrix), index);

    private static Formula MatrixPower(Formula matrix, Formula exponent) =>
        Seq(matrix, Caret, Grp(exponent));

    private static Formula PowerTrace(Formula matrix, Formula exponent) =>
        Call("tr", MatrixPower(matrix, exponent));

    private static Formula IndexedSum(
        Formula index,
        Formula dimension,
        Formula summand) =>
        Seq(Sum, Underscore, Grp(index, Sp, Lt, Sp, dimension), Sp, summand);

    private static Formula TheoremFormula()
    {
        Formula field = F.Id("K");
        Formula dimension = F.Id("n");
        Formula matrix = F.Id("A");
        Formula other = F.Id("B");
        Formula index = F.Id("k");
        Formula offset = F.Id("m");
        Formula exponent = F.Id("r");
        Formula matrixSpace = MatrixSpace(dimension, field);

        Formula matrixRecurrence = Seq(
            MatrixPower(matrix, dimension), Sp, Eq, Sp, Minus,
            IndexedSum(
                index,
                dimension,
                Seq(Coeff(matrix, index), Sp, Times, Sp,
                    MatrixPower(matrix, index))));

        Formula traceRecurrence = Seq(
            Forall, Sp, offset, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            PowerTrace(matrix, Seq(dimension, Sp, Plus, Sp, offset)),
            Sp, Eq, Sp, Minus,
            IndexedSum(
                index,
                dimension,
                Seq(Coeff(matrix, index), Sp, Times, Sp,
                    PowerTrace(matrix, Seq(index, Sp, Plus, Sp, offset)))));

        Formula initialAgreement = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            index, Sp, Lt, Sp, dimension, Sp, Rightarrow, Sp,
            PowerTrace(matrix, Seq(index, Sp, Plus, Sp, D(1))),
            Sp, Eq, Sp,
            PowerTrace(other, Seq(index, Sp, Plus, Sp, D(1))));

        Formula allAgreement = Seq(
            Forall, Sp, exponent, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            PowerTrace(matrix, Seq(exponent, Sp, Plus, Sp, D(1))),
            Sp, Eq, Sp,
            PowerTrace(other, Seq(exponent, Sp, Plus, Sp, D(1))));

        Formula saturation = Seq(
            Forall, Sp, other, Sp, InMacro, Sp, matrixSpace, Comma, Sp,
            Open,
            Charpoly(other), Sp, Eq, Sp, Charpoly(matrix), Sp, Land, Sp,
            initialAgreement,
            Close, Sp, Rightarrow, Sp, allAgreement);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, field, Colon, Sp, TypeUniverse(), Comma, Sp,
                Call("Field", field), Comma, Sp,
                dimension, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(
                matrix, Sp, InMacro, Sp, matrixSpace, Sp, Rightarrow),
            Seq(Open, matrixRecurrence, Close, Sp, Land),
            Seq(Open, traceRecurrence, Close, Sp, Land),
            Seq(saturation, Dot),
        ]));
    }
}
