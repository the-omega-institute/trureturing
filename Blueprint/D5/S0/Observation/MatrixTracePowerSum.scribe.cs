using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Observation;

internal sealed class MatrixTracePowerSumDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Observation/MatrixTracePowerSum.trace_pow_eq_add_pow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed power traces for a two by two matrix from a supplied Vieta pair.",
        H("Power Traces from Trace and Determinant in Size Two"),
        Blocks(Describe.Lean(
            DescribeId.Create("matrix-trace-power-sum"),
            DeclarationHandle.Create(Declaration),
            H("A supplied Vieta pair gives every power trace"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "If a two by two matrix has trace a + b and determinant a * b, then "
                        + "the trace of its k-th power is a ^ k + b ^ k.")),
                Paragraph(Text(
                    "No algebraically closed field is needed: the pair is supplied as a "
                        + "hypothesis rather than extracted from a characteristic polynomial, "
                        + "so the statement holds over any commutative ring in which such a "
                        + "pair happens to exist.")),
                Paragraph(Text(
                    "The proof starts from the size-two Cayley identity M ^ 2 = trace M • M "
                        + "- det M • 1, multiplies it by M ^ n, and reads off the resulting "
                        + "recurrence on traces.")),
                Paragraph(Text(
                    "A two-step induction then identifies that recurrence with the scalar "
                        + "power sums.")),
                Paragraph(Text(
                    "The frozen power_trace_characteristic_polynomial_saturation in this "
                        + "same directory already gives, for a field and any size, "
                        + "Cayley-Hamilton together with a recurrence among power traces; at "
                        + "size two that recurrence is the one used here, while this node adds "
                        + "the closed form and removes the field hypothesis, and that file is "
                        + "neither restated nor amended."))),
            DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula MatrixSpace(Formula ring) =>
        Call("Matrix", Call("Fin", Num(2)), Call("Fin", Num(2)), ring);

    private static Formula MatrixPower(Formula matrix, Formula exponent) =>
        Seq(matrix, Caret, Grp(exponent));

    private static Formula MatrixTrace(Formula matrix) =>
        Call("tr", matrix);

    private static Formula MatrixDeterminant(Formula matrix) =>
        Call("det", matrix);

    private static Formula TypeClass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula ring = F.Id("R");
        Formula matrix = F.Id("M");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula exponent = F.Id("k");
        Formula vietaHypotheses = Seq(
            Open,
            MatrixTrace(matrix), Sp, Eq, Sp, a, Sp, Plus, Sp, b,
            Sp, Land, Sp,
            MatrixDeterminant(matrix), Sp, Eq, Sp, a, Sp, Cdot, Sp, b,
            Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, ring, Colon, Sp, TypeUniverse(), Comma, Sp,
                TypeClass(Call("CommRing", ring)), Comma),
            Seq(
                Forall, Sp, matrix, Colon, Sp, MatrixSpace(ring), Comma),
            Seq(
                Forall, Sp, a, Comma, Sp, b, Colon, Sp, ring, Comma),
            Seq(
                Forall, Sp, exponent, Colon, Sp, Naturals(), Comma),
            Seq(
                vietaHypotheses, Sp, Rightarrow, Sp,
                MatrixTrace(MatrixPower(matrix, exponent)), Sp, Eq, Sp,
                a, Caret, Grp(exponent), Sp, Plus, Sp,
                b, Caret, Grp(exponent), Dot),
        ]));
    }
}
