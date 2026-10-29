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
        Blocks(
            Describe.Lean(
                DescribeId.Create("matrix-square-cayley-hamilton"),
                DeclarationHandle.Create("D5/S0/Observation/MatrixTracePowerSum.sq_eq"),
                H("The Cayley-Hamilton identity in size two"),
                StatementSource.FromAuthor(SquareFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over a commutative ring, the square of a two-by-two matrix is its trace times the matrix minus its determinant times the identity matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-pow-add-two"),
                DeclarationHandle.Create("D5/S0/Observation/MatrixTracePowerSum.pow_add_two"),
                H("The matrix power recurrence in size two"),
                StatementSource.FromAuthor(PowerRecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every commutative ring and every two-by-two matrix, Cayley-Hamilton "
                    + "gives M^(n+2)=trace(M) times M^(n+1) minus det(M) times M^n. "
                    + "This existing recurrence is used by trace_pow_add_two and by the "
                    + "determinant-one Chebyshev transport construction in AndersonDefectFamily."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-trace-pow-add-two"),
                DeclarationHandle.Create("D5/S0/Observation/MatrixTracePowerSum.trace_pow_add_two"),
                H("The two-step recurrence for matrix power traces"),
                StatementSource.FromAuthor(TraceRecurrenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over any commutative ring, the traces of powers of a two-by-two matrix "
                        + "satisfy a two-step recurrence whose coefficients are its trace and determinant."))),
                DescribeRole.Theorem),
            Describe.Lean(
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

    private static Formula SquareFormula()
    {
        Formula r = F.Id("R"), m = F.Id("M");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, r, Colon, Sp, TypeUniverse(), Comma, Sp,
                TypeClass(Call("CommRing", r)), Comma),
            Seq(Forall, Sp, m, Colon, Sp, MatrixSpace(r), Comma),
            Seq(MatrixPower(m, Num(2)), Sp, Eq, Sp,
                MatrixTrace(m), Sp, Cdot, Sp, m, Sp, Minus, Sp,
                MatrixDeterminant(m), Sp, Cdot, Sp, Num(1))
        ]));
    }

    private static Formula TraceRecurrenceFormula()
    {
        Formula ring = F.Id("R");
        Formula matrix = F.Id("M");
        Formula exponent = F.Id("n");
        Formula trace(Formula value) => Seq(Qualified("Matrix", "trace"), Parenthesized(value));
        Formula determinant = Seq(Qualified("Matrix", "det"), Parenthesized(matrix));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Parenthesized(Seq(ring, Colon, Sp, TypeUniverse())), Comma, Sp,
                TypeClass(Call("CommRing", ring)), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(matrix, Colon, Sp, MatrixSpace(ring))), Comma),
            Seq(Forall, Sp, Parenthesized(Seq(exponent, Colon, Sp, Naturals())), Comma),
            Seq(trace(MatrixPower(matrix, Seq(exponent, Sp, Plus, Sp, Num(2)))), Sp, Eq, Sp,
                trace(matrix), Sp, Cdot, Sp,
                trace(MatrixPower(matrix, Seq(exponent, Sp, Plus, Sp, Num(1)))), Sp, Minus, Sp,
                determinant, Sp, Cdot, Sp, trace(MatrixPower(matrix, exponent))),
        ]));
    }

    private static Formula PowerRecurrenceFormula()
    {
        Formula r=F.Id("R"), m=F.Id("M"), n=F.Id("n");
        return Disp(new Formula.Aligned([
            Seq(Forall,Sp,r,Colon,Sp,TypeUniverse(),Comma,Sp,TypeClass(Call("CommRing",r)),Comma),
            Seq(Forall,Sp,m,Colon,Sp,MatrixSpace(r),Comma,Sp,n,Colon,Sp,Naturals(),Comma),
            Seq(MatrixPower(m,Seq(n,Sp,Plus,Sp,Num(2))),Sp,Eq,Sp,
                MatrixTrace(m),Sp,Cdot,Sp,MatrixPower(m,Seq(n,Sp,Plus,Sp,Num(1))),
                Sp,Minus,Sp,MatrixDeterminant(m),Sp,Cdot,Sp,MatrixPower(m,n))
        ]));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));

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
