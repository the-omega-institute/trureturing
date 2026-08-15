using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ShiftOperators;

internal sealed class ShiftRangeProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The backward-shift defect projection is the norm-one divisibility filter on zeta coefficients.",
        H("Shift Range Projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shift-range-projection-is-the-divisibility-filter"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection."
                    + "shiftRangeProjection_apply"),
                H("The projection is the divisibility filter"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("b"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Forall, Sp, F.Id("x"), InMacro, Sp,
                    Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Open, F.Id("x"), Close, Open, F.Id("b"), Close,
                    Sp, Eq, Sp, Begin, Grp(F.Id("cases")),
                    F.Id("x"), Open, F.Id("b"), Close, Comma, Amp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close, Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("b"), Close, RowBreak,
                    D(0), Comma, Amp, F.Text, Grp(F.Id("otherwise")),
                    End, Grp(F.Id("cases"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime-axis address u, the projection retains exactly those "
                    + "coefficients whose encoded address is divisible by the encoding of u. "
                    + "At a divisible address it returns the original coefficient, and at every "
                    + "other address it returns zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shift-range-projection-is-idempotent"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection."
                    + "shift_range_projection_idempotent"),
                H("The projection is idempotent"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the divisibility filter twice has the same effect as applying it "
                    + "once. The proof is coordinatewise: on divisible addresses both passes "
                    + "retain the coefficient, while on all other addresses the first pass has "
                    + "already produced zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("backward-shift-and-projection-have-the-same-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection."
                    + "backward_shift_apply_eq_zero_iff"),
                H("The backward shift and projection have the same kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Forall, Sp, F.Id("x"), InMacro, Sp,
                    Operatorname, Grp(F.Id("ZetaHilbertSpace")), Comma, Esc,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Open, F.Id("x"), Close,
                    Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Open, F.Id("x"), Close,
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A Hilbert vector is annihilated by the backward shift exactly when it is "
                    + "annihilated by the defect projection. One direction follows by applying "
                    + "forward translation to zero; the reverse follows by applying the backward "
                    + "shift and using its right-inverse identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shift-range-projection-has-operator-norm-one"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection."
                    + "shift_range_projection_norm_eq_one"),
                H("The projection has norm one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Vert, Sp, Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Vert, Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The projection is a contraction because forward translation preserves the "
                    + "norm and the backward shift is norm-nonincreasing. The unit single-support "
                    + "vector at u is fixed by the projection, so the contraction bound is "
                    + "attained and the operator norm is exactly one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projected-zeta-pairing-reproduces-the-euler-factor-kernel"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection."
                    + "shift_range_projection_zeta_kernel"),
                H("The projected zeta pairing reproduces the Euler-factor kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Forall, Sp, F.Id("s"), Comma, Sp, F.Id("w"), InMacro, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Esc,
                    Open,
                    Operatorname, Grp(F.Id("criticalAbscissa")), Sp, Lt, Sp,
                    Re, Grp(F.Id("s")), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("criticalAbscissa")), Sp, Lt, Sp,
                    Re, Grp(F.Id("w")), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("sourcePairing")), Open,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Open,
                    Operatorname, Grp(F.Id("labeledZetaVector")),
                    Open, F.Id("s"), Close, Close, Comma, Sp,
                    Operatorname, Grp(F.Id("labeledZetaVector")),
                    Open, F.Id("w"), Close, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("labeledZetaCoefficient")),
                    Open, F.Id("s"), Sp, Plus, Sp, Overline, Grp(F.Id("w")),
                    Comma, Sp, F.Id("u"), Close, Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("classicalZeta")),
                    Open, F.Id("s"), Sp, Plus, Sp, Overline, Grp(F.Id("w")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For square-summable labeled zeta vectors at s and w, projecting the first "
                    + "vector before taking the source pairing multiplies the zeta reproducing "
                    + "kernel by the u-th labeled coefficient at s plus conjugate w. The proof "
                    + "uses the backward-shift eigenrelation, pairing adjointness, and the "
                    + "multiplicativity of the labeled coefficient."))),
                DescribeRole.Theorem))));
}
