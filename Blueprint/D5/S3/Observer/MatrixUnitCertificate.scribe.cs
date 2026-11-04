using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class MatrixUnitCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fourier combinations of the cyclic window clock and shift form exact matrix units.",
        H("Exact Matrix Units from a Finite Weyl Pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("clock-phase-powers-are-cyclic-characters"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MatrixUnitCertificate.clock_phase_pow_eq_character"),
                H("Clock phase powers are cyclic characters"),
                StatementSource.FromAuthor(ClockPhaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonzero window cardinality M and cyclic indices r and k, "
                        + "raising the rth clock phase to the representative of k gives "
                        + "the standard cyclic character with frequency k evaluated at r."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-shift-power-entries"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MatrixUnitCertificate.shift_matrix_pow_apply"),
                H("Entries of every cyclic shift power"),
                StatementSource.FromAuthor(ShiftPowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonzero natural cardinality M, every natural exponent n, and "
                        + "cyclic indices r and s, the (r,s) entry of the nth power of "
                        + "shiftMatrix M is the complex number one exactly when r-s equals "
                        + "the image of n in Z/MZ, and is zero otherwise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fourier-matrix-units-are-single-entry-matrices"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MatrixUnitCertificate.matrix_unit_eq_single"),
                H("Fourier matrix units are single-entry matrices"),
                StatementSource.FromAuthor(Disp(Seq(
                    Unit(F.Id("i"), F.Id("j")), Eq,
                    Operatorname, Grp(F.Id("single")),
                    Open, F.Id("i"), Comma, F.Id("j"), Comma, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive window cardinality M and indices i and j in Z/MZ, "
                        + "the Fourier construction E_ij defined below equals the matrix with "
                        + "entry one at (i,j) and zero elsewhere. Character orthogonality gives "
                        + "the diagonal projector, and the shift places its nonzero entry at (i,j)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weyl-fourier-matrix-units-multiply-exactly"),
                DeclarationHandle.Create("D5/S3/Observer/MatrixUnitCertificate.matrix_unit_mul"),
                H("Weyl Fourier matrix units multiply exactly"),
                StatementSource.FromAuthor(MatrixUnitRelationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For each positive window cardinality M, Fourier projection of the " +
                                        "frozen clock V_M onto address i, followed by the frozen shift " +
                                        "U_M^(i-j), defines E_ij. The exponent i-j is forced by the existing " +
                                        "entry convention U_M(r,s) = 1 exactly when r-s = 1.")),
                                    Paragraph(Text(
                                        "The standard Z/MZ characters enumerate the full finite character " +
                                        "group. Exact character orthogonality makes the Fourier projector the " +
                                        "single-entry matrix at (i,i), and the shift moves its nonzero column to " +
                                        "j. Thus E_ij is exactly the standard single-entry matrix at (i,j).")),
                                    Paragraph(Text(
                                        "Consequently E_ij E_kl equals E_il when j=k and is the zero matrix " +
                                        "otherwise. This is an identity of complex matrices for every four " +
                                        "window indices; it has no residual, norm bound, tolerance, or numerical " +
                                        "approximation."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("diagonal-matrix-units-resolve-the-identity"),
                DeclarationHandle.Create("D5/S3/Observer/MatrixUnitCertificate.matrix_units_sum_diagonal"),
                H("Diagonal matrix units resolve the identity"),
                StatementSource.FromAuthor(CompletenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Summing the diagonal Fourier matrix units over every cyclic address gives " +
                                    "the identity matrix exactly. This is the finite-window completeness " +
                                    "relation for the same Weyl-generated family."))),
                DescribeRole.Theorem
            ))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula ClockPhaseFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp,
        OpenBracket, Operatorname, Grp(F.Id("NeZero")), Sp, F.Id("M"), CloseBracket, Comma, Sp,
        Forall, Sp, F.Id("r"), Comma, Sp, F.Id("k"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z")), Comma, Esc,
        new Formula.Relation(
            new Formula.Power(
                Parenthesized(new Formula.Power(Call("windowRoot", F.Id("M")), Call("val", F.Id("r")))),
                Call("val", F.Id("k"))),
            FormulaRelationOperator.Equal,
            new Formula.Apply(
                new Formula.Subscript(Seq(Operatorname, Grp(F.Id("character"))), F.Id("M")),
                [F.Id("k"), F.Id("r")]))));

    private static Formula ShiftPowerFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Sp, OpenBracket,
        Operatorname, Grp(F.Id("NeZero")), Sp, F.Id("M"), CloseBracket, Comma, RowBreak,
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Forall, Sp, F.Id("r"), Comma, Sp, F.Id("s"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z")), Comma, RowBreak,
        Open, Operatorname, Grp(F.Id("shiftMatrix")), Open, F.Id("M"), Close,
        Caret, Grp(F.Id("n")), Close, Underscore, Grp(F.Id("r"), F.Id("s")), Eq,
        Begin, Grp(F.Id("cases")),
        Open, D(1), Colon, Mathbb, Grp(F.Id("C")), Close, Comma, Amp,
        F.Id("r"), Minus, F.Id("s"), Eq,
        Open, F.Id("n"), Colon, Mathbb, Grp(F.Id("Z")), Slash,
        F.Id("M"), Mathbb, Grp(F.Id("Z")), Close, RowBreak,
        Open, D(0), Colon, Mathbb, Grp(F.Id("C")), Close, Comma, Amp,
        Operatorname, Grp(F.Id("otherwise")),
        End, Grp(F.Id("cases")),
        End, Grp(F.Id("gathered"))));

    private static Formula MatrixUnitRelationFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, RowBreak,
        Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
        F.Id("k"), Comma, Sp, F.Id("l"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z")),
        Comma, RowBreak,
        Unit(F.Id("i"), F.Id("j")), Colon, Eq,
        Open,
        Frac, Grp(D(1)), Grp(F.Id("M")),
        Sum, Underscore, Grp(
            F.Id("a"), Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z"))),
        Omega, Underscore, Grp(F.Id("M")),
        Caret, Grp(Minus, F.Id("i"), F.Id("a")),
        F.Id("V"), Underscore, Grp(F.Id("M")),
        Caret, Grp(F.Id("a")),
        Close,
        F.Id("U"), Underscore, Grp(F.Id("M")),
        Caret, Grp(F.Id("i"), Minus, F.Id("j")),
        Comma, RowBreak,
        Unit(F.Id("i"), F.Id("j")),
        Unit(F.Id("k"), F.Id("l")), Sp, Eq, Sp,
        Begin, Grp(F.Id("cases")),
        D(1), Comma, Amp, F.Id("j"), Eq, F.Id("k"), RowBreak,
        D(0), Comma, Amp, F.Id("j"), Neq, Sp, F.Id("k"),
        End, Grp(F.Id("cases")),
        Unit(F.Id("i"), F.Id("l")), Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula CompletenessFormula() => Disp(Seq(
        Forall, Sp, F.Id("M"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)), Comma, Esc,
        Sum, Underscore, Grp(
            F.Id("i"), Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("Z")), Slash, F.Id("M"), Mathbb, Grp(F.Id("Z"))),
        Unit(F.Id("i"), F.Id("i")), Sp, Eq, Sp,
        F.Id("I"), Underscore, Grp(F.Id("M")), Dot));

    private static Formula Unit(Formula row, Formula column) => Seq(
        F.Id("E"), Underscore, Grp(row, column));
}
