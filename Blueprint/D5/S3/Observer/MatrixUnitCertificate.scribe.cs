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
