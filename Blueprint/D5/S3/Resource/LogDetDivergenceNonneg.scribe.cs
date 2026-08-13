using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class LogDetDivergenceNonnegDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The log-determinant divergence is nonnegative on invertible positive semidefinite complex matrices, by reduction to a positive spectral sum.",
        H("Nonnegativity of the Log-Determinant Divergence"),
        Blocks(
            Paragraph(Text(
                "This theorem closes an open left by the frozen log-determinant module. That "
                + "module identified its own missing step precisely: \"The spectral nonnegativity "
                + "theorem is NOT proved here; the remaining blocker is the similarity/spectral "
                + "identification of `sigma^{-1} * rho` with a Hermitian positive-definite "
                + "congruence (and the resulting trace/determinant eigenvalue sum).\" The proof "
                + "below performs exactly that identification.")),
            Describe.Lean(
                DescribeId.Create("log-det-divergence-is-nonnegative-on-invertible-positive-semidefinite-matrices"),
                DeclarationHandle.Create("D5/S3/Resource/LogDetDivergenceNonneg.logDetDivergence_nonneg"),
                H("Log-det divergence is nonnegative on invertible positive semidefinite matrices"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Begin, F.Grp(F.Id("gathered")),
                    F.Forall, F.Sp, F.Id("n"), F.Esc,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("Fintype")),
                    F.Open, F.Id("n"), F.Close, F.CloseBracket, F.Sp,
                    F.OpenBracket, F.Operatorname, F.Grp(F.Id("DecidableEq")),
                    F.Open, F.Id("n"), F.Close, F.CloseBracket, F.Comma, F.RowBreak,
                    F.Forall, F.Sp, F.Rho, F.Comma, F.Sp, F.SigmaLower,
                    F.Colon, F.Sp, F.Operatorname, F.Grp(F.Id("Matrix")), F.Open,
                    F.Id("n"), F.Comma, F.Sp, F.Id("n"), F.Comma, F.Sp,
                    F.Mathbb, F.Grp(F.Id("C")), F.Close, F.Comma, F.RowBreak,
                    F.Open, F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.Rho, F.Close, F.Sp, F.Land, F.Sp,
                    F.Operatorname, F.Grp(F.Id("IsUnit")), F.Open,
                    F.Rho, F.Close, F.Sp, F.Land, F.Sp,
                    F.Operatorname, F.Grp(F.Id("PosSemidef")), F.Open,
                    F.SigmaLower, F.Close, F.Sp, F.Land, F.Sp,
                    F.Operatorname, F.Grp(F.Id("IsUnit")), F.Open,
                    F.SigmaLower, F.Close, F.Close, F.Sp, F.Rightarrow, F.RowBreak,
                    F.D(0), F.Le, F.Sp,
                    F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
                    F.Rho, F.Comma, F.Sp, F.SigmaLower, F.Close, F.Dot,
                    F.End, F.Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The statement uses positive semidefiniteness together with invertibility "
                        + "for both rho and sigma. For a positive semidefinite matrix, mathlib "
                        + "identifies this conjunction with positive definiteness, and the proof "
                        + "makes that conversion immediately. This is a convenient equivalent "
                        + "interface, not a weakening of the positive-definite hypothesis.")),
                    Paragraph(Text(
                        "Let s be the positive semidefinite square root of sigma and set A equal "
                        + "to s inverse times rho times s inverse. Since s is Hermitian and "
                        + "invertible, A is a congruence of rho and is therefore positive definite. "
                        + "The identity sigma inverse times rho equals s inverse times A times s "
                        + "then exhibits the matrix in the divergence as similar to A. Cyclicity "
                        + "of trace and multiplicativity of determinant consequently identify its "
                        + "real trace and the real part of its determinant with those of A, in the "
                        + "same convention used by the frozen definition.")),
                    Paragraph(Text(
                        "Because A is Hermitian positive definite, all of its eigenvalues lambda_i "
                        + "are strictly positive, their sum is its trace, and their product is its "
                        + "determinant. The divergence is therefore the finite sum of "
                        + "lambda_i - log lambda_i - 1. Each summand is nonnegative by the scalar "
                        + "inequality log x <= x - 1 for x > 0, which proves the result.")),
                    Paragraph(Text(
                        "No equality characterization is claimed. Proving that vanishing forces "
                        + "rho and sigma to coincide would additionally require the strictness "
                        + "condition for log x <= x - 1 and the fact that a Hermitian matrix whose "
                        + "eigenvalues are all one is the identity; that further argument was "
                        + "deliberately not attempted here.")),
                    Paragraph(Text(
                        "The authored display is legal because no pinned projectable statement "
                        + "fixture exists for this declaration; construction records the resulting "
                        + "ProjectionGap."))),
                DescribeRole.Theorem
            ))));
}
