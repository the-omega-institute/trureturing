using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class LogDetDivergenceEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The log-determinant divergence vanishes exactly when its two invertible positive semidefinite matrix arguments coincide.",
        H("Equality in the Log-Determinant Divergence"),
        Blocks(
            Paragraph(Text(
                "This theorem completes the pair begun by the preceding nonnegativity wave. That "
                + "wave deliberately declined the equality case and named its two remaining "
                + "obstructions: strictness in the scalar inequality log x <= x - 1, and the fact "
                + "that a Hermitian matrix whose eigenvalues are all one is the identity. Both "
                + "obstructions are closed here.")),
            Describe.Lean(
                DescribeId.Create("zero-log-det-divergence-characterizes-equality-on-invertible-positive-semidefinite-matrices"),
                DeclarationHandle.Create("D5/S3/Resource/LogDetDivergenceEquality.logDetDivergence_eq_zero_iff"),
                H("Zero log-det divergence characterizes equality on invertible positive semidefinite matrices"),
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
                    F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
                    F.Rho, F.Comma, F.Sp, F.SigmaLower, F.Close, F.Eq, F.D(0),
                    F.Sp, F.Leftrightarrow, F.Sp, F.Rho, F.Eq, F.SigmaLower, F.Dot,
                    F.End, F.Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The hypotheses are identical, word for word, to those of the frozen "
                        + "nonnegativity theorem: rho and sigma are positive semidefinite and "
                        + "invertible. The two theorems therefore form a complete "
                        + "nonnegativity-plus-equality pair over exactly the same domain.")),
                    Paragraph(Text(
                        "As in the nonnegativity proof, let s be the positive semidefinite square "
                        + "root of sigma and set A equal to s inverse times rho times s inverse. "
                        + "Similarity and the trace and determinant identities express the "
                        + "divergence as the finite sum of lambda_i - log lambda_i - 1 over the "
                        + "strictly positive eigenvalues of the Hermitian positive-definite matrix "
                        + "A. Every summand is nonnegative, so a vanishing sum forces every "
                        + "summand to vanish.")),
                    Paragraph(Text(
                        "For an eigenvalue different from one, the strict inequality log x < x - 1 "
                        + "makes its summand strictly positive. Hence every eigenvalue is one. The "
                        + "spectral theorem then reconstructs A as the identity, and unwinding its "
                        + "definition through the square-root identities gives rho equal to sigma. "
                        + "Conversely, equality of rho and sigma reduces the claim to the frozen "
                        + "zero self-divergence theorem.")),
                    Paragraph(Text(
                        "The Lean module deliberately records the provenance of two negative "
                        + "mathlib searches so that a later reader does not repeat them. There is "
                        + "no declaration `Real.log_lt_sub_one_of_ne`; the available strict result "
                        + "is `Real.log_lt_sub_one_of_pos`. There is likewise no declaration "
                        + "`Matrix.IsHermitian.eq_one_of_eigenvalues_eq_one`; the identity is "
                        + "reconstructed directly from `Matrix.IsHermitian.spectral_theorem`. This "
                        + "record is deliberate rather than incidental.")),
                    Paragraph(Text(
                        "The authored display is legal because no pinned projectable statement "
                        + "fixture exists for this declaration; construction records the resulting "
                        + "ProjectionGap."))),
                DescribeRole.Theorem
            ))));
}
