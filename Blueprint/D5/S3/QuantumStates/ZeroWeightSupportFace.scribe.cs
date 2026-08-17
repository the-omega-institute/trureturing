using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumStates;

internal sealed class ZeroWeightSupportFaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero projection weight confines a positive matrix to the complementary support.",
        H("Zero-Weight Support Face"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-weight-support-face"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumStates/ZeroWeightSupportFace."
                        + "zero_weight_support_face"),
                H("Zero projection weight exposes a support face"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
                    Sp, Land, Sp,
                    F.Id("P"), Caret, Grp(Star), Sp, Eq, Sp, F.Id("P"),
                    Sp, Land, Sp,
                    F.Id("P"), Caret, Grp(D(2)), Sp, Eq, Sp, F.Id("P"),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Tr")), Open, Rho, Thin, F.Id("P"),
                    Close, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
                    Open, F.Id("P"), Thin, Rho, Sp, Eq, Sp, D(0), Sp,
                    Land, Sp, Rho, Thin, F.Id("P"), Sp, Eq, Sp, D(0), Close,
                    Sp, Land, Sp,
                    Rho, Sp, Eq, Sp,
                    Open, F.Id("I"), Sp, Minus, Sp, F.Id("P"), Close,
                    Thin, Rho, Thin,
                    Open, F.Id("I"), Sp, Minus, Sp, F.Id("P"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let rho be a positive semidefinite complex matrix and P a self-adjoint "
                            + "idempotent matrix. If the trace weight Tr(rho P) vanishes, then both "
                            + "one-sided products P rho and rho P vanish.")),
                    Paragraph(Text(
                        "The proof first compresses rho by P. The compression is positive "
                            + "semidefinite and has zero trace, so Mathlib's trace-zero theorem "
                            + "makes it zero. A positive factorization of rho then turns this into "
                            + "the two one-sided annihilations.")),
                    Paragraph(Text(
                        "Expanding the complementary compression and using those annihilations "
                            + "gives rho = (I-P) rho (I-P). No trace-one normalization or "
                            + "finite-rank restriction on the projection is required."))),
                DescribeRole.Theorem))));
}
