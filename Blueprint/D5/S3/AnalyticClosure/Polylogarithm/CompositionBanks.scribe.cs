using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionBanksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive composition and positive reciprocal power has its source-faithful "
        + "endpoint and strict conjugate banks on a sufficiently small closed half-collar.",
        H("CompositionBanks"), Blocks(
            Describe.Lean(DescribeId.Create("complete-composition-banks-bridge"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/Polylogarithm/CompositionBanks.result"),
                H("Endpoint limits and strict conjugate banks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text(
                        "For every positive head, positive-entry tail and positive power ell, "
                        + "the theorem uses the actual continued source branch and its depth-normalized "
                        + "reciprocal power A. It produces a real radius rho with 0<rho<1. On the "
                        + "intersection of the full principal slit domain with the closed rho-ball "
                        + "about one, the continued branch is nonzero. Along the full slit-domain "
                        + "filter at one, A tends to the reciprocal zeta power when the head is "
                        + "admissible, and to zero when the head is one.")),
                    Paragraph(Text(
                        "The same radius supports jointly chosen upper and lower functions continuous "
                        + "on the closed upper and lower half-collars. They agree with A wherever the "
                        + "corresponding half-collar lies in the slit domain, take the common endpoint "
                        + "value at one, and are related by complex conjugation throughout the lower "
                        + "closed half-collar. For every real t with 0<t<=rho, the upper boundary "
                        + "value at 1+t has strictly negative imaginary part. Thus the strict sign is "
                        + "proved on the entire punctured boundary interval supplied by rho, not only "
                        + "eventually or at a selected point.")),
                    Paragraph(Text(
                        "The proof combines source-weight induction, radial and arc integral control, "
                        + "leading-one polynomial transport, the ordinary-head step and local analytic "
                        + "representations of the actual branch. This is an intermediate analytic bridge "
                        + "with zero solved-problem credit. It does not assert a general power-log "
                        + "asymptotic. Its rho is local and composition-dependent; it does not supply the "
                        + "still-missing normalized extension on a fixed slit disk, the Taylor or formal-"
                        + "inverse coefficient identification, finite-contour transfer, or the all-j "
                        + "assembly required for Xu-Zhao Conjecture 1.3. The full conjecture remains open, "
                        + "with no resolution, novelty or priority claim."))),
                DescribeRole.Theorem))));
}
