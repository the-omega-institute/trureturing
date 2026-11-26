using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzSupportedLinearRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary Petz squared trace error is bounded by the actual Umegaki loss with coefficient 4(ν₊(T) + ν₊(Q) − 1).",
        H("Ordinary Petz recovery with a linear rank bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petzsupportedlinearrank-positivelevelcount"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSupportedLinearRank.positiveLevelCount"),
                H("Distinct positive eigenvalues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the eigenvalues of the density matrix on their positive spectral indices and count the elements of the image."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzsupportedlinearrank-ordinary-petz-tracenorm-sq-le-four-linear-rank"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSupportedLinearRank.ordinary_petz_traceNorm_sq_le_four_linear_rank"),
                H("The finite CPTP ordinary Petz bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(Paragraph(Text("For every finite CPTP channel Φ and reference density state σ, let Q = Φ(σ) and P be its support projection. The theorem gives the ordinary Petz channel with the actual Kraus adjoint and the inverse square root of Q on its positive spectrum. Its extension on the kernel adds Tr((I − P)X) σ to the action on X. It recovers σ exactly. For every ρ supported in σ, that extension contributes zero at T = Φ(ρ). The squared trace norm of ρ minus the recovered T is at most 4(ν₊(T) + ν₊(Q) − 1) Δ and at most 4(2 rank Q − 1) Δ, where Δ = D(ρ ∥ σ) − D(T ∥ Q) uses the actual finite trace-log relative entropies and ν₊ counts distinct positive eigenvalues.")),
                    Paragraph(Text("The actual Stinespring amplitudes realize both supported strip deficits. Their reflected cross term survives the input support projections. The midline identity gives the full logistic energy bound, the mixed eigenbasis gives the distinct-level coefficient, and the endpoint Gram is the ordinary recovered state."))),
                DescribeRole.Theorem))));
}
