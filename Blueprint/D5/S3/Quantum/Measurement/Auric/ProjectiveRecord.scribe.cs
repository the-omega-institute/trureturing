using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Auric;

internal sealed class ProjectiveRecordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coherent record of a complete projective measurement",
        H("The coherent record of a complete projective measurement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coherent-projective-record"),
                DeclarationHandle.Create("D5/S3/Quantum/Measurement/Auric/ProjectiveRecord.coherent_projective_record"),
                H("The joint state and its actual marginals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/watrous2018theory"),
                    LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(
                    Paragraph(Text("For a complete finite PVM (E_j), set Wψ = Σ_j E_jψ ⊗ |j⟩ and ω = WρW†. Orthogonality and completeness give W†W = I. The system marginal is Πρ = Σ_j E_jρE_j. The record marginal is diag(q), with q_j = Re Tr(E_jρ). The joint entropy equals S(ρ). If G = S(Πρ) − S(ρ), then I(S:R) = H(q) + G and S(R|S) = −G.")),
                    Paragraph(Text("Watrous Corollary 2.27 locates the finite-dimensional channel dilation. Proposition 5.19 supplies isometric entropy invariance, including singular states. The marginal calculation here uses the actual orthogonal projectors and the same joint state throughout."))),
                DescribeRole.Theorem))));
}
