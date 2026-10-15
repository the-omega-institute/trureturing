using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzSpectralCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual support coordinates of Petz recovery.",
        H("Actual support coordinates of Petz recovery"), Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-petz-coordinate-matrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSpectralCoordinates.spectral_petz_coordinate_matrix"),
                H("Inverse-square-root modular coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("The positive-support relative modular coordinate matrix at B^(-1/2) eta is exactly "
                        + "Q^(-1/2) sqrt(T), using the spectral pseudoinverse on the kernel. The proof handles "
                        + "repeated eigenvalues and actual finite CFC coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-input-support-columns"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSpectralCoordinates.petz_input_support_columns"),
                H("Reconstruct the input support columns"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("The positive input eigenbasis coordinate identities imply sqrt(S) Psi(Y) P_R = sqrt(R). "
                        + "The actual input kernel containment supplies the zero-eigenvalue coordinates. This "
                        + "supported identity is consumed by Schwarz trace rigidity; it is not promoted to an "
                        + "unsupported full-space equality."))),
                DescribeRole.Theorem))));
}
