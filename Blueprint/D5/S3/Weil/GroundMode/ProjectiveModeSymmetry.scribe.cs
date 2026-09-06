using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GroundMode;

internal sealed class ProjectiveModeSymmetryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Candidate source; Lean elaboration and Scribe emission are not claimed.",
        H("ProjectiveModeSymmetry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projectivemodesymmetry-normalized-eigenvectors-unique"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/ProjectiveModeSymmetry.normalized_eigenvectors_unique"),
                H("normalized eigenvectors unique"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtract the two domain eigenvectors. Their equal candidate normalization makes the difference orthogonal. The existing below-threshold nonzero-overlap theorem excludes a nonzero difference. No prior simplicity or bounded extension is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projectivemodesymmetry-normalized-mode-fixed-by-semilinear-symmetry"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/ProjectiveModeSymmetry.normalized_mode_fixed_by_semilinear_symmetry"),
                H("normalized mode fixed by semilinear symmetry"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Commutation on the domain and Hilbert space preserves the eigenvalue equation. Inner-product compatibility and candidate fixedness preserve normalization. Apply the proved uniqueness. Conjugation and linear reflection are applications after their actual domain compatibility is supplied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("projectivemodesymmetry-projective-eigenmode-fixed-by-semilinear-symmetry"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/ProjectiveModeSymmetry.projective_eigenmode_fixed_by_semilinear_symmetry"),
                H("projective eigenmode fixed by semilinear symmetry"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derive nonzero overlap with the existing owner, construct the actual normalized eigenvector and apply the preceding symmetry theorem. Real or even behavior is a consequence for a compatible symmetry; it is not inferred just from proximity to a real even candidate."))),
                DescribeRole.Theorem))));
}
