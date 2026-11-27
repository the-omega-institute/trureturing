using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class VolumeKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Volume Kernel", H("Volume Kernel"),
        Blocks(
            Paragraph(Text("Frames with equal Gram block and congruent middle parts are lattice translates. Volume weight for the Schur test, dominated by a kernel with Hua-type integral bound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/VolumeKernel.exists_kernel_frameVolume_le"),
                H("exists_kernel_frameVolume_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Fix besselSize y ≤ θ, e: σ ↪ j, V; R, z = Z_j (leading block) invertible. Some measurable K has ∫K ≤ ((2θ²)^j/|det z|)^(k+n)(π^|σ|/(|σ|!θ^{2|σ|}|det R|²))^k, and (Δ(y)/Δ(γ⁻¹y))^(k+n) ≤ K(A) whenever Z(γ) = Z, IsNormalForm j γ, and γf₁, …, γf_j have X₀-components V + (AR,0)z.")))))));
}
