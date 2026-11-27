using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class FloorKernelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Floor Kernels", H("Floor Kernels"),
        Blocks(
            Paragraph(Text("Laws of floor kernels; pairing on one floor is integral of next floor's pairings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/FloorKernels.pivotModulus_sq_le"),
                H("pivotModulus_sq_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Cauchy–Schwarz on floor l, for a kernel k (Level.IsPairingKernel). If |k_{l+1}(σg, σy)|² ≤ u(σg)v(σ) on H_l, with u, v measurable and u of mass ≤ K on near points (Level.FloorMassLe), then (∫|k_{l+1}(σg, σy)| dθ_l)² ≤ K ∫ v dθ_l.")))))));
}
