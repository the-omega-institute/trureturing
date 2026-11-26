using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class BoxPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Box Partition", H("Box Partition"),
        Blocks(
            Paragraph(Text("Positive form on links, lifts to the lattice, dimension and isotropy of links. Primes where agreeing frames meet divide a determinant; integral Eichler lifts. Integral Eichler transformations give elements of the level-g unipotent group of a class. Covering lemmas for weighted sums; counting bounded integral vectors; index of a scaled lattice. Definitions of indices, discriminants, gauges and class representatives for the crude bounds. Boxed cutoffs for the arithmetic unipotent group and packing count of boxed frames.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/BoxPartition.tsum_classCutoff_box_le"),
                H("tsum_classCutoff_box_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Frame count: let w_p ≤ β_{k_p}(δ_p⁻¹y')·x, with p ↦ (k_p, δ_p) injective. If, where w_p ≠ 0, γ_p ∈ δ_p𝖴_{k_p}(g) lies over (c,s,k_p), γ_p⁻¹y ∈ Filling.boxedPoints, and the frames y⁻¹γ_pf differ in a real subspace V, then ∑w_p ≤ b^(6(ϱ+1)² dim V)·x.")))))));
}
