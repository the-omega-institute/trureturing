using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.Dual;

internal sealed class MixedCartanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed Cartan", H("Mixed Cartan"),
        Blocks(
            Paragraph(Text("Integral isometric Cartan component of a Weyl module tensor a dual Weyl module.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/Dual/MixedCartan.nonempty_mixedCartanEmbedding"),
                H("nonempty_mixedCartanEmbedding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Duality for Weyl lattices: for all column counts kp and km, a map PolyRep.MixedCartanEmbedding exists from the lattice with column counts kp_τ(i) + km_τ(|n| − i) to Δ_kp ⊗ Δ_km, that is, an equivariant integral isometry with integral left inverse sending ev₁ to ev₁ ⊗ ev_{w₀}.")))))));
}
