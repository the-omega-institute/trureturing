using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori;

internal sealed class HeckeCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Counts", H("Hecke Counts"),
        Blocks(
            Paragraph(Text("Degree of I t I; spherical T_j acts on exponents by elementary symmetric functions.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/HeckeCounts.partialHecke_dual"),
                H("partialHecke_dual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Duality of lattices. Let T^r_j sum over the cosets in partialCosets r j, x be GL_N(𝒪_w)-fixed, r + i + j = N. Then T^r_j for the representation g ↦ ρ((gᵀ)⁻¹) sends x to ρ(diag(1_r, ϖ⁻¹1_{N−r})) T^r_i x, with T^r_i taken for ρ.")))))));
}
