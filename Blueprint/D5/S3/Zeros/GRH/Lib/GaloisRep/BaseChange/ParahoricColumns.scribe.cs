using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class ParahoricColumnsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parahoric Columns", H("Parahoric Columns"),
        Blocks(
            Paragraph(Text("Local matching of pro-p Iwahori double cosets of t and its norm. Sums over columns of a parahoric, counting vectors by last non-zero coordinate.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/ParahoricColumns.exists_line_orbit_sums"),
                H("exists_line_orbit_sums"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P ⊂ GL_N(𝒪) have columns before m in 𝔭 below the diagonal, x be fixed by the p ∈ P with column m in 𝔭 off the diagonal, φ Iwahori-invariant, a_j = (q−1)q^j φ((m j)x), indices from 0. Some P-fixed y has φ(y) = ∑_{j≥m} a_j; some z, fixed by the p ∈ P with row m in 𝔭 off the diagonal, has φ((m i)z) = a_i + (1−1/q)∑_{j>i} a_j for i ≥ m.")))))));
}
