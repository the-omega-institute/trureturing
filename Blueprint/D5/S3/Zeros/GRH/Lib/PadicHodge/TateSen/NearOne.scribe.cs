using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.TateSen;

internal sealed class NearOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Near One", H("Near One"),
        Blocks(
            Paragraph(Text("Tate: normalised trace bounded on cyclotomic tower; H^0 of C_p(i) vanishes. Filter near 1, fixed field, embeddings of Q̄_p into C_p are Galois elements.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/TateSen/NearOne.le_of_hodgeTate_stable"),
                H("le_of_hodgeTate_stable"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("F a filter of neighbourhoods of 1 in G_p, ι finite; each a ∈ W ⊂ C_p^ι has (χ(g)^u_i·g a_i) ∈ W for F-almost all g. Then W ⊂ W' once W' contains each integral a ∈ W over Q̄_p, F-almost fixed, with some a_k = 1, a_i = 0 if u_i ≠ u_k.")))))));
}
