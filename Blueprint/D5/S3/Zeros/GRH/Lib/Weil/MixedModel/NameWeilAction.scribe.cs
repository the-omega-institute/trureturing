using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class NameWeilActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Name Weil Action", H("Name Weil Action"),
        Blocks(
            Paragraph(Text("Coordinate changes keeping the vacuum intertwine Heisenberg and Weil operators (negation, conjugation). Schrödinger data are compatible with direct sums and changes of space. Weil action in the Schrödinger model at split finite places; products over disjoint places.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/NameWeilAction.ω_name_on"),
                H("ω_name_on"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let S be disjoint from its conjugate and Ψ Schwartz–Bruhat on S. For a finite unitary g supported on S ∪ S̄, ω(g)(Ψ⊗f) = υ(det g_S)⁻¹ |det g_S|^(−1/2) Ψ(g⁻¹·)⊗f.")))))));
}
