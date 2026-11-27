using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaGroup;

internal sealed class SectionLiftsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Section Lifts", H("Section Lifts"),
        Blocks(
            Paragraph(Text("Quasi-finiteness from ample pull-backs; identities for the pairing: ⟨x+y, z⟩ + ⟨x−y, z⟩ = 2⟨x, z⟩, ⟨mx, y⟩ = m⟨x, y⟩ for natural m, symmetry, and compatibility with additive maps; [m]*L = L^(m²). Maps on sections induced by isomorphisms of pulled-back line bundles; composition, uniqueness.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/SectionLifts.comp"),
                H("comp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Lifts compose: if Φ: H⁰(L) → H⁰(L') is pull-back along f followed by an isomorphism f^*L ≅ L', and Θ: H⁰(L') → H⁰(L'') likewise along g, then Θ∘Φ is such a map along f∘g: X'' → X.")))))));
}
