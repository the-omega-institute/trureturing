using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class NamesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Names", H("Names"),
        Blocks(
            Paragraph(Text("Schrödinger model at split places embedded in the vacuum model: Heisenberg action, inner products.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/Names.dataInner_name"),
                H("dataInner_name"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For S disjoint from its conjugate and Ψ, Ψ′ Schwartz–Bruhat above S, ⟨Ψ ⊗ f, Ψ′ ⊗ f′⟩ equals the inner product of Ψ and Ψ′ above S times ⟨P^S f, P^S f′⟩.")))))));
}
