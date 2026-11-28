using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Lift;

internal sealed class EdgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Edge", H("Edge"),
        Blocks(
            Paragraph(Text("Theta lifts with joint harmonic data carry discrete series forms to the corresponding type.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Lift/Edge.isEdge_jointHarmonic"),
                H("isEdge_jointHarmonic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let n, n' ≥ 1. If l, l' correspond for the weights γ, γ' and signs s, t, the Fock vector of the product jointHarmonic of joint harmonics is an edge e_l → e_{l'} for the real Weil representation of weights γ, γ'.")))))));
}
