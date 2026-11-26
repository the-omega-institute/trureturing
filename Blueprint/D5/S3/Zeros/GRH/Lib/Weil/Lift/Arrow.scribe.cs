using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Lift;

internal sealed class ArrowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arrow", H("Arrow"),
        Blocks(
            Paragraph(Text("Theta lift on forms: equivariance, adjoint, matched real data lift types to types.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Lift/Arrow.inner_formLift_adjoint"),
                H("inner_formLift_adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If φ is an arrow e → e' and, for the swapped pair, an arrow between the conjugate types, then ⟨x, L_φ y⟩ = ⟨conj(D_φ conj(x)), y⟩: the adjoint of the lift is the conjugate of the descent.")))))));
}
