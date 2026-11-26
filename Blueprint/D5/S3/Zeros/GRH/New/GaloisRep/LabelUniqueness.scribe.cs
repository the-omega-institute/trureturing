using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.GaloisRep;

internal sealed class LabelUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label Uniqueness", H("Label Uniqueness"),
        Blocks(
            Paragraph(Text("Given an injective lift to forms on a definite group, a Hecke eigensystem has at most one primitive label at a chosen place over g.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/GaloisRep/LabelUniqueness.occurringLabels_subsingleton"),
                H("occurringLabels_subsingleton"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let L inject level g forms on V into definite algebraic forms, make the p-part spherical with fixed eigenvalues at split places off g, and intertwine the parabolic action at x up to ψ∘det and distinct χ_l∘det, of orders dividing Mω. Then Data.occurringLabels V p x has at most one element.")))))));
}
