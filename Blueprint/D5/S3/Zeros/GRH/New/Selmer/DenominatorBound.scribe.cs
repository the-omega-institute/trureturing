using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class DenominatorBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Denominator Bound", H("Denominator Bound"),
        Blocks(
            Paragraph(Text("Denominator of projection to theta lifts bounded without the even classes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/DenominatorBound.denominatorLe_rowBudget"),
                H("denominatorLe_rowBudget"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Q be auxiliary, the avatar ψ of ϑ⁻¹ anticyclotomic, Σ_Q v(ψ(γ) − 1) ≤ cr for tame generators γ, β = rowBudget. A cut spanned by lifts whose rows T have Sel_M(Tψ) of length ≤ (10fr + 1)cr, M = ⌊D.r·β⌋ + 1, has denominator ≤ rβ log ℓ.")))))));
}
