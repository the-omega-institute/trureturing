using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters.FourCurrent;

internal sealed class TraceRecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original signed four-current finite recurrence.",
        H("Original signed four-current finite recurrence"),
        Blocks(
            Describe.Lean(DescribeId.Create("four-current-finite-recurrence"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/FourCurrent/TraceRecurrence.original_four_finite_sum"),
                H("Original signed four-current finite recurrence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original lattice D with positive-definite real Gram matrix, labels i : Fin 4 → Fin D.rank and natural grades n : Fin 4 → Nat with n(0) < n(1), put ell=n(1)-n(0), p=n(2)-n(1), q=n(3)-n(2), r=n(0)-n(3), with the latter differences in the integers. The literal original four-block trace is the sum over a=0,...,floor(n(0)/ell) of the three labeled CCR contractions times the corresponding original two-mode word trace at the signed grade n(0)-a ell. The factors are ell times the signed Gram entry when the contracted modes sum to zero, and zero otherwise."))), DescribeRole.Theorem),
            Paragraph(Text("The module owns the literal original complete-grade trace, all ten labeled matchings and their bounded coefficient, zero-mode basis trace, signed homogeneity and rectangular finite trace cyclicity. Original positive energy kills every negative grade. The signed four-current commutator and finite telescoping proof are used by the matching-mode coefficient reduction; they impose no substitute CCR or trace assumption. Zero and equal grades, repeated labels, signed Gram entries and rank zero remain part of the definitions and of the subsequent endpoint.")))));
}
