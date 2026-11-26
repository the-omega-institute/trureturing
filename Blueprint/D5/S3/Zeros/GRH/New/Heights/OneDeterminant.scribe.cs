using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Heights;

internal sealed class OneDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One Determinant", H("One Determinant"),
        Blocks(
            Paragraph(Text("Positive-type functions avoid singular minors; Hilbert-Schmidt variance inequality giving spread. Few translates nearly span; height bound for a ratio of Gram determinants.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Heights/OneDeterminant.one_determinant"),
                H("one_determinant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("One determinant. Let x be a basis of W, u o injective, all conjugates of the Gram determinant of u o ∘ x of modulus ≤ exp α, γ nonzero with |γ|⁻² of height ≤ g, all finite sums of e at most δ. If for all ι at l and j : ℂ → ℂ_l the pairing of Λ ι (j∘conj) with Λ ι j is j-integral and a complex matrix m with |j(det m)| ≥ exp(−e l)·|j(γ ι)|^k recombines u (θ ι) ∘ x into Λ ι j, then the squared-volume ratios of u (θ ι) to u o have height ≤ α + 2δ + kg.")))))));
}
