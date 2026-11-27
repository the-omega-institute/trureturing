using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicRankTwoCutDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicRankTwoCut.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixing even occupation and charge gives sharp lower bounds on both directed CAR cut weights.",
        H("Sharp rank-two occupation cut"),
        Blocks(
            Entry("cut-weight-ge-sqrt", "cutWeight_ge_sqrt", "Lower bounds in both directions",
                "In a complex unitary frame, let a and b be the empty and full masses of columns 0 and 1. " +
                "Write t = a+b−1 for the even occupation offset and g = a−b for the empty-minus-full charge. " +
                "The weight from columns 0 and 1 to columns 2 and 3 is at least " +
                "L₋ = 1+t²−g−2√(ab(1−a)(1−b)). The opposite direction is at least " +
                "L₊ = 1+t²+g−2√(ab(1−a)(1−b)). Bounding the product of the even and odd minors gives " +
                "the square-root term. Each L± is at least (1±g)²/2 + 3t²/2, which improves the " +
                "one-parameter projection bound (1±g)²/2 strictly whenever t is nonzero."),
            Entry("cut-weight-sqrt-attained", "cutWeight_sqrt_attained", "Simultaneous attainment",
                "For every a,b ∈ [0,1], one unitary frame realizes those two masses and simultaneously " +
                "attains L₋ and L₊ in their respective directions. Thus the two occupations, or equivalently " +
                "the even offset and charge, can be fixed throughout the minimization."),
            Entry("reverse-cubic-penalty-ge-sqrt", "reverseCubicPenalty_ge_sqrt", "Reverse cubic penalty",
                "Write wⱼᵢ for the summed squared lowering amplitudes from column i to column j. " +
                "For any monotone real tuple u₀ ≤ u₁ ≤ u₂ ≤ u₃, the reverse-edge sum " +
                "∑ᵢ<ⱼ wⱼᵢ(uⱼ−uᵢ)³ is at least (u₂−u₁)³ L₋. Every crossing edge has gap " +
                "at least u₂−u₁, and each of the two within-pair terms is nonnegative."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
