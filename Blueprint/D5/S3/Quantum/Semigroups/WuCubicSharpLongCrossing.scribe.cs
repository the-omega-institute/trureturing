using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicSharpLongCrossingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicSharpLongCrossing.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp lower bound for the symmetric crossing of two columns in the signed two-mode CAR frame.",
        H("Sharp singleton-pair crossing"),
        Blocks(
            Paragraph(Text("In occupation order, the two jumps are E₀₂+E₁₃ and −E₀₁+E₂₃. " +
                "For wᵢⱼ, column ψⱼ is the source and column ψᵢ is the target. " +
                "The weight is the sum over the two jumps of |⟨ψᵢ,Jψⱼ⟩|². " +
                "Write W = wᵢⱼ+wⱼᵢ, and let t and s be the odd masses in coordinates 1 and 2 of ψᵢ and ψⱼ, respectively. " +
                "The angular certificate applies both bounds to columns 0 and 3 in the equal-cap cubic proof of Wu v1 (3.54).")),
            Entry("singleton-pair-weight-ge-radical", "singletonPairWeight_ge_radical", "Radical lower bound",
                "Set P = √((1−t)s) and Q = √(t(1−s)). For x = ψᵢ and y = ψⱼ, " +
                "the even and odd minors are E = x₀y₃−x₃y₀ and O = x₁y₂−x₂y₁. " +
                "Adding both directed weights gives W = P²+Q²+2 Re(conj(E)O). " +
                "Complex Cauchy–Schwarz in the two sectors gives |E|² ≤ (1−t)(1−s) and |O|² ≤ ts. " +
                "Consequently Re(conj(E)O) ≥ −|E||O| ≥ −PQ, so W ≥ (P−Q)²."),
            Entry("singleton-pair-weight-ge-product", "singletonPairWeight_ge_product", "Division-free product bound",
                "Since P²−Q² = s−t and (P+Q)² ≤ 2(P²+Q²) ≤ 2(t+s), " +
                "the radical bound implies 2(t+s)W ≥ (t−s)². At t+s = 0 both masses and both sides are zero."),
            Entry("singleton-pair-weight-radical-attained", "singletonPairWeight_radical_attained", "Attaining unitary columns",
                "For any t,s ∈ [0,1], take columns 0 and 1 to be √(1−t)e₀+√t e₁ and √(1−s)e₃−√s e₂. " +
                "Complete them with −√t e₀+√(1−t)e₁ and √(1−s)e₂+√s e₃ in the same two coordinate planes. " +
                "The resulting real orthonormal frame is unitary and has the prescribed odd masses. " +
                "The relative minus sign produces the amplitude Q−P from column 1 to column 0 under the first jump. " +
                "The other amplitude and both reverse amplitudes vanish, giving W = (P−Q)²."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
