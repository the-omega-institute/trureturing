using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseMemorySaturatedFrameDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseMemorySaturatedFrame.";
    private static LibraryNoteRef GramCriterion => LibraryNoteRef.Create("D5/L/Resource/cheflesjozsawinter2004transformations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality constraints for the clipped guessing bound with one finite quantum memory.",
        H("Saturated phase-memory equality"),
        Blocks(
            Paragraph(Text("A single CPTP channel receives the unknown quantum signal and sends an M-dimensional quantum system to the decoder. One POVM acts on that system alone. Visible encoding uses the classical label as input. An instrument with a retained classical outcome can also give the decoder a branch-dependent measurement. Those models have different feasible strategies.")),
            Describe.Lean(DescribeId.Create("saturated-phase-memory-canonical-effects"),
                DeclarationHandle.Create(Module + "saturated_local_effects_canonical"),
                H("Equality fixes the compressed effects and one column of the pullbacks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write the physical amplitudes as tᵢ = rᵢaᵢ with 0 < aᵢ ≤ 1 and Σᵢaᵢ² = M. The slopes satisfy rᵢ ≥ τ > 0, with rᵢ = τ wherever aᵢ < 1. At a saturated coordinate k, aₖ = 1. Dephase that column to one and assume the other column sums vanish and the vectors wⱼ = a · uⱼ are linearly independent. Positive amplitudes and a square orthogonal flat phase matrix give these independence and column-sum properties after dephasing.")),
                    Paragraph(Text("Equality in the weighted rank-one estimate forces each score-preserving local effect to be a multiple of |wⱼ⟩⟨wⱼ|. These multiples sum to one. The aggregate effect has the same k-th column as the identity because the positive semidefinite slack has zero k-th diagonal entry. Independence gives the common multiple 1/N. The same zero-diagonal argument for the individual positive slacks gives Eⱼ(:,k) = Fⱼ(:,k)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saturated-phase-memory-dimension"),
                DeclarationHandle.Create(Module + "saturated_channel_equality_card_le_memory_sq"),
                H("A saturated equality strategy needs N ≤ M²"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For normalized inputs the spectral per-effect witness supplies score preservation and bounds the trace by that of the corresponding decoder effect. The pulled-back columns are independent at equality, so the decoder effects are complex-linearly independent in the M by M matrix space. The dimension bound concerns equality in the clipped guessing score."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saturated-phase-memory-projector-gram"),
                DeclarationHandle.Create(Module + "threshold_projector_gram"),
                H("At N = M² the decoder effects form a tight projector frame"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(GramCriterion),
                Blocks(
                    Paragraph(Text("For normalized virtual vectors vⱼ = wⱼ/√M, the common dephased coordinate is 1/√M. Rank-one domination in the Stinespring pullback forces each decoder trace to be at least M/N. Since the traces sum to M, each trace equals M/N and each effect is (M/N)Qⱼ for a unit rank-one projector Qⱼ. The Qⱼ sum to (N/M)I.")),
                    Paragraph(Text("The canonical columns intertwine the decoder action with the virtual vectors. At N = M² the Qⱼ span the full matrix space. The induced functional on matrices equals the normalized trace, so ⟨vⱼ,vₗ⟩ = Tr(QⱼQₗ). In particular, each entry is real and nonnegative. Chefles, Jozsa and Winter provide related pure-state transformation background. The equality argument here derives the projector frame from the guessing score."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saturated-fourier-four-nonattainment"),
                DeclarationHandle.Create(Module + "fourier4_dominant_ne_upper"),
                H("An asymmetric dominant Fourier ensemble cannot attain the clipped bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(GramCriterion),
                Blocks(Paragraph(Text("For tᵢ > 0, Σᵢtᵢ² = 1 and t₀² ≥ 1/2, the clipped amplitudes are a₀ = 1 and aᵢ = tᵢ/r for i > 0, where r = √(t₁² + t₂² + t₃²). With uⱼᵢ = i to the power ji, the imaginary part of the normalized virtual Gram entry (0,1) is (a₁² − a₃²)/2. If t₁ ≠ t₃, this contradicts the projector Gram required for a qubit equality strategy."))),
                DescribeRole.Theorem))));
}
