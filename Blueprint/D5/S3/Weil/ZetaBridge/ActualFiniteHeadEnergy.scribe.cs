using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualFiniteHeadEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite arithmetic heads and complete tail energy", H("Finite arithmetic heads and complete tail energy"),
        Blocks(
            Paragraph(Text("For every natural c>=3, finite integer head S, natural cutoff N and complex coefficient function v, the complete paired tail energy is zero exactly when v vanishes on S. The empty head and zero vector are included; values outside S play no role.")),
            Paragraph(Text("The positive mean square of the actual prime symbol controls the reciprocal Q energy. The nodal reconstruction formula makes Q nonzero whenever a retained coefficient is nonzero. Reversal and dilation preserve this property at a positive cutoff.")),
            Paragraph(Text("The explicit 336 uniform enclosure chooses a cutoff before the coefficient vector. Its lower inequality gives positive energy without dividing by an energy or a coefficient mass. Nonnegative tail cropping then transfers positivity to every original cutoff, including zero.")),
            Paragraph(Text("This concerns the actual arithmetic divided-difference columns. It gives neither injectivity on all integer-indexed functions nor a uniform positive constant independent of cutoff. It does not identify the full physical Weil operator or assert RH or Robin.")),
            Describe.Lean(DescribeId.Create("actual-tail-summable-all"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_tail_summable_all"),
                H("actual tail summable all"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) : Summable (pairedColumnTerm c N S v)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-finite-head-tail-pos"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_pos"),
                H("actual finite head tail pos"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) : 0 < ∑' j : ℕ, pairedColumnTerm c N S v j"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-finite-head-tail-zero-iff"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFiniteHeadEnergy.actual_finite_head_tail_zero_iff"),
                H("actual finite head tail zero iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) : (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0"))), DescribeRole.Theorem))));
}
