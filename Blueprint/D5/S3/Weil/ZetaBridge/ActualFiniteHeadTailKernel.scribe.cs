using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualFiniteHeadTailKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete finite-head tail kernel at every cutoff", H("Complete finite-head tail kernel at every cutoff"),
        Blocks(
            Paragraph(Text("For every natural c>=3, finite integer head S, natural cutoff N and complex coefficient function v, the complete paired tail energy vanishes exactly when v vanishes on S. The empty head and zero vector are included.")),
            Paragraph(Text("ActualUniformFiniteHeadTail.actual_finite_head_uniform_tail_lower provides the coefficient-uniform lower bound for c>=2: positive C and a cutoff N0 are chosen before all coefficient functions and all later cutoffs. Its summability at N+N0, reindexing of both signed columns and Summable.comp_nat_add give summability at every N.")),
            Paragraph(Text("A retained nonzero coefficient gives strictly positive original coefficient mass. The uniform lower bound gives a positive complete tail at max(N,N0), and nonnegative tail cropping transfers positivity to N. This is a consequence of the uniform estimate; ActualThreeNodeSourceHeadBridge uses that consequence on the literal three-node head.")),
            Describe.Lean(DescribeId.Create("actual-tail-summable-all"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_tail_summable_all"),
                H("actual tail summable all"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma actual_tail_summable_all {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hS : S.Nonempty) (N : ℕ) (v : ℤ → ℂ) : Summable (pairedColumnTerm c N S v)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-finite-head-tail-pos"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_pos"),
                H("actual finite head tail pos"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem actual_finite_head_tail_pos {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0) : 0 < ∑' j : ℕ, pairedColumnTerm c N S v j"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-finite-head-tail-zero-iff"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualFiniteHeadTailKernel.actual_finite_head_tail_zero_iff"),
                H("actual finite head tail zero iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem actual_finite_head_tail_zero_iff {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ) : (∑' j : ℕ, pairedColumnTerm c N S v j) = 0 ↔ ∀ k ∈ S, v k = 0"))), DescribeRole.Theorem))));
}
