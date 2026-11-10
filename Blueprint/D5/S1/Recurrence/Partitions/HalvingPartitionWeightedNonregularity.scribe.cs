using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionWeightedNonregularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionWeightedNonregularity", H("HalvingPartitionWeightedNonregularity"), Blocks(
            Paragraph(Text("The full binary and power-base weighted audits compile their realization, variation, sensitivity and dependence proofs, but current source binding is declared_unresolved with IE-C050 source.dictionary_or_proof_coordinate. The other new public audits in this owner remain missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("All weighted results hold for every nonzero commutative unital ring R, including positive characteristic and zero divisors, and every t in R. The weighted difference has impulses 1 and 1-t for m≥3. The separately proved unweighted difference includes m=2 and gives exactly 2^r consecutive zeros between jumps. The monic recurrence contradiction never divides by t or a recurrence coefficient. The representation base ranges over every 2^h with h≥1. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("weightedTail", "Exact source declaration: def weightedTail (t : R) (m r : ℕ) : R := if 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m then t ^ (m - r - 2 ^ r - 2) else 0", DescribeRole.Definition),
            Node("weightedCount_bounded", "Exact source declaration: theorem weightedCount_bounded (t : R) (m L : ℕ) (hm : 2 ≤ m) (hL : m < L) : weightedCount t (2 ^ m + 1) = t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) + ∑ r ∈ Finset.range L, weightedTail t m r", DescribeRole.Theorem),
            Node("weightedDifference", "Exact source declaration: noncomputable def weightedDifference (t : R) (m : ℕ) : R := weightedCount t (2 ^ (m + 1) + 1) - t * weightedCount t (2 ^ m + 1)", DescribeRole.Definition),
            Node("weightedDifference_impulses", "Exact source declaration: theorem weightedDifference_impulses (t : R) (m : ℕ) (hm : 3 ≤ m) : weightedDifference t m = ∑ r ∈ Finset.range (m + 2), if 1 ≤ r ∧ 2 ^ r + r = m then 1 else if 1 ≤ r ∧ 2 ^ r + r + 1 = m then 1 - t else 0", DescribeRole.Theorem),
            Node("weightedDifference_jump", "Exact source declaration: theorem weightedDifference_jump (t : R) (r : ℕ) (hr : 1 ≤ r) : weightedDifference t (2 ^ r + r) = 1", DescribeRole.Theorem),
            Node("weightedDifference_after_jump", "Exact source declaration: theorem weightedDifference_after_jump (t : R) (r : ℕ) (hr : 1 ≤ r) : weightedDifference t (2 ^ r + r + 1) = 1 - t", DescribeRole.Theorem),
            Node("weightedDifference_gap", "Exact source declaration: theorem weightedDifference_gap (t : R) (m r : ℕ) (hr : 1 ≤ r) (hlo : 2 ^ r + r + 1 < m) (hhi : m < 2 ^ (r + 1) + (r + 1)) : weightedDifference t m = 0", DescribeRole.Theorem),
            Node("count_difference", "Exact source declaration: theorem count_difference (m : ℕ) (hm : 2 ≤ m) : (count (2 ^ (m + 1) + 1) : R) - (count (2 ^ m + 1) : R) = if ∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r = m then 1 else 0", DescribeRole.Theorem),
            Node("count_difference_zero_block", "Exact source declaration: theorem count_difference_zero_block (r i : ℕ) (hr : 1 ≤ r) (hi : i < 2 ^ r) : (count (2 ^ (2 ^ r + r + 1 + i + 1) + 1) : R) - (count (2 ^ (2 ^ r + r + 1 + i) + 1) : R) = 0", DescribeRole.Theorem),
            Node("weighted_nonregularity", "Exact source declaration: theorem weighted_nonregularity [Nontrivial R] (t : R) : ¬ BinaryDecimation.MatrixFamily (weightedCount t)", DescribeRole.Theorem),
            Node("weighted_powerBase_nonregularity", "Exact source declaration: theorem weighted_powerBase_nonregularity [Nontrivial R] (t : R) (h : ℕ) (hh : 1 ≤ h) : ¬ BinaryDecimation.BaseFamily (2 ^ h) (weightedCount t)", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionweightednonregularity-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
