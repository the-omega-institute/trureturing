using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionWeightedNonregularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionWeightedNonregularity",
        H("HalvingPartitionWeightedNonregularity"),
        Blocks(
            Paragraph(Text("These results preserve the actual SourceLists count, including repeated terminal ones and the unique empty list at zero. The dyadic enumeration specializes Alekseyev (2026), Theorem 5. The ring, weighted, representation-base and statistical scope follows the written note by Haobo Ma then Wenlin Zhang (7 November 2026, CC BY 4.0). No global novelty or independent final acceptance is asserted.")),
            Node("weightedTail", "The r-th dyadic tail contribution is present at its threshold, with the first two exponents equal to zero. Natural subtraction is intentional.", DescribeRole.Definition),
            Node("weightedCount_bounded", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedDifference", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("weightedDifference_impulses", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedDifference_jump", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedDifference_after_jump", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedDifference_gap", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weighted_nonregularity", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weighted_powerBase_nonregularity", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem))));

    private static string Exact(string name) => name switch
    {
        "weightedTail" => "Exact source statement: def weightedTail (t : R) (m r : ℕ) : R := if 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m then t ^ (m - r - 2 ^ r - 2) else 0",
        "weightedCount_bounded" => "Exact source statement: theorem weightedCount_bounded (t : R) (m L : ℕ) (hm : 2 ≤ m) (hL : m < L) : weightedCount t (2 ^ m + 1) = t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) + ∑ r ∈ Finset.range L, weightedTail t m r",
        "weightedDifference" => "Exact source statement: noncomputable def weightedDifference (t : R) (m : ℕ) : R := weightedCount t (2 ^ (m + 1) + 1) - t * weightedCount t (2 ^ m + 1) open Classical in",
        "weightedDifference_impulses" => "Exact source statement: theorem weightedDifference_impulses (t : R) (m : ℕ) (hm : 3 ≤ m) : weightedDifference t m = ∑ r ∈ Finset.range (m + 2), if 1 ≤ r ∧ 2 ^ r + r = m then 1 else if 1 ≤ r ∧ 2 ^ r + r + 1 = m then 1 - t else 0",
        "weightedDifference_jump" => "Exact source statement: theorem weightedDifference_jump (t : R) (r : ℕ) (hr : 1 ≤ r) : weightedDifference t (2 ^ r + r) = 1",
        "weightedDifference_after_jump" => "Exact source statement: theorem weightedDifference_after_jump (t : R) (r : ℕ) (hr : 1 ≤ r) : weightedDifference t (2 ^ r + r + 1) = 1 - t",
        "weightedDifference_gap" => "Exact source statement: theorem weightedDifference_gap (t : R) (m r : ℕ) (hr : 1 ≤ r) (hlo : 2 ^ r + r + 1 < m) (hhi : m < 2 ^ (r + 1) + (r + 1)) : weightedDifference t m = 0",
        "weighted_nonregularity" => "Exact source statement: theorem weighted_nonregularity [Nontrivial R] (t : R) : ¬ BinaryDecimation.MatrixFamily (weightedCount t)",
        "weighted_powerBase_nonregularity" => "Exact source statement: theorem weighted_powerBase_nonregularity [Nontrivial R] (t : R) (h : ℕ) (hh : 1 ≤ h) : ¬ BinaryDecimation.BaseFamily (2 ^ h) (weightedCount t)",
        _ => name
    };

    private static DocumentBlock Node(string name, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionweightednonregularity-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose)), Paragraph(Text(Exact(name)))), role);
}
