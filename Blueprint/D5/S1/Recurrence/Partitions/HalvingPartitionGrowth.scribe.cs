using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionGrowth", H("HalvingPartitionGrowth"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("R_m counts every positive threshold 2^r+r+1≤m. For m≥4, floor(log_2 m)+2≤a(2^m+1)≤floor(log_2 m)+3. The ordinary real logarithm is Real.logb 2; the bounded absolute error yields the standard atTop O(1) assertion. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("thresholdCount_log_bounds", "Exact source declaration: theorem thresholdCount_log_bounds (m : ℕ) (hm : 4 ≤ m) : Nat.log2 m - 1 ≤ thresholdCount m ∧ thresholdCount m ≤ Nat.log2 m", DescribeRole.Theorem),
            Node("dyadic_count_log_bounds", "Exact source declaration: theorem dyadic_count_log_bounds (m : ℕ) (hm : 4 ≤ m) : Nat.log2 m + 2 ≤ count (2 ^ m + 1) ∧ count (2 ^ m + 1) ≤ Nat.log2 m + 3", DescribeRole.Theorem),
            Node("dyadic_count_real_log_bound", "Exact source declaration: theorem dyadic_count_real_log_bound (m : ℕ) (hm : 4 ≤ m) : |(count (2 ^ m + 1) : ℝ) - Real.logb 2 m| ≤ 3", DescribeRole.Theorem),
            Node("dyadic_count_log_isBigO", "Exact source declaration: theorem dyadic_count_log_isBigO : Asymptotics.IsBigO Filter.atTop (fun m : ℕ => (count (2 ^ m + 1) : ℝ) - Real.logb 2 m) (fun _ : ℕ => (1 : ℝ))", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitiongrowth-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
