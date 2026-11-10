using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionGrowth",
        H("HalvingPartitionGrowth"),
        Blocks(
            Paragraph(Text("These results preserve the actual SourceLists count, including repeated terminal ones and the unique empty list at zero. The dyadic enumeration specializes Alekseyev (2026), Theorem 5. The ring, weighted, representation-base and statistical scope follows the written note by Haobo Ma then Wenlin Zhang (7 November 2026, CC BY 4.0). No global novelty or independent final acceptance is asserted.")),
            Node("thresholdCount_log_bounds", "The threshold count is either floor(log2 m)-1 or floor(log2 m).", DescribeRole.Theorem),
            Node("dyadic_count_log_bounds", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("dyadic_count_real_log_bound", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("dyadic_count_log_isBigO", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem))));

    private static string Exact(string name) => name switch
    {
        "thresholdCount_log_bounds" => "Exact source statement: theorem thresholdCount_log_bounds (m : ℕ) (hm : 4 ≤ m) : Nat.log2 m - 1 ≤ thresholdCount m ∧ thresholdCount m ≤ Nat.log2 m",
        "dyadic_count_log_bounds" => "Exact source statement: theorem dyadic_count_log_bounds (m : ℕ) (hm : 4 ≤ m) : Nat.log2 m + 2 ≤ count (2 ^ m + 1) ∧ count (2 ^ m + 1) ≤ Nat.log2 m + 3",
        "dyadic_count_real_log_bound" => "Exact source statement: theorem dyadic_count_real_log_bound (m : ℕ) (hm : 4 ≤ m) : |(count (2 ^ m + 1) : ℝ) - Real.logb 2 m| ≤ 3",
        "dyadic_count_log_isBigO" => "Exact source statement: theorem dyadic_count_log_isBigO : Asymptotics.IsBigO Filter.atTop (fun m : ℕ => (count (2 ^ m + 1) : ℝ) - Real.logb 2 m) (fun _ : ℕ => (1 : ℝ))",
        _ => name
    };

    private static DocumentBlock Node(string name, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitiongrowth-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose)), Paragraph(Text(Exact(name)))), role);
}
