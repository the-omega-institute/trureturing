using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class HalvingPartitionDeficitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    private static readonly LibraryNoteRef Alekseyev =
        LibraryNoteRef.Create("D5/L/Words/alekseyev2026halving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionDeficit", H("HalvingPartitionDeficit"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("The Stern sequence is the existing published AdamsonSternFareyInverse.stern, with recursion facts exposed at their original place. The deficit is actual Stern minus actual halving count, using natural subtraction. All m≥2 and every even dilation are retained; floor-log bounds and an ordinary real-log O(1) estimate are separate verified statements. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("deficit", "Exact source declaration: noncomputable def deficit (n : ℕ) : ℕ := stern n - count n", DescribeRole.Definition),
            Node("stern_dyadic_successor", "Exact source declaration: theorem stern_dyadic_successor (m : ℕ) : stern (2 ^ m + 1) = m + 1", DescribeRole.Theorem),
            Node("deficit_dyadic", "Exact source declaration: theorem deficit_dyadic (m : ℕ) (hm : 2 ≤ m) : deficit (2 ^ m + 1) = m - 2 - thresholdCount m", DescribeRole.Theorem),
            Node("deficit_dyadic_dilation", "Exact source declaration: theorem deficit_dyadic_dilation (m v : ℕ) (hm : 2 ≤ m) : deficit (2 ^ v * (2 ^ m + 1)) = m - 2 - thresholdCount m", DescribeRole.Theorem),
            Node("deficit_log_bounds", "Exact source declaration: theorem deficit_log_bounds (m : ℕ) (hm : 4 ≤ m) : m - Nat.log2 m - 2 ≤ deficit (2 ^ m + 1) ∧ deficit (2 ^ m + 1) ≤ m - Nat.log2 m - 1", DescribeRole.Theorem),
            Node("deficit_real_log_bound", "Exact source declaration: theorem deficit_real_log_bound (m : ℕ) (hm : 4 ≤ m) : |(deficit (2 ^ m + 1) : ℝ) - ((m : ℝ) - Real.logb 2 m)| ≤ 4", DescribeRole.Theorem),
            Node("deficit_log_isBigO", "Exact source declaration: theorem deficit_log_isBigO : Asymptotics.IsBigO Filter.atTop (fun m : ℕ => (deficit (2 ^ m + 1) : ℝ) - ((m : ℝ) - Real.logb 2 m)) (fun _ : ℕ => (1 : ℝ))", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitiondeficit-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        name is "deficit_dyadic" or "deficit_dyadic_dilation"
            ? AssessedProvenance.FromLiterature(Alekseyev) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(statement))), role);
}
