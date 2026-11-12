using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionOneZeroDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionOneZero.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    private static readonly LibraryNoteRef Alekseyev =
        LibraryNoteRef.Create("D5/L/Words/alekseyev2026halving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionOneZero", H("HalvingPartitionOneZero"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("Explicit source lists at n=(2^k-1)*2^j-1 are indexed injectively by (Fin j × Fin k) ⊕ Fin(k-1). Their first-run sum and total length recover both parameters. Taking j=floor(H/2), k=H-j proves the fixed H-bit lower bound floor((H+1)^2/4)-1 for every H≥3. This does not assert an exact maximum or an exact count for every one-zero input. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("minusWord", "Exact source declaration: def minusWord (b : ℕ) : ℕ → ℕ → ℕ → List ℕ | _, _, 0 => [] | 0, _, _ + 1 => [] | m + 1, 0, l + 1 => b * 2 ^ m :: minusWord b m 0 l | m + 1, a + 1, l + 1 => (b * 2 ^ m - 1) :: minusWord b m a l", DescribeRole.Definition),
            Node("OneZeroCode", "Exact source declaration: abbrev OneZeroCode (j k : ℕ) := (Fin j × Fin k) ⊕ Fin (k - 1)", DescribeRole.Definition),
            Node("oneZeroList", "Exact source declaration: def oneZeroList (j k : ℕ) : OneZeroCode j k → List ℕ | .inl ia => minusWord (2 ^ k - 1) j ia.1.val j ++ (minusWord 1 k ia.2.val (k - 1) ++ List.replicate (ia.1.val + ia.2.val) 1) | .inr a => minusWord (2 ^ k - 1) j j j ++ (2 ^ (k - 1) - 1) :: (minusWord 1 (k - 1) a.val (k - 2) ++ List.replicate (j + a.val + 1) 1)", DescribeRole.Definition),
            Node("oneZeroList_injective", "Exact source declaration: theorem oneZeroList_injective (j k : ℕ) (hk : 2 ≤ k) : Function.Injective (oneZeroList j k)", DescribeRole.Theorem),
            Node("oneZero_count_lower", "Exact source declaration: theorem oneZero_count_lower (j k : ℕ) (hj : 1 ≤ j) (hk : 2 ≤ k) : j * k + (k - 1) ≤ count ((2 ^ k - 1) * 2 ^ j - 1)", DescribeRole.Theorem),
            Node("fixed_digit_count_lower", "Exact source declaration: theorem fixed_digit_count_lower (H : ℕ) (hH : 3 ≤ H) : ∃ n : ℕ, 2 ^ (H - 1) ≤ n ∧ n < 2 ^ H ∧ (H + 1) ^ 2 / 4 - 1 ≤ count n", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitiononezero-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        name is "oneZero_count_lower" or "fixed_digit_count_lower"
            ? AssessedProvenance.FromLiterature(Alekseyev) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(statement))), role);
}
