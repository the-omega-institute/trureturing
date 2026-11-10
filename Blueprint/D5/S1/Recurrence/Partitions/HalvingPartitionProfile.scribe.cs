using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionProfile.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionProfile",
        H("HalvingPartitionProfile"),
        Blocks(
            Paragraph(Text("These results preserve the actual SourceLists count, including repeated terminal ones and the unique empty list at zero. The dyadic enumeration specializes Alekseyev (2026), Theorem 5. The ring, weighted, representation-base and statistical scope follows the written note by Haobo Ma then Wenlin Zhang (7 November 2026, CC BY 4.0). No global novelty or independent final acceptance is asserted.")),
            Node("sourceFintype", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("lengthCount", "The number of actual source lists of exactly the specified length.", DescribeRole.Definition),
            Node("lengthPolynomial", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("codeSource_length", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("source_length_injective", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("source_length_support", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("lengthCount_dyadic", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("sum_source_dyadic", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("lengthPolynomial_dyadic", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("thresholdCount", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("threshold_iff_le_count", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("thresholdCount_lt", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("source_length_interval", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("lengthIntervalEquiv", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("lengthIntervalEquiv_length", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("sum_source_lengths", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("totalParts", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("totalParts_twice", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("totalParts_dyadic", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem))));

    private static string Exact(string name) => name switch
    {
        "sourceFintype" => "Exact source statement: noncomputable instance sourceFintype (n : ℕ) : Fintype (SourceLists n)",
        "lengthCount" => "Exact source statement: noncomputable def lengthCount (n ell : ℕ) : ℕ := Nat.card {p : SourceLists n // p.val.length = ell}",
        "lengthPolynomial" => "Exact source statement: noncomputable def lengthPolynomial (n : ℕ) : Polynomial ℕ := ∑ p : SourceLists n, Polynomial.X ^ p.val.length",
        "codeSource_length" => "Exact source statement: theorem codeSource_length (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : (codeSource m hm c).val.length = (codeParams m c).1",
        "source_length_injective" => "Exact source statement: theorem source_length_injective (m : ℕ) : Function.Injective (fun p : SourceLists (2 ^ m + 1) => p.val.length)",
        "source_length_support" => "Exact source statement: theorem source_length_support (m ell : ℕ) (hm : 2 ≤ m) : (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔ ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨ ∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r",
        "lengthCount_dyadic" => "Exact source statement: theorem lengthCount_dyadic (m ell : ℕ) (hm : 2 ≤ m) : lengthCount (2 ^ m + 1) ell = if ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨ (∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r) then 1 else 0",
        "sum_source_dyadic" => "Exact source statement: theorem sum_source_dyadic {A : Type*} [AddCommMonoid A] (m : ℕ) (hm : 2 ≤ m) (f : SourceLists (2 ^ m + 1) → A) : ∑ p, f p = ∑ c : DyadicCode m, f (codeSource m hm c)",
        "lengthPolynomial_dyadic" => "Exact source statement: theorem lengthPolynomial_dyadic (m : ℕ) (hm : 2 ≤ m) : lengthPolynomial (2 ^ m + 1) = Polynomial.X ^ m * (1 + Polynomial.X + Polynomial.X ^ 2) + ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val)",
        "thresholdCount" => "Exact source statement: def thresholdCount (m : ℕ) : ℕ := Fintype.card (Threshold m)",
        "threshold_iff_le_count" => "Exact source statement: theorem threshold_iff_le_count (m r : ℕ) : (1 ≤ r ∧ 2 ^ r + r + 1 ≤ m) ↔ (1 ≤ r ∧ r ≤ thresholdCount m)",
        "thresholdCount_lt" => "Exact source statement: theorem thresholdCount_lt (m : ℕ) (hm : 2 ≤ m) : thresholdCount m < m",
        "source_length_interval" => "Exact source statement: theorem source_length_interval (m ell : ℕ) (hm : 2 ≤ m) : (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔ m - thresholdCount m ≤ ell ∧ ell ≤ m + 2",
        "lengthIntervalEquiv" => "Exact source statement: noncomputable def lengthIntervalEquiv (m : ℕ) (hm : 2 ≤ m) : SourceLists (2 ^ m + 1) ≃ Fin (thresholdCount m + 3)",
        "lengthIntervalEquiv_length" => "Exact source statement: theorem lengthIntervalEquiv_length (m : ℕ) (hm : 2 ≤ m) (p : SourceLists (2 ^ m + 1)) : p.val.length = m - thresholdCount m + (lengthIntervalEquiv m hm p).val",
        "sum_source_lengths" => "Exact source statement: theorem sum_source_lengths {A : Type*} [AddCommMonoid A] (m : ℕ) (hm : 2 ≤ m) (f : ℕ → A) : ∑ p : SourceLists (2 ^ m + 1), f p.val.length = ∑ i : Fin (thresholdCount m + 3), f (m - thresholdCount m + i.val)",
        "totalParts" => "Exact source statement: noncomputable def totalParts (n : ℕ) : ℕ := ∑ p : SourceLists n, p.val.length",
        "totalParts_twice" => "Exact source statement: theorem totalParts_twice (m : ℕ) (hm : 2 ≤ m) : 2 * totalParts (2 ^ m + 1) = (thresholdCount m + 3) * (2 * m + 2 - thresholdCount m)",
        "totalParts_dyadic" => "Exact source statement: theorem totalParts_dyadic (m : ℕ) (hm : 2 ≤ m) : totalParts (2 ^ m + 1) = (thresholdCount m + 3) * m + 3 - thresholdCount m * (thresholdCount m + 1) / 2",
        _ => name
    };

    private static DocumentBlock Node(string name, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionprofile-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose)), Paragraph(Text(Exact(name)))), role);
}
