using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionProfile.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    private static readonly LibraryNoteRef Alekseyev =
        LibraryNoteRef.Create("D5/L/Words/alekseyev2026halving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionProfile", H("HalvingPartitionProfile"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("Exact source-length fibers use the original exhaustive list/code bijection at its original declaration. All m≥2 and all natural lengths are included. The support is exactly the integer interval from m-R_m to m+2, with one actual list per length. Total parts uses natural subtraction and exact natural division, rather than an informal rational rearrangement. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("sourceFintype", "Exact source declaration: noncomputable instance sourceFintype (n : ℕ) : Fintype (SourceLists n) := Fintype.ofFinite _", DescribeRole.Definition),
            Node("lengthCount", "Exact source declaration: noncomputable def lengthCount (n ell : ℕ) : ℕ := Nat.card {p : SourceLists n // p.val.length = ell}", DescribeRole.Definition),
            Node("lengthPolynomial", "Exact source declaration: noncomputable def lengthPolynomial (n : ℕ) : Polynomial ℕ := ∑ p : SourceLists n, Polynomial.X ^ p.val.length", DescribeRole.Definition),
            Node("codeSource_length", "Exact source declaration: theorem codeSource_length (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : (codeSource m hm c).val.length = (codeParams m c).1", DescribeRole.Theorem),
            Node("source_length_injective", "Exact source declaration: theorem source_length_injective (m : ℕ) : Function.Injective (fun p : SourceLists (2 ^ m + 1) => p.val.length)", DescribeRole.Theorem),
            Node("source_length_support", "Exact source declaration: theorem source_length_support (m ell : ℕ) (hm : 2 ≤ m) : (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔ ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨ ∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r", DescribeRole.Theorem),
            Node("lengthCount_dyadic", "Exact source declaration: theorem lengthCount_dyadic (m ell : ℕ) (hm : 2 ≤ m) : lengthCount (2 ^ m + 1) ell = if ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨ (∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r) then 1 else 0", DescribeRole.Theorem),
            Node("sum_source_dyadic", "Exact source declaration: theorem sum_source_dyadic {A : Type*} [AddCommMonoid A] (m : ℕ) (hm : 2 ≤ m) (f : SourceLists (2 ^ m + 1) → A) : ∑ p, f p = ∑ c : DyadicCode m, f (codeSource m hm c)", DescribeRole.Theorem),
            Node("lengthPolynomial_dyadic", "Exact source declaration: theorem lengthPolynomial_dyadic (m : ℕ) (hm : 2 ≤ m) : lengthPolynomial (2 ^ m + 1) = Polynomial.X ^ m * (1 + Polynomial.X + Polynomial.X ^ 2) + ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val)", DescribeRole.Theorem),
            Node("thresholdCount", "Exact source declaration: def thresholdCount (m : ℕ) : ℕ := Fintype.card (Threshold m)", DescribeRole.Definition),
            Node("threshold_iff_le_count", "Exact source declaration: theorem threshold_iff_le_count (m r : ℕ) : (1 ≤ r ∧ 2 ^ r + r + 1 ≤ m) ↔ (1 ≤ r ∧ r ≤ thresholdCount m)", DescribeRole.Theorem),
            Node("thresholdCount_lt", "Exact source declaration: theorem thresholdCount_lt (m : ℕ) (hm : 2 ≤ m) : thresholdCount m < m", DescribeRole.Theorem),
            Node("source_length_interval", "Exact source declaration: theorem source_length_interval (m ell : ℕ) (hm : 2 ≤ m) : (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔ m - thresholdCount m ≤ ell ∧ ell ≤ m + 2", DescribeRole.Theorem),
            Node("lengthIntervalEquiv", "Exact source declaration: noncomputable def lengthIntervalEquiv (m : ℕ) (hm : 2 ≤ m) : SourceLists (2 ^ m + 1) ≃ Fin (thresholdCount m + 3) := by let f : SourceLists (2 ^ m + 1) → Fin (thresholdCount m + 3) := fun p => ⟨p.val.length - (m - thresholdCount m), by have hp := (source_length_interval m p.val.length hm).mp ⟨p, rfl⟩ have hr := thresholdCount_lt m hm omega⟩ apply Equiv.ofBijective f constructor · intro p q h apply source_length_injective m change p.val.length = q.val.length have he := congrArg Fin.val h have hp := (source_length_interval m p.val.length hm).mp ⟨p, rfl⟩ have hq := (source_length_interval m q.val.length hm).mp ⟨q, rfl⟩ change p.val.length - (m - thresholdCount m) = q.val.length - (m - thresholdCount m) at he omega · intro i have hr := thresholdCount_lt m hm have hi := i.isLt obtain ⟨p, hp⟩ := (source_length_interval m (m - thresholdCount m + i.val) hm).mpr ⟨by omega, by omega⟩ refine ⟨p, Fin.ext ?_⟩ change p.val.length - (m - thresholdCount m) = i.val omega", DescribeRole.Definition),
            Node("lengthIntervalEquiv_length", "Exact source declaration: theorem lengthIntervalEquiv_length (m : ℕ) (hm : 2 ≤ m) (p : SourceLists (2 ^ m + 1)) : p.val.length = m - thresholdCount m + (lengthIntervalEquiv m hm p).val", DescribeRole.Theorem),
            Node("sum_source_lengths", "Exact source declaration: theorem sum_source_lengths {A : Type*} [AddCommMonoid A] (m : ℕ) (hm : 2 ≤ m) (f : ℕ → A) : ∑ p : SourceLists (2 ^ m + 1), f p.val.length = ∑ i : Fin (thresholdCount m + 3), f (m - thresholdCount m + i.val)", DescribeRole.Theorem),
            Node("totalParts", "Exact source declaration: noncomputable def totalParts (n : ℕ) : ℕ := ∑ p : SourceLists n, p.val.length", DescribeRole.Definition),
            Node("totalParts_eq_derivative", "For every n, totalParts n = (lengthPolynomial n).derivative.eval 1. The exact length polynomial is consumed through this derivative in the total-parts proof.", DescribeRole.Theorem),
            Node("totalParts_twice", "Exact source declaration: theorem totalParts_twice (m : ℕ) (hm : 2 ≤ m) : 2 * totalParts (2 ^ m + 1) = (thresholdCount m + 3) * (2 * m + 2 - thresholdCount m)", DescribeRole.Theorem),
            Node("totalParts_dyadic", "Exact source declaration: theorem totalParts_dyadic (m : ℕ) (hm : 2 ≤ m) : totalParts (2 ^ m + 1) = (thresholdCount m + 3) * m + 3 - thresholdCount m * (thresholdCount m + 1) / 2", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionprofile-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        name is "source_length_injective" or "source_length_support" or "lengthCount_dyadic" or "lengthPolynomial_dyadic" or "source_length_interval"
            ? AssessedProvenance.FromLiterature(Alekseyev) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(statement))), role);
}
