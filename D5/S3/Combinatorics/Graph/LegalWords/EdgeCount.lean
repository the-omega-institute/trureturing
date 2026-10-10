/- GID: D5/S3/Combinatorics/Graph/LegalWords/EdgeCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/EdgeCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native legal-word edges equal total occupation and its actual size-fiber sum. -/

import D5.S3.Combinatorics.Graph.LegalWordDegree

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.EdgeCount

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open D5.S3.Combinatorics.Graph.LegalWordDegree

abbrev Legal (n : ℕ) := {w : Fin n → Bool // Adm n w}

/-- The actual number of legal words with exactly `k` occupied positions. -/
def supportCount (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun b : Legal n => occupationCount b.val = k)).card

private def erase {n : ℕ} (b : Legal n) (i : Fin n) : Legal n :=
  ⟨Function.update b.val i false, by
    rw [adm_iff_no_adjacent_true]
    intro j k hjk
    by_cases hj : j = i
    · subst j; exact Or.inl (by simp)
    by_cases hk : k = i
    · subst k; exact Or.inr (by simp)
    simpa [Function.update_of_ne hj, Function.update_of_ne hk] using
      (adm_iff_no_adjacent_true n b.val).mp b.property j k hjk⟩

private theorem erase_occupation {n : ℕ} (b : Legal n) (i : Fin n)
    (hi : b.val i = true) : occupationCount (erase b i).val + 1 = occupationCount b.val := by
  classical
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => (b.val j).toNat) (Finset.mem_univ i)
  have he : occupationCount (erase b i).val =
      ∑ j ∈ Finset.univ.erase i, (b.val j).toNat := by
    unfold occupationCount
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [erase, Function.update_self, Bool.toNat_false, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  simpa [hi, occupationCount] using hsum

private theorem erase_adj {n : ℕ} (b : Legal n) (i : Fin n)
    (hi : b.val i = true) : (legalWordGraph n).Adj b (erase b i) := by
  classical
  change (Finset.univ.filter (fun j => b.val j ≠ (erase b i).val j)).card = 1
  have he : Finset.univ.filter (fun j => b.val j ≠ (erase b i).val j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    change (b.val j ≠ Function.update b.val i false j) ↔ j = i
    by_cases hj : j = i
    · subst j; simp [hi]
    · simp [hj]
  rw [he, Finset.card_singleton]

private abbrev Marked (n : ℕ) := Σ b : Legal n, {i : Fin n // b.val i = true}

open Classical in
private noncomputable def deletionEdge (n : ℕ) (p : Marked n) :
    ↥((legalWordGraph n).edgeFinset) := by
  classical
  exact ⟨s(p.1, erase p.1 p.2.val),
    SimpleGraph.mem_edgeFinset.mpr (erase_adj p.1 p.2.val p.2.property)⟩

private theorem deletionEdge_bijective (n : ℕ) : Function.Bijective (deletionEdge n) := by
  classical
  constructor
  · rintro ⟨b, i⟩ ⟨c, j⟩ he
    have hs : s(b, erase b i.val) = s(c, erase c j.val) := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp hs with ⟨hbc, hij⟩ | ⟨hbc, hcb⟩
    · subst c
      have heij : i.val = j.val := by
        by_contra hne
        have hv := congrArg (fun w : Legal n => w.val i.val) hij
        simp [erase, Function.update_of_ne hne, i.property] at hv
      have hi : i = j := Subtype.ext heij
      subst j
      rfl
    · have hb := erase_occupation b i.val i.property
      have hc := erase_occupation c j.val j.property
      have h1 := congrArg (fun w : Legal n => occupationCount w.val) hbc
      have h2 := congrArg (fun w : Legal n => occupationCount w.val) hcb
      omega
  · rintro ⟨e, he⟩
    revert he
    refine Sym2.ind (fun a b he => ?_) e
    have hab : (legalWordGraph n).Adj a b := SimpleGraph.mem_edgeFinset.mp he
    have hdiff : (Finset.univ.filter (fun i => a.val i ≠ b.val i)).card = 1 := hab
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdiff
    have hmem (j : Fin n) : a.val j ≠ b.val j ↔ j = i := by
      have := Finset.ext_iff.mp hi j
      simpa using this
    have herase (x y : Legal n) (hy : y.val i = false)
        (haway : ∀ j, j ≠ i → x.val j = y.val j) : erase x i = y := by
      apply Subtype.ext
      funext j
      by_cases hj : j = i
      · subst j; simp [erase, hy]
      · simpa [erase, Function.update_of_ne hj] using haway j hj
    have haway (j : Fin n) (hj : j ≠ i) : a.val j = b.val j := by
      by_contra hne
      exact hj ((hmem j).mp hne)
    have hne := (hmem i).mpr rfl
    cases ha : a.val i with
    | false =>
      have hb : b.val i = true := by cases h : b.val i <;> simp_all
      refine ⟨⟨b, ⟨i, hb⟩⟩, Subtype.ext ?_⟩
      change s(b, erase b i) = s(a, b)
      rw [herase b a ha (fun j hj => (haway j hj).symm), Sym2.eq_swap]
    | true =>
      have hb : b.val i = false := by cases h : b.val i <;> simp_all
      refine ⟨⟨a, ⟨i, ha⟩⟩, Subtype.ext ?_⟩
      change s(a, erase a i) = s(a, b)
      rw [herase a b hb haway]

private theorem marked_card (n : ℕ) :
    Fintype.card (Marked n) = ∑ b : Legal n, occupationCount b.val := by
  classical
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, occupationCount]
  apply Finset.sum_congr rfl
  intro i _
  cases b.val i <;> rfl

private theorem occupation_cutoff (n : ℕ) (b : Legal n) :
    occupationCount b.val ≤ (n + 1) / 2 := by
  have h := (flippable_bound_and_equality n b).1
  omega

private theorem occupation_grouping (n : ℕ) :
    (∑ b : Legal n, occupationCount b.val) =
      ∑ k ∈ Finset.range ((n + 1) / 2 + 1), k * supportCount n k := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Legal n)))
    (t := Finset.range ((n + 1) / 2 + 1))
    (g := fun b : Legal n => occupationCount b.val)
    (f := fun b : Legal n => occupationCount b.val)
    (by intro b _; exact Finset.mem_range.mpr (by have := occupation_cutoff n b; omega))
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ b ∈ Finset.univ.filter (fun b : Legal n => occupationCount b.val = k),
      occupationCount b.val) =
        ∑ _b ∈ Finset.univ.filter (fun b : Legal n => occupationCount b.val = k), k := by
          apply Finset.sum_congr rfl
          intro b hb
          exact (Finset.mem_filter.mp hb).2
    _ = k * supportCount n k := by simp [supportCount, Nat.mul_comm]

open Classical in
/-- Actual unordered edges equal total occupation and its actual size-fiber sum at every length. -/
theorem edge_count (n : ℕ) :
    (legalWordGraph n).edgeFinset.card = (∑ b : Legal n, occupationCount b.val) ∧
    (∑ b : Legal n, occupationCount b.val) =
      ∑ k ∈ Finset.range ((n + 1) / 2 + 1), k * supportCount n k := by
  classical
  constructor
  · rw [← Fintype.card_coe, ← Fintype.card_congr
      (Equiv.ofBijective (deletionEdge n) (deletionEdge_bijective n)), marked_card]
  · exact occupation_grouping n

#print axioms edge_count
#check edge_count

end D5.S3.Combinatorics.Graph.LegalWords.EdgeCount
