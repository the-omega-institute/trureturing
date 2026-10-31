/- GID: D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtThreeRowMixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal three-row Young weights and strict shifted dominance determine the actual mixed character pairing. -/

/-
Source only: native elaboration, axiom closure, liveness and admission are unverified.
Unfinished audit: https://github.com/the-omega-institute/trureturing/issues/24542.
The actual complex polytabloid Specht module and all selected Apache suppliers are
unchanged. No standalone firstfreeze is asserted. Arbitrary degree, not enumeration.
-/
import D5.S3.Combinatorics.Partitions.SpechtThreeRowVirtual

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators
namespace TauCeti.ThreeRowGram
open _root_.Equiv _root_.Equiv.Perm Finset MvPolynomial CategoryTheory

/-- Sort the three natural row sizes and delete zero parts. Equal sizes retain their
multiplicity. The degree proof changes no data in the literal partition. -/
def tripleShape {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n) : n.Partition :=
  weightPartition (Finsupp.equivFunOnFinite.symm r)
    (by simpa only [Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm] using hr)

private theorem tripleShape_parts {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n) :
    (tripleShape r hr).parts =
      (([r 0, r 1, r 2].filter fun x => x != 0 : List ℕ) : Multiset ℕ) := by
  classical
  let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm r
  have hs : d.support = ({0, 1, 2} : Finset (Fin 3)).filter fun i => r i ≠ 0 := by
    ext i
    fin_cases i <;> simp [d]
  change (weightPartition d _).parts = _
  rw [weightPartition_parts, hs]
  by_cases h0 : r 0 = 0 <;> by_cases h1 : r 1 = 0 <;> by_cases h2 : r 2 = 0 <;>
    simp [d, h0, h1, h2, Multiset.filter_singleton] <;> rfl

private theorem tripleShape_sorted {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n)
    (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1) :
    (tripleShape r hr).parts.sort (· ≥ ·) =
      [r 0, r 1, r 2].filter fun x => x != 0 := by
  rw [tripleShape_parts, Multiset.coe_sort]
  apply List.mergeSort_eq_self
  apply List.Pairwise.filter
  refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact h01
    · exact h12.trans h01
  · intro a ha
    have he : a = r 2 := List.mem_singleton.mp ha
    subst a
    exact h12
  · simp

private theorem tripleShape_rows {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n)
    (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1) (i : Fin 3) :
    (_root_.YoungDiagram.ofPartition (tripleShape r hr)).rowLen i = r i := by
  rw [YoungDiagram.rowLen_ofPartition, tripleShape_sorted r hr h01 h12]
  by_cases h0 : r 0 = 0 <;> by_cases h1 : r 1 = 0 <;> by_cases h2 : r 2 = 0
  all_goals fin_cases i <;> simp_all

/-- The ordered-colouring character is the character of the actual Young module at
its sort/delete-zero partition. There is no quotient by permutations of equal rows. -/
private theorem fixedColourings_eq_youngFixed {n : ℕ} (r : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (π : Perm (Fin n)) :
    fixedColourings (fun i => (r i : ℤ)) π =
      Nat.card {q : Perm (Fin n) ⧸ youngSubgroup (tripleShape r hr) // π • q = q} := by
  let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm r
  have hd : d.degree = n := by simpa only [d, Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm] using hr
  let ρ := (partitionEquivConjClasses n).symm (ConjClasses.mk π)
  have hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ :=
    ((partitionEquivConjClasses n).apply_symm_apply _).symm
  have hc := coeff_psumPart_eq_card_fixedPoints (σ := Fin 3) ℤ hπ hd
  rw [psumPart_eq_psumPart_partition ℤ hπ, coeff_psumPart_partition] at hc
  have he : fixedColourings (fun i => (r i : ℤ)) π =
      #{f : Fin n → Fin 3 | f ∘ π = f ∧ ∀ i, #{x | f x = i} = d i} := by
    unfold fixedColourings
    congr 1
    ext f
    simp [d, Finsupp.coe_equivFunOnFinite_symm]
  rw [he]
  convert (Int.natCast_inj.mp hc) using 1 <;> simp [tripleShape, d]

private theorem sum_spechtChar_mul_fixedColourings {n : ℕ} (μ : n.Partition)
    (r : Fin 3 → ℕ) (hr : ∑ i, r i = n) :
    (∑ π : Perm (Fin n), spechtChar μ π * (fixedColourings (fun i => (r i : ℤ)) π : ℤ)) =
      (n.factorial : ℤ) *
        (Module.finrank ℂ (spechtModuleℂ μ ⟶ permutationModuleℂ (tripleShape r hr)) : ℤ) := by
  have h := sum_spechtTrace_mul_card_fixedPoints μ (tripleShape r hr)
  change (∑ π : Perm (Fin n), (spechtModuleℂ μ).character π * _) = _ at h
  simp only [character_spechtModuleℂ_intCast] at h
  simp_rw [fixedColourings_eq_youngFixed r hr]
  exact_mod_cast h

private theorem prefix_rows {n : ℕ} (μ : n.Partition) (k : ℕ) :
    ((μ.parts.sort (· ≥ ·)).take k).sum =
      ∑ i ∈ range k, (_root_.YoungDiagram.ofPartition μ).rowLen i := by
  rw [← _root_.YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    YoungDiagram.sum_take_rowLens_eq_card_filter_fst,
    YoungDiagram.sum_range_rowLen_eq_card_filter_fst]

/-- Sorting a three-coordinate weight increases each proper prefix. This proof
uses the existing permutation of the weight to the literal padded row lengths. -/
private theorem weight_prefix_le_rows {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n) :
    r 0 ≤ (_root_.YoungDiagram.ofPartition (tripleShape r hr)).rowLen 0 ∧
    r 0 + r 1 ≤ (_root_.YoungDiagram.ofPartition (tripleShape r hr)).rowLen 0 +
      (_root_.YoungDiagram.ofPartition (tripleShape r hr)).rowLen 1 := by
  let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm r
  obtain ⟨e, he⟩ := exists_perm_mapDomain_eq_partWeight d
    (show d.degree = n by simpa only [d, Finsupp.degree_eq_sum, Finsupp.coe_equivFunOnFinite_symm] using hr)
  let p : Perm (Fin 3) := e.trans (Fintype.equivFin (Fin 3))
  let q : ℕ → ℕ := (_root_.YoungDiagram.ofPartition (tripleShape r hr)).rowLen
  have hp (i : Fin 3) : r i = q (p i) := by
    have h := congrArg (fun w : Fin 3 →₀ ℕ => w (e i)) he
    rw [Finsupp.mapDomain_apply_of_injective e.injective, partWeight_apply] at h
    change r i = (_root_.YoungDiagram.ofPartition (weightPartition d _)).rowLen
      ((Fintype.equivFin (Fin 3)) (e i))
    simpa only [d, Finsupp.coe_equivFunOnFinite_symm] using h
  have h01 : q 1 ≤ q 0 := _root_.YoungDiagram.rowLen_anti _ 0 1 (by omega)
  have h12 : q 2 ≤ q 1 := _root_.YoungDiagram.rowLen_anti _ 1 2 (by omega)
  have hne : p 0 ≠ p 1 := p.injective.ne (by decide)
  rw [hp 0, hp 1]
  generalize h0 : p 0 = i0 at *
  generalize h1 : p 1 = i1 at *
  fin_cases i0 <;> fin_cases i1 <;> simp_all [q] <;> omega

private theorem shifted_sum {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n)
    (σ : Perm (Fin 3)) : ∑ i, shifted r σ i = (n : ℤ) := by
  have hp : (∑ i : Fin 3, (σ i : ℕ)) = ∑ i : Fin 3, (i : ℕ) :=
    Equiv.sum_comp σ (fun i : Fin 3 => (i : ℕ))
  have hz : (∑ i : Fin 3, ((σ i : ℕ) : ℤ)) = ∑ i : Fin 3, ((i : ℕ) : ℤ) := by
    exact_mod_cast hp
  simp only [shifted, sum_add_distrib, sum_sub_distrib]
  rw [hz, sub_add_cancel]
  exact_mod_cast hr

theorem shifted_nat_sum {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n)
    (σ : Perm (Fin 3)) (hn : ∀ i, 0 ≤ shifted r σ i) :
    (∑ i, (shifted r σ i).toNat) = n := by
  have h : (∑ i, ((shifted r σ i).toNat : ℤ)) = (n : ℤ) := by
    simpa only [Int.toNat_of_nonneg (hn _)] using shifted_sum r hr σ
  exact_mod_cast h

private theorem shifted_strict_prefix (r : Fin 3 → ℕ) (σ : Perm (Fin 3)) (hσ : σ ≠ 1) :
    (r 0 : ℤ) < shifted r σ 0 ∨
    (r 0 : ℤ) + r 1 < shifted r σ 0 + shifted r σ 1 := by
  have hi01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hi02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hi12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have hs0 := (σ 0).isLt
  have hs1 := (σ 1).isLt
  have hs2 := (σ 2).isLt
  have hn : ¬ ((σ 0 : ℕ) = 0 ∧ (σ 1 : ℕ) = 1) := by
    rintro ⟨h0, h1⟩
    apply hσ
    apply Equiv.ext
    intro i
    fin_cases i
    · exact Fin.ext h0
    · exact Fin.ext h1
    · apply Fin.ext
      change (σ (2 : Fin 3) : ℕ) = 2
      have hn0 : (σ 2 : ℕ) ≠ 0 := fun h => hi02 (Fin.ext (h0.trans h.symm))
      have hn1 : (σ 2 : ℕ) ≠ 1 := fun h => hi12 (Fin.ext (h1.trans h.symm))
      omega
  have hne : (σ 0 : ℕ) ≠ (σ 1 : ℕ) := fun h => hi01 (Fin.ext h)
  simp only [shifted, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  omega

private theorem shifted_not_dominated {n : ℕ} (r : Fin 3 → ℕ) (hr : ∑ i, r i = n)
    (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1) (σ : Perm (Fin 3)) (hσ : σ ≠ 1)
    (hnonneg : ∀ i, 0 ≤ shifted r σ i) :
    ¬ Dominates (tripleShape r hr)
      (tripleShape (fun i => (shifted r σ i).toNat)
        (shifted_nat_sum r hr σ hnonneg)) := by
  let a : Fin 3 → ℕ := fun i => (shifted r σ i).toNat
  have ha (i : Fin 3) : (a i : ℤ) = shifted r σ i := Int.toNat_of_nonneg (hnonneg i)
  have hat : ∑ i, a i = n := shifted_nat_sum r hr σ hnonneg
  intro hd
  have hb := weight_prefix_le_rows a hat
  have hd1 := hd 1
  have hd2 := hd 2
  rw [prefix_rows, prefix_rows] at hd1 hd2
  simp only [sum_range_succ, range_zero, sum_empty, zero_add] at hd1 hd2
  have hr0 : (_root_.YoungDiagram.ofPartition (tripleShape r hr)).rowLen 0 = r 0 := by
    simpa using tripleShape_rows r hr h01 h12 (0 : Fin 3)
  have hr1 : (_root_.YoungDiagram.ofPartition (tripleShape r hr)).rowLen 1 = r 1 := by
    simpa using tripleShape_rows r hr h01 h12 (1 : Fin 3)
  rw [hr0] at hd1 hd2
  rw [hr1] at hd2
  have hb1 : a 0 ≤ r 0 := hb.1.trans hd1
  have hb2 : a 0 + a 1 ≤ r 0 + r 1 := hb.2.trans hd2
  have hi := shifted_strict_prefix r σ hσ
  have hb1z : (a 0 : ℤ) ≤ r 0 := by exact_mod_cast hb1
  have hb2z : (a 0 : ℤ) + a 1 ≤ (r 0 : ℤ) + r 1 := by exact_mod_cast hb2
  simp only [ha] at hb1z hb2z
  omega

/-- Actual same-shape mixed pairing in every degree. Negative shifts are empty;
all other nonidentity shifts are killed by actual Hom dominance. -/
theorem sum_spechtChar_mul_virtualCharacter {n : ℕ} (r : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1) :
    (∑ π : Perm (Fin n), spechtChar (tripleShape r hr) π * virtualCharacter n r π) =
      (n.factorial : ℤ) := by
  classical
  have hterm (σ : Perm (Fin 3)) :
      (∑ π : Perm (Fin n), spechtChar (tripleShape r hr) π *
        (fixedColourings (shifted r σ) π : ℤ)) =
        if σ = 1 then (n.factorial : ℤ) else 0 := by
    by_cases hn : ∀ i, 0 ≤ shifted r σ i
    · let a : Fin 3 → ℕ := fun i => (shifted r σ i).toNat
      have ha : (fun i => (a i : ℤ)) = shifted r σ :=
        funext fun i => Int.toNat_of_nonneg (hn i)
      have hat : ∑ i, a i = n := shifted_nat_sum r hr σ hn
      rw [← ha, sum_spechtChar_mul_fixedColourings _ a hat]
      by_cases hs : σ = 1
      · subst σ
        have he : a = r := by ext i; simp [a, shifted]
        have hshape : tripleShape a hat = tripleShape r hr := by simp only [he]
        rw [hshape, finrank_hom_spechtModuleℂ_permutationModuleℂ_self]
        simp
      · rw [finrank_hom_spechtModuleℂ_permutationModuleℂ_eq_zero
          (shifted_not_dominated r hr h01 h12 σ hs hn)]
        simp [hs]
    · obtain ⟨i, hi⟩ := not_forall.mp hn
      have hz (π : Perm (Fin n)) : fixedColourings (shifted r σ) π = 0 := by
        rw [fixedColourings, card_eq_zero, filter_eq_empty_iff]
        intro f _ hf
        have hf0 := hf.2 i
        have hnat := Int.natCast_nonneg (#{x | f x = i})
        omega
      have hs : σ ≠ 1 := by
        rintro rfl
        simp [shifted] at hi
      simp [hz, hs]
  simp only [virtualCharacter, mul_sum]
  rw [sum_comm]
  simp_rw [show ∀ σ π, spechtChar (tripleShape r hr) π *
    ((sign σ : ℤ) * (fixedColourings (shifted r σ) π : ℤ)) =
    (sign σ : ℤ) * (spechtChar (tripleShape r hr) π *
      (fixedColourings (shifted r σ) π : ℤ)) from fun _ _ => by ring]
  simp_rw [← mul_sum, hterm]
  simp

/-- With the mixed scalar supplied, only the finite Cauchy self-Gram premise
remains in the actual same-literal-shape ordinary trace criterion. -/
theorem ordinaryTrace_eq_frobChar_of_selfGram {n : ℕ} (r : Fin 3 → ℕ)
    (hr : ∑ i, r i = n) (h01 : r 1 ≤ r 0) (h12 : r 2 ≤ r 1)
    (hgram : signedContingencyGram n r r = 1) (ρ : n.Partition) {π : Perm (Fin n)}
    (hπ : ConjClasses.mk π = partitionEquivConjClasses n ρ) {τ : List ℕ}
    (hτ : (τ : Multiset ℕ) = ρ.parts) :
    LinearMap.trace ℂ _ ((spechtModuleℂ (tripleShape r hr)).ρ π) =
      (D5.S3.Combinatorics.Partitions.HemmerStraubWestrem.frobChar r τ : ℂ) := by
  exact ordinaryTrace_eq_frobChar_of_gram _ ρ r hgram
    (sum_spechtChar_mul_virtualCharacter r hr h01 h12) hπ hτ

end TauCeti.ThreeRowGram
end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
