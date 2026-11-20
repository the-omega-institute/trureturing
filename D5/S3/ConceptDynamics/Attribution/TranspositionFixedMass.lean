/- GID: D5/S3/ConceptDynamics/Attribution/TranspositionFixedMass
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/TranspositionFixedMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp mass of transposition-fixed seeds for paired label and subset outputs. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass

open Finset

private def fixesLabelAndPair (a b i : Fin 4) (B : Finset (Fin 4)) : Prop :=
  Equiv.swap a b i = i ∧ B.image (Equiv.swap a b) = B

private instance (a b i : Fin 4) (B : Finset (Fin 4)) : Decidable (fixesLabelAndPair a b i B) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem exactlyOneTranspositionFixes :
    ∀ (i : Fin 4) (B : Finset (Fin 4)), B.card = 2 →
      (∑ a : Fin 4, ∑ b : Fin 4, if a ≠ b ∧ fixesLabelAndPair a b i B then (1 : ℕ) else 0) = 2 := by
  decide


noncomputable def transpositionMass (w : Fin 4 → Finset (Fin 4) → ℝ) (a b : Fin 4) : ℝ :=
  ∑ i, ∑ B, if a ≠ b ∧ fixesLabelAndPair a b i B then w i B else 0

private theorem sharp_mass_from_transposition_symmetry
    (w : Fin 4 → Finset (Fin 4) → ℝ) (normalize : ∑ i, ∑ B, w i B = 1)
    (support : ∀ i B, B.card ≠ 2 → w i B = 0) (c : ℝ)
    (equalMass : ∀ a b : Fin 4, a ≠ b → transpositionMass w a b = c) :
    c = 1 / 6 := by
  have columnSum (i : Fin 4) (B : Finset (Fin 4)) :
      (∑ a : Fin 4, ∑ b : Fin 4,
        if a ≠ b ∧ fixesLabelAndPair a b i B then w i B else 0) = 2 * w i B := by
    by_cases h : B.card = 2
    · have count := exactlyOneTranspositionFixes i B h
      have castCount := congrArg (fun n : ℕ => (n : ℝ)) count
      push_cast at castCount
      have term (a b : Fin 4) :
          (if a ≠ b ∧ fixesLabelAndPair a b i B then w i B else 0) =
          (if a ≠ b ∧ fixesLabelAndPair a b i B then 1 else 0) * w i B := by
        split <;> simp
      simp_rw [term, ← Finset.sum_mul, castCount]
    · simp [support i B h]
  have total : (∑ a : Fin 4, ∑ b : Fin 4, transpositionMass w a b) = 2 := by
    unfold transpositionMass
    calc
      _ = ∑ a : Fin 4 × Fin 4, ∑ b : Fin 4 × Finset (Fin 4),
          if a.1 ≠ a.2 ∧ fixesLabelAndPair a.1 a.2 b.1 b.2 then w b.1 b.2 else 0 := by
        simp only [Fintype.sum_prod_type]
      _ = ∑ b : Fin 4 × Finset (Fin 4), ∑ a : Fin 4 × Fin 4,
          if a.1 ≠ a.2 ∧ fixesLabelAndPair a.1 a.2 b.1 b.2 then w b.1 b.2 else 0 :=
        Finset.sum_comm
      _ = ∑ i : Fin 4, ∑ B : Finset (Fin 4), ∑ a : Fin 4, ∑ b : Fin 4,
          if a ≠ b ∧ fixesLabelAndPair a b i B then w i B else 0 := by
        simp only [Fintype.sum_prod_type]
      _ = 2 := by
        simp_rw [columnSum, ← Finset.mul_sum, normalize, mul_one]
  have row (a b : Fin 4) : transpositionMass w a b = if a ≠ b then c else 0 := by
    by_cases h : a ≠ b
    · simp [h, equalMass a b h]
    · obtain rfl := not_ne_iff.mp h
      simp [transpositionMass]
  have rowCount : (∑ a : Fin 4, ∑ b : Fin 4, if a ≠ b then (1 : ℕ) else 0) = 12 := by decide
  have castCount := congrArg (fun n : ℕ => (n : ℝ)) rowCount
  push_cast at castCount
  have term (a b : Fin 4) :
      (if a ≠ b then c else 0) = (if a ≠ b then 1 else 0) * c := by split <;> simp
  simp_rw [row, term, ← Finset.sum_mul, castCount] at total
  linarith


private theorem transposition_mass_transport (w : Fin 4 → Finset (Fin 4) → ℝ)
    (invariant : ∀ (g : Equiv.Perm (Fin 4)) i B, w (g i) (g.finsetCongr B) = w i B)
    (g : Equiv.Perm (Fin 4)) (a b : Fin 4) :
    transpositionMass w (g a) (g b) = transpositionMass w a b := by
  have crossing (i : Fin 4) : Equiv.swap (g a) (g b) (g i) = g (Equiv.swap a b i) := by
    have eq := congrArg (fun (e : Equiv.Perm (Fin 4)) => e (g i))
      (Equiv.symm_trans_swap_trans a b g)
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using eq.symm
  have mapCrossing (B : Finset (Fin 4)) :
      (g.finsetCongr B).image (Equiv.swap (g a) (g b)) =
        g.finsetCongr (B.image (Equiv.swap a b)) := by
    simp only [Equiv.finsetCongr_apply, Finset.map_eq_image, Finset.image_image]
    exact congrArg (fun F : Fin 4 → Fin 4 => B.image F) (funext crossing)
  have iffFix (i : Fin 4) (B : Finset (Fin 4)) :
      fixesLabelAndPair (g a) (g b) (g i) (g.finsetCongr B) ↔ fixesLabelAndPair a b i B := by
    unfold fixesLabelAndPair
    rw [crossing, mapCrossing, g.injective.eq_iff, g.finsetCongr.injective.eq_iff]
  unfold transpositionMass
  rw [← Equiv.sum_comp g]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Equiv.sum_comp g.finsetCongr]
  apply Finset.sum_congr rfl
  intro B _
  simp only [iffFix, g.injective.ne_iff, invariant]


private theorem invariant_table_transposition_mass
    (w : Fin 4 → Finset (Fin 4) → ℝ) (normalize : ∑ i, ∑ B, w i B = 1)
    (support : ∀ i B, B.card ≠ 2 → w i B = 0)
    (invariant : ∀ (g : Equiv.Perm (Fin 4)) i B, w (g i) (g.finsetCongr B) = w i B) :
    transpositionMass w 0 1 = 1 / 6 := by
  apply sharp_mass_from_transposition_symmetry w normalize support
  intro a b hab
  let first : Equiv.Perm (Fin 4) := Equiv.swap 0 a
  have first0 : first 0 = a := Equiv.swap_apply_left _ _
  have distinct : first 1 ≠ a := by
    rw [← first0]
    exact first.injective.ne (by decide)
  let last : Equiv.Perm (Fin 4) := Equiv.swap (first 1) b
  have lastA : last a = a := Equiv.swap_apply_of_ne_of_ne distinct.symm hab
  have lastB : last (first 1) = b := Equiv.swap_apply_left _ _
  let g := first.trans last
  have h0 : g 0 = a := by unfold g; rw [Equiv.trans_apply, first0, lastA]
  have h1 : g 1 = b := lastB
  simpa only [h0, h1] using transposition_mass_transport w invariant g 0 1


theorem seeded_transposition_mass_le {S : Type*} [Fintype S] [MulAction (Equiv.Perm (Fin 4)) S]
    (w : S → ℝ) (nn : ∀ s, 0 ≤ w s) (total : ∑ s, w s = 1)
    (weightInvariant : ∀ (g : Equiv.Perm (Fin 4)) s, w (g • s) = w s)
    (i : S → Fin 4) (B : S → Finset (Fin 4))
    (card : ∀ s, (B s).card = 2)
    (labelCov : ∀ (g : Equiv.Perm (Fin 4)) s, i (g • s) = g (i s))
    (pairCov : ∀ (g : Equiv.Perm (Fin 4)) s, B (g • s) = g.finsetCongr (B s))
    [DecidablePred (fun s : S => Equiv.swap (0 : Fin 4) 1 • s = s)] :
    (∑ s ∈ univ.filter (fun s => Equiv.swap (0 : Fin 4) 1 • s = s), w s) ≤ 1 / 6 := by
  classical
  let T := Fin 4 × Finset (Fin 4)
  let t (s : S) : T := (i s, B s)
  let mass (p : T) := ∑ s, if t s = p then w s else 0
  let table (j : Fin 4) (p : Finset (Fin 4)) := mass (j, p)
  have normalized : ∑ j, ∑ p, table j p = 1 := by
    change (∑ j : Fin 4, ∑ p : Finset (Fin 4), mass (j,p)) = 1
    rw [← Fintype.sum_prod_type]
    have overAll := Finset.sum_fiberwise_eq_sum_filter univ (univ : Finset T) t w
    simpa only [Finset.sum_filter, Finset.mem_univ, ite_true, mass] using overAll.trans (by simpa using total)
  have supported (j : Fin 4) (p : Finset (Fin 4)) (bad : p.card ≠ 2) :
      table j p = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    have no : t s ≠ (j, p) := fun h => bad ((congrArg (fun v : T => v.2.card) h).symm.trans (card s))
    simp [no]
  have invariant (g : Equiv.Perm (Fin 4)) j p :
      table (g j) (g.finsetCongr p) = table j p := by
    change mass (g j, g.finsetCongr p) = mass (j,p)
    unfold mass
    rw [← Equiv.sum_comp (MulAction.toPerm g)]
    apply Finset.sum_congr rfl
    intro s _
    have hit : t (g • s) = (g j, g.finsetCongr p) ↔ t s = (j,p) := by
      simp only [t, labelCov, pairCov]
      let e := g.prodCongr g.finsetCongr
      change e (i s, B s) = e (j,p) ↔ (i s, B s) = (j,p)
      exact e.injective.eq_iff
    change (if t (g • s) = (g j, g.finsetCongr p) then w (g • s) else 0) = _
    simp only [hit, weightInvariant]
  let good (p : T) := (0 : Fin 4) ≠ 1 ∧ fixesLabelAndPair 0 1 p.1 p.2
  have transported :
      transpositionMass table 0 1 = ∑ s ∈ univ.filter (fun s => good (t s)), w s := by
    unfold transpositionMass
    change (∑ j : Fin 4, ∑ p : Finset (Fin 4), if good (j,p) then mass (j,p) else 0) = _
    rw [← Fintype.sum_prod_type (fun p : T => if good p then mass p else 0)]
    simpa only [Finset.sum_filter, Finset.mem_filter, Finset.mem_univ, true_and, mass] using
      Finset.sum_fiberwise_eq_sum_filter univ (univ.filter good) t w
  rw [← invariant_table_transposition_mass table normalized supported invariant, transported]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    have fixed := (Finset.mem_filter.mp hs).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide, ?_⟩
    have lab := (labelCov (Equiv.swap 0 1) s).symm
    have pair := (pairCov (Equiv.swap 0 1) s).symm
    rw [fixed] at lab pair
    refine ⟨lab, ?_⟩
    change (B s).image (Equiv.swap (0 : Fin 4) 1) = B s
    rw [Equiv.finsetCongr_apply, Finset.map_eq_image] at pair
    exact pair
  · intro s _ _
    exact nn s


private noncomputable def uniformTable (_ : Fin 4) (B : Finset (Fin 4)) : ℝ :=
  if B.card = 2 then 1 / 24 else 0

private theorem invariant_uniform_table_attains
    : (∀ i : Fin 4, (∑ B : Finset (Fin 4), uniformTable i B) = 1 / 4)
      ∧ (∀ B : Finset (Fin 4), B.card = 2 → (∑ i : Fin 4, uniformTable i B) = 1 / 6)
      ∧ transpositionMass uniformTable 0 1 = 1 / 6 := by
  have counts : (∑ B : Finset (Fin 4), if B.card = 2 then (1 : ℕ) else 0) = 6 := by decide
  have realCount := congrArg (fun n : ℕ => (n : ℝ)) counts
  push_cast at realCount
  have labelMass (i : Fin 4) : (∑ B : Finset (Fin 4), uniformTable i B) = 1 / 4 := by
    have term (B : Finset (Fin 4)) : uniformTable i B =
        (if B.card = 2 then 1 else 0) * ((1 : ℝ) / 24) := by
      by_cases h : B.card = 2 <;> simp [uniformTable, h]
    simp_rw [term, ← Finset.sum_mul, realCount]
    norm_num
  refine ⟨labelMass, ?_, ?_⟩
  · intro B h
    simp only [uniformTable, h, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  · apply invariant_table_transposition_mass uniformTable
    · simp only [labelMass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    · intro i B bad
      simp [uniformTable, bad]
    · intro g i B
      simp [uniformTable, Equiv.finsetCongr_apply]


/-- A common invariant table law with these marginals attains the transposition bound. -/
theorem uniform_label_pair_attains :
    ∃ w : Fin 4 → Finset (Fin 4) → ℝ,
      (∀ i B, B.card = 2 → 0 < w i B) ∧
      (∀ i B, B.card ≠ 2 → w i B = 0) ∧
      (∀ (g : Equiv.Perm (Fin 4)) i B, w (g i) (g.finsetCongr B) = w i B) ∧
      (∀ i : Fin 4, (∑ B : Finset (Fin 4), w i B) = 1 / 4) ∧
      (∀ B : Finset (Fin 4), B.card = 2 → (∑ i : Fin 4, w i B) = 1 / 6) ∧
      (∑ i, ∑ B, w i B) = 1 ∧ transpositionMass w 0 1 = 1 / 6 := by
  obtain ⟨label, pair, fixed⟩ := invariant_uniform_table_attains
  refine ⟨uniformTable, ?_, ?_, ?_, label, pair, ?_, fixed⟩
  · intro i B good
    norm_num [uniformTable, good]
  · intro i B bad
    simp [uniformTable, bad]
  · intro g i B
    simp [uniformTable, Equiv.finsetCongr_apply]
  · simp only [label, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num

end D5.S3.ConceptDynamics.Attribution.TranspositionFixedMass
