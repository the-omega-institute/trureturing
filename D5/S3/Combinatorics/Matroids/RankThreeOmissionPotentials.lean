/- GID: D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeOmissionPotentials
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Point potentials determine the cyclic factors of rank-three lifting obstructions. -/

import D5.S3.Combinatorics.Matroids.CircuitDifferenceBasis
import D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates
import D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors
import D5.S3.Combinatorics.Matroids.UniformCircuitResidueDiagonal
import D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.Function
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Point potentials for relations among omitted triangle rows. -/

namespace D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials

private theorem cycle_torsion {A : Type*} [AddCommGroup A] (u v w : A)
    (h₁ : v - u = w - v) (h₂ : w - v = u - w) :
    3 • (v - u) = 0 ∧ 3 • (w - v) = 0 ∧ 3 • (u - w) = 0 := by
  have h : 3 • (v - u) = 0 := calc
    3 • (v - u) = (v - u) + (v - u) + (v - u) := by abel
    _ = (v - u) + (w - v) + (u - w) := by
      exact congrArg₂ (· + ·) (congrArg ((v - u) + ·) h₁) (h₁.trans h₂)
    _ = 0 := by abel
  exact ⟨h, h₁ ▸ h, (h₁.trans h₂) ▸ h⟩

private theorem triangle_gaps_torsion {A : Type*} [AddCommGroup A] (u : Fin 3 → A)
    (h₁ : u 1 - u 0 = u 2 - u 1) (h₂ : u 2 - u 1 = u 0 - u 2) :
    ∀ i j : Fin 3, 3 • (u j - u i) = 0 := by
  obtain ⟨ha, hb, hc⟩ := cycle_torsion (u 0) (u 1) (u 2) h₁ h₂
  have ha' : 3 • (u 0 - u 1) = 0 := by
    calc
      3 • (u 0 - u 1) = (-((3 : ℕ) • (u 1 - u 0)) : A) := by abel
      _ = 0 := by rw [ha, neg_zero]
  have hb' : 3 • (u 1 - u 2) = 0 := by
    calc
      3 • (u 1 - u 2) = (-((3 : ℕ) • (u 2 - u 1)) : A) := by abel
      _ = 0 := by rw [hb, neg_zero]
  have hc' : 3 • (u 2 - u 0) = 0 := by
    calc
      3 • (u 2 - u 0) = (-((3 : ℕ) • (u 0 - u 2)) : A) := by abel
      _ = 0 := by rw [hc, neg_zero]
  intro i j
  fin_cases i <;> fin_cases j <;> first | assumption | simp

/-- After fixing one point's potential to zero, constant cyclic gaps on omitted
triangles and zero gaps on uncovered edges become three-torsion line sums. -/
private theorem normalized_potential_iff {I T A : Type*} [AddCommGroup A]
    (points : T → Fin 3 → I) (u : I → A) (root : I) :
    let uncovered (i j : I) := ¬ ∃ t a b, points t a = i ∧ points t b = j
    let v (i : I) := u i - u root
    ( (∀ i j, uncovered i j → u i = u j) ∧
      (∀ t, u (points t 1) - u (points t 0) = u (points t 2) - u (points t 1) ∧
        u (points t 2) - u (points t 1) = u (points t 0) - u (points t 2))) ↔
    ( (∀ i, 3 • v i = 0) ∧ (∀ i j, uncovered i j → v i = v j) ∧
      (∀ t, v (points t 0) + v (points t 1) + v (points t 2) = 0)) := by
  classical
  intro uncovered v
  have gap (i j : I) : v j - v i = u j - u i := by dsimp [v]; abel
  have eq_shift (i j : I) : u i = u j ↔ v i = v j := by
    constructor
    · intro h
      simp only [v, h]
    · intro h
      apply sub_eq_zero.mp
      rw [← gap j i, h, sub_self]
  constructor
  · rintro ⟨hedge, hcycle⟩
    have htorsion (i : I) : 3 • v i = 0 := by
      by_cases h : uncovered root i
      · simp [v, hedge root i h]
      · obtain ⟨t, a, b, ha, hb⟩ :
            ∃ t a b, points t a = root ∧ points t b = i := by
          exact not_not.mp h
        have hc := triangle_gaps_torsion (u ∘ points t) (hcycle t).1 (hcycle t).2 a b
        simpa [Function.comp_apply, v, ha, hb] using hc
    refine ⟨htorsion, fun i j h => (eq_shift i j).mp (hedge i j h), ?_⟩
    intro t
    have h : v (points t 1) - v (points t 0) = v (points t 2) - v (points t 1) := by
      simp only [gap]
      exact (hcycle t).1
    calc
      v (points t 0) + v (points t 1) + v (points t 2) =
          3 • v (points t 1) + ((v (points t 2) - v (points t 1)) -
            (v (points t 1) - v (points t 0))) := by abel
      _ = 0 := by rw [← h, sub_self, add_zero, htorsion]
  · rintro ⟨htorsion, hedge, hline⟩
    refine ⟨fun i j h => (eq_shift i j).mpr (hedge i j h), ?_⟩
    intro t
    simp only [← gap]
    constructor
    · calc
        v (points t 1) - v (points t 0) =
            (v (points t 2) - v (points t 1)) + (3 • v (points t 1) -
              (v (points t 0) + v (points t 1) + v (points t 2))) := by abel
        _ = _ := by rw [htorsion, hline, sub_self, add_zero]
    · calc
        v (points t 2) - v (points t 1) =
            (v (points t 0) - v (points t 2)) + (3 • v (points t 2) -
              (v (points t 0) + v (points t 1) + v (points t 2))) := by abel
        _ = _ := by rw [htorsion, hline, sub_self, add_zero]

private def forward {I : Type*} (triangle : Fin 3 → I) (i j : I) : Prop :=
  (triangle 0 = i ∧ triangle 1 = j) ∨
  (triangle 1 = i ∧ triangle 2 = j) ∨
  (triangle 2 = i ∧ triangle 0 = j)

private def covers {I : Type*} (triangle : Fin 3 → I) (i j : I) : Prop :=
  ∃ a b, triangle a = i ∧ triangle b = j

private theorem covers_iff_forward {I : Type*} (triangle : Fin 3 → I) {i j : I}
    (hne : i ≠ j) : covers triangle i j ↔ forward triangle i j ∨ forward triangle j i := by
  constructor
  · rintro ⟨a, b, ha, hb⟩
    fin_cases a <;> fin_cases b <;>
      first
      | exact (hne (ha.symm.trans hb)).elim
      | exact Or.inl (Or.inl ⟨ha, hb⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨ha, hb⟩))
      | exact Or.inl (Or.inr (Or.inr ⟨ha, hb⟩))
      | exact Or.inr (Or.inl ⟨hb, ha⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨hb, ha⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨hb, ha⟩))
  · intro h
    rcases h with (⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩) | (⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩)
    · exact ⟨0, 1, ha, hb⟩
    · exact ⟨1, 2, ha, hb⟩
    · exact ⟨2, 0, ha, hb⟩
    · exact ⟨1, 0, hb, ha⟩
    · exact ⟨2, 1, hb, ha⟩
    · exact ⟨0, 2, hb, ha⟩

private noncomputable def row {I A : Type*} [AddCommGroup A]
    (triangle : Fin 3 → I) (value : A) (i j : I) : A :=
  open Classical in
  if forward triangle i j then value else if forward triangle j i then -value else 0

private theorem row_eq_zero {I A : Type*} [AddCommGroup A]
    (triangle : Fin 3 → I) (value : A) {i j : I}
    (hne : i ≠ j) (h : ¬ covers triangle i j) : row triangle value i j = 0 := by
  classical
  have h' := fun hf => h ((covers_iff_forward triangle hne).mpr hf)
  have hf : ¬ forward triangle i j := fun hf => h' (Or.inl hf)
  have hr : ¬ forward triangle j i := fun hr => h' (Or.inr hr)
  rw [row, ite_eq_right hf, ite_eq_right hr]

private theorem not_reverse {I : Type*} {triangle : Fin 3 → I}
    (hinj : Function.Injective triangle) {i j : I}
    (hf : forward triangle i j) : ¬ forward triangle j i := by
  intro hr
  rcases hf with (⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩) <;>
    rcases hr with (⟨hc,hd⟩ | ⟨hc,hd⟩ | ⟨hc,hd⟩) <;>
    first
    | have hf := hinj (ha.trans hd.symm); exact absurd hf (by decide)
    | have hf := hinj (hb.trans hc.symm); exact absurd hf (by decide)

/-- For disjoint triangle edge supports, the gap of a point potential is a
sum of oriented triangle rows exactly for normalized three-torsion potentials
with zero uncovered gaps and zero sums on each triangle. -/
private theorem edge_rows_iff {I T A : Type*} [Fintype T] [AddCommGroup A]
    (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j → covers (points t) i j → covers (points s) i j → t = s)
    (u : I → A) (root : I) :
    let v (i : I) := u i - u root
    (∃ c : T → A, ∀ i j, i ≠ j → u j - u i = ∑ t, row (points t) (c t) i j) ↔
    ((∀ i, 3 • v i = 0) ∧
      (∀ i j, (¬ ∃ t a b, points t a = i ∧ points t b = j) → v i = v j) ∧
      (∀ t, v (points t 0) + v (points t 1) + v (points t 2) = 0)) := by
  classical
  intro v
  have normalize := normalized_potential_iff points u root
  dsimp only at normalize
  refine Iff.trans ?_ normalize
  have single (c : T → A) (t : T) (i j : I) (hne : i ≠ j)
      (ht : covers (points t) i j) :
      (∑ s, row (points s) (c s) i j) = row (points t) (c t) i j := by
    apply Finset.sum_eq_single_of_mem t (Finset.mem_univ _)
    intro s _ hst
    exact row_eq_zero _ _ hne fun hs => hst (hdis s t i j hne hs ht)
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨?_, ?_⟩
    · intro i j huncovered
      by_cases hne : i = j
      · exact congrArg u hne
      · have hz : u j - u i = 0 := by
          rw [hc i j hne]
          apply Finset.sum_eq_zero
          intro t _
          exact row_eq_zero _ _ hne (fun ⟨a,b,ha,hb⟩ => huncovered ⟨t,a,b,ha,hb⟩)
        exact (sub_eq_zero.mp hz).symm
    · intro t
      have eval (i j : I) (hne : i ≠ j) (hf : forward (points t) i j) :
          u j - u i = c t := by
        rw [hc i j hne, single c t i j hne
          ((covers_iff_forward _ hne).mpr (Or.inl hf)), row, ite_eq_left hf]
      have h01 := eval _ _ ((hinj t).ne (by decide : (0 : Fin 3) ≠ 1))
        (Or.inl ⟨rfl, rfl⟩)
      have h12 := eval _ _ ((hinj t).ne (by decide : (1 : Fin 3) ≠ 2))
        (Or.inr (Or.inl ⟨rfl, rfl⟩))
      have h20 := eval _ _ ((hinj t).ne (by decide : (2 : Fin 3) ≠ 0))
        (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact ⟨h01.trans h12.symm, h12.trans h20.symm⟩
  · rintro ⟨hedge, hcycle⟩
    let c := fun t => u (points t 1) - u (points t 0)
    refine ⟨c, ?_⟩
    intro i j hne
    by_cases h : ∃ t, covers (points t) i j
    · obtain ⟨t, ht⟩ := h
      rw [single c t i j hne ht]
      have eval (i j : I) (hf : forward (points t) i j) : u j - u i = c t := by
        rcases hf with (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · rfl
        · exact (hcycle t).1.symm
        · exact ((hcycle t).1.trans (hcycle t).2).symm
      rcases (covers_iff_forward _ hne).mp ht with hf | hf
      · rw [row, ite_eq_left hf]
        exact eval i j hf
      · rw [row, ite_eq_right (not_reverse (hinj t) hf), ite_eq_left hf, ← eval j i hf]
        exact (neg_sub _ _).symm
    · have he := hedge i j fun ⟨t,a,b,ha,hb⟩ => h ⟨t,a,b,ha,hb⟩
      rw [he, sub_self]
      symm
      apply Finset.sum_eq_zero
      intro t _
      exact row_eq_zero _ _ hne (fun ht => h ⟨t, ht⟩)

/-- Zero row sums determine the edges at an omitted vertex. When the point
count kills the coefficients, restoring those edges gives a zero-sum potential. -/
private theorem restore_potential {I A : Type*} [Fintype I] [AddCommGroup A]
    (edge : I → I → A) (root anchor : I) (hne : anchor ≠ root)
    (hdiag : ∀ i, edge i i = 0) (hflip : ∀ i j, edge i j = -edge j i)
    (hsum : ∀ i, ∑ j, edge i j = 0) (hann : ∀ x : A, Fintype.card I • x = 0)
    (hrest : ∀ i j, i ≠ root → j ≠ root → edge i j = edge anchor j - edge anchor i) :
    ∃! u : I → A, u anchor = 0 ∧ (∑ j, u j) = 0 ∧ ∀ i j, edge i j = u j - u i := by
  classical
  let partialSum : A := ∑ j ∈ Finset.univ.erase root, edge anchor j
  let u : I → A := fun j => if j = root then -partialSum else edge anchor j
  have hu (j : I) (hj : j ≠ root) : u j = edge anchor j := by simp [u, hj]
  have hanchor : u anchor = 0 := (hu anchor hne).trans (hdiag anchor)
  have htotal : (∑ j, u j) = 0 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root)]
    have hpart : (∑ j ∈ Finset.univ.erase root, u j) = partialSum := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hu j (Finset.ne_of_mem_erase hj)
    rw [hpart]
    simp [u]
  have hdiffsum (i : I) : (∑ j, (u j - u i)) = 0 := by
    rw [Finset.sum_sub_distrib, htotal, Finset.sum_const, Finset.card_univ, hann, sub_zero]
  have hnonroot (i j : I) (hi : i ≠ root) (hj : j ≠ root) :
      edge i j = u j - u i := by rw [hu i hi, hu j hj, hrest i j hi hj]
  have hroot (i : I) (hi : i ≠ root) : edge i root = u root - u i := by
    have hpart : (∑ j ∈ Finset.univ.erase root, edge i j) =
        ∑ j ∈ Finset.univ.erase root, (u j - u i) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hnonroot i j hi (Finset.ne_of_mem_erase hj)
    have left := hsum i
    have right := hdiffsum i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root), hpart] at left
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root)] at right
    exact add_left_cancel (left.trans right.symm)
  refine ⟨u, ⟨hanchor, htotal, ?_⟩, ?_⟩
  · intro i j
    by_cases hi : i = root
    · subst i
      by_cases hj : j = root
      · subst j
        rw [hdiag, sub_self]
      · rw [hflip root j, hroot j hj, neg_sub]
    · by_cases hj : j = root
      · subst j
        exact hroot i hi
      · exact hnonroot i j hi hj
  · intro w hw
    funext j
    have he := hw.2.2 anchor j
    rw [hw.1, sub_zero] at he
    by_cases hj : j = root
    · subst j
      exact he.symm.trans (by simpa [hanchor] using hroot anchor hne)
    · exact he.symm.trans (hu j hj).symm

private theorem row_flip {I A : Type*} [AddCommGroup A]
    {triangle : Fin 3 → I} (hinj : Function.Injective triangle) (value : A) (i j : I) :
    row triangle value i j = -row triangle value j i := by
  classical
  by_cases hf : forward triangle i j
  · simp [row, hf, not_reverse hinj hf]
  · by_cases hr : forward triangle j i <;> simp [row, hf, hr]

private theorem row_diag {I A : Type*} [AddCommGroup A]
    {triangle : Fin 3 → I} (hinj : Function.Injective triangle) (value : A) (i : I) :
    row triangle value i i = 0 := by
  classical
  have hf : ¬ forward triangle i i := fun h => not_reverse hinj h h
  simp [row, hf]

private theorem row_sum {I A : Type*} [Fintype I] [AddCommGroup A]
    {triangle : Fin 3 → I} (hinj : Function.Injective triangle) (value : A) (i : I) :
    (∑ j, row triangle value i j) = 0 := by
  classical
  have h01 := hinj.ne (by decide : (0 : Fin 3) ≠ 1)
  have h12 := hinj.ne (by decide : (1 : Fin 3) ≠ 2)
  have h20 := hinj.ne (by decide : (2 : Fin 3) ≠ 0)
  have indicator (a b : I) (hab : a ≠ b) :
      (∑ j : I, if j = a then value else if j = b then -value else 0) = 0 := by
    have split (j : I) :
        (if j = a then value else if j = b then -value else 0) =
          (if j = a then value else 0) + (if j = b then -value else 0) := by
      by_cases ha : j = a
      · subst j
        simp [hab]
      · simp [ha]
    simp only [split, Finset.sum_add_distrib]
    simp
  by_cases h0 : triangle 0 = i
  · subst i
    simpa [row, forward, h01, h01.symm, h12, h12.symm, h20, h20.symm, eq_comm] using
      indicator (triangle 1) (triangle 2) h12
  by_cases h1 : triangle 1 = i
  · subst i
    simpa [row, forward, h01, h01.symm, h12, h12.symm, h20, h20.symm, eq_comm] using
      indicator (triangle 2) (triangle 0) h20
  by_cases h2 : triangle 2 = i
  · subst i
    simpa [row, forward, h01, h01.symm, h12, h12.symm, h20, h20.symm, eq_comm] using
      indicator (triangle 0) (triangle 1) h01
  simp [row, forward, h0, h1, h2]

/-- A linear relation among the non-root triangle edge rows that is a potential
difference on those edges has a unique normalized potential on the whole ground
set. Both the potential values and the relation coefficients are killed by three. -/
private theorem triangle_relation_potential {I T A : Type*} [Fintype I] [Fintype T]
    [AddCommGroup A] (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j → covers (points t) i j → covers (points s) i j → t = s)
    (root anchor : I) (hne : anchor ≠ root) (hann : ∀ x : A, Fintype.card I • x = 0)
    (c : T → A) :
    let e (i j : I) := ∑ t, row (points t) (c t) i j
    (∀ i j, i ≠ root → j ≠ root → e i j = e anchor j - e anchor i) →
      (∀ t, 3 • c t = 0) ∧
      ∃! u : I → A, u anchor = 0 ∧ (∑ j, u j) = 0 ∧
        (∀ i, 3 • u i = 0) ∧ (∀ i j, e i j = u j - u i) := by
  classical
  intro e hrest
  have hdiag (i : I) : e i i = 0 := Finset.sum_eq_zero fun t _ => row_diag (hinj t) (c t) i
  have hflip (i j : I) : e i j = -e j i := by
    dsimp [e]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => row_flip (hinj t) (c t) i j)
  have hsum (i : I) : (∑ j, e i j) = 0 := by
    dsimp [e]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun t _ => row_sum (hinj t) (c t) i
  obtain ⟨u, hu, unique⟩ := restore_potential e root anchor hne hdiag hflip hsum hann hrest
  have hex : ∃ d : T → A, ∀ i j, i ≠ j → u j - u i = ∑ t, row (points t) (d t) i j :=
    ⟨c, fun i j _ => (hu.2.2 i j).symm⟩
  have ht := ((edge_rows_iff points hinj hdis u anchor).mp hex).1
  have kill (i : I) : 3 • u i = 0 := by simpa [hu.1] using ht i
  refine ⟨?_, u, ⟨hu.1, hu.2.1, kill, hu.2.2⟩, fun v hv => unique v ⟨hv.1, hv.2.1, hv.2.2.2⟩⟩
  intro t
  let i := points t 0
  let j := points t 1
  have hne' : i ≠ j := (hinj t).ne (by decide : (0 : Fin 3) ≠ 1)
  have ht' : covers (points t) i j := ⟨0, 1, rfl, rfl⟩
  have hsum' : e i j = row (points t) (c t) i j := by
    apply Finset.sum_eq_single_of_mem t (Finset.mem_univ _)
    intro s _ hst
    exact row_eq_zero _ _ hne' fun hs => hst (hdis s t i j hne' hs ht')
  have hfor : forward (points t) i j := Or.inl ⟨rfl, rfl⟩
  rw [row, ite_eq_left hfor, hu.2.2] at hsum'
  rw [← hsum']
  have he : (3 : ℕ) • (u j - u i) = (3 : ℕ) • u j - (3 : ℕ) • u i := by abel
  rw [he, kill, kill, sub_self]

/-- The signed sum of triangle rows with the given coefficients. -/
private noncomputable def sumRows {I T A : Type*} [Fintype T] [AddCommGroup A]
    (points : T → Fin 3 → I) (c : T → A) (i j : I) : A :=
  ∑ t, row (points t) (c t) i j

private theorem sumRows_eval {I T A : Type*} [Fintype T] [AddCommGroup A]
    (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j → covers (points t) i j → covers (points s) i j → t = s)
    (c : T → A) (t : T) : sumRows points c (points t 0) (points t 1) = c t := by
  classical
  let i := points t 0
  let j := points t 1
  have hne : i ≠ j := (hinj t).ne (by decide : (0 : Fin 3) ≠ 1)
  have ht : covers (points t) i j := ⟨0, 1, rfl, rfl⟩
  calc
    sumRows points c i j = row (points t) (c t) i j := by
      apply Finset.sum_eq_single_of_mem t (Finset.mem_univ _)
      intro s _ hst
      exact row_eq_zero _ _ hne fun hs => hst (hdis s t i j hne hs ht)
    _ = c t := by
      have hfor : forward (points t) i j := Or.inl ⟨rfl, rfl⟩
      rw [row, ite_eq_left hfor]

/-- The reduced equations express whether a signed sum of triangle rows
is a potential difference after the root coordinate is omitted. -/
private def IsReducedRelation {I T A : Type*} [Fintype T] [AddCommGroup A]
    (points : T → Fin 3 → I) (root anchor : I) (c : T → A) : Prop :=
  ∀ i j, i ≠ root → j ≠ root →
    sumRows points c i j = sumRows points c anchor j - sumRows points c anchor i

/-- A normalized point potential compatible with the omitted triangles. -/
def IsOmissionPotential {I T A : Type*} [Fintype I] [AddCommGroup A]
    (points : T → Fin 3 → I) (anchor : I) (u : I → A) : Prop :=
  u anchor = 0 ∧ (∑ i, u i) = 0 ∧
  (∀ i, 3 • u i = 0) ∧
  (∀ i j, (¬ ∃ t a b, points t a = i ∧ points t b = j) → u i = u j) ∧
  (∀ t, u (points t 0) + u (points t 1) + u (points t 2) = 0)

/-- Evaluation on each first oriented edge gives a bijection from normalized
point potentials to relations among the reduced omitted-triangle rows. -/
private theorem potential_to_relations_bijective {I T A : Type*} [Fintype I] [Fintype T]
    [AddCommGroup A] (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j → covers (points t) i j → covers (points s) i j → t = s)
    (root anchor : I) (hne : anchor ≠ root) (hann : ∀ x : A, Fintype.card I • x = 0) :
    let eval (u : I → A) (t : T) := u (points t 1) - u (points t 0)
    Set.BijOn eval (Set.ofPred (IsOmissionPotential points anchor))
      (Set.ofPred (IsReducedRelation points root anchor)) := by
  classical
  intro eval
  have realizable (u : I → A) (hu : IsOmissionPotential points anchor u) :
      ∀ i j, sumRows points (eval u) i j = u j - u i := by
    obtain ⟨c, hc⟩ := (edge_rows_iff points hinj hdis u anchor).mpr
      (by simpa [hu.1] using hu.2.2)
    have he (t : T) : eval u t = c t := by
      exact (hc _ _ ((hinj t).ne (by decide : (0 : Fin 3) ≠ 1))).trans
        (sumRows_eval points hinj hdis c t)
    intro i j
    by_cases hij : i = j
    · subst j
      rw [sub_self]
      exact Finset.sum_eq_zero fun t _ => row_diag (hinj t) (eval u t) i
    · rw [show eval u = c from funext he]
      exact (hc i j hij).symm
  refine ⟨?_, ?_, ?_⟩
  · intro u hu i j _ _
    simp only [realizable u hu]
    abel
  · intro u hu v hv hev
    funext i
    have h := (realizable u hu anchor i).symm.trans
      ((congrArg (fun c => sumRows points c anchor i) hev).trans (realizable v hv anchor i))
    have hu0 : u anchor = 0 := hu.1
    have hv0 : v anchor = 0 := hv.1
    rwa [hu0, hv0, sub_zero, sub_zero] at h
  · intro c hc
    obtain ⟨_, u, hu, _⟩ := triangle_relation_potential points hinj hdis root anchor hne hann c hc
    have he (t : T) : eval u t = c t :=
      (hu.2.2.2 (points t 0) (points t 1)).symm.trans (sumRows_eval points hinj hdis c t)
    have hrest := (edge_rows_iff points hinj hdis u anchor).mp
      ⟨c, fun i j _ => (hu.2.2.2 i j).symm⟩
    refine ⟨u, ⟨hu.1, hu.2.1, ?_⟩, funext he⟩
    simpa [hu.1] using hrest

private def affineLines : Fin 12 → Fin 3 → Fin 9 :=
  ![![0,1,2], ![0,3,6], ![0,4,8], ![0,5,7], ![1,3,8], ![1,4,7],
    ![1,5,6], ![2,3,7], ![2,4,6], ![2,5,8], ![3,4,5], ![6,7,8]]

private def affineFormula (a b : ZMod 3) : Fin 9 → ZMod 3 :=
  ![0, b, -b, a, a + b, a - b, -a, -a + b, -a - b]

private def lineConstraint (u : Fin 9 → ZMod 3) (i : Fin 12) : Prop :=
  u (affineLines i 0) + u (affineLines i 1) + u (affineLines i 2) = 0

/-- A zero-at-the-origin potential with zero sums on the twelve affine lines
is determined by its two coordinate slopes. -/
private theorem affine_plane_potential_coordinates (u : Fin 9 → ZMod 3) :
    (u 0 = 0 ∧ ∀ i, lineConstraint u i) ↔
      u = affineFormula (u 3) (u 1) := by
  have hthree : (3 : ZMod 3) = 0 := by decide
  constructor
  · rintro ⟨h0, h⟩
    have h012 : u 0 + u 1 + u 2 = 0 := h 0
    have h036 : u 0 + u 3 + u 6 = 0 := h 1
    have h048 : u 0 + u 4 + u 8 = 0 := h 2
    have h138 : u 1 + u 3 + u 8 = 0 := h 4
    have h147 : u 1 + u 4 + u 7 = 0 := h 5
    have h345 : u 3 + u 4 + u 5 = 0 := h 10
    have h2 : u 2 = -u 1 := by linear_combination h012 - h0
    have h6 : u 6 = -u 3 := by linear_combination h036 - h0
    have h8 : u 8 = -u 3 - u 1 := by linear_combination h138
    have h4 : u 4 = u 3 + u 1 := by linear_combination h048 - h138 - h0
    have h5 : u 5 = u 3 - u 1 := by
      linear_combination h345 - h4 - u 3 * hthree
    have h7 : u 7 = -u 3 + u 1 := by
      linear_combination h147 - h4 - u 1 * hthree
    funext i
    fin_cases i <;> first | assumption | rfl
  · intro h
    rw [h]
    refine ⟨rfl, fun i => ?_⟩
    fin_cases i <;> simp [lineConstraint, affineLines, affineFormula] <;> ring_nf <;> simp [hthree]

private theorem affine_plane_potential_card :
    Nat.card {u : Fin 9 → ZMod 3 // u 0 = 0 ∧ ∀ i, lineConstraint u i} = 9 := by
  classical
  let e : {u : Fin 9 → ZMod 3 // u 0 = 0 ∧ ∀ i, lineConstraint u i} ≃
      ZMod 3 × ZMod 3 :=
    { toFun := fun u => (u.val 3, u.val 1)
      invFun := fun s => ⟨affineFormula s.1 s.2,
        (affine_plane_potential_coordinates _).mpr rfl⟩
      left_inv := fun u => Subtype.ext ((affine_plane_potential_coordinates u.val).mp u.prop).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]

private theorem affine_triangle_injective :
    ∀ t, Function.Injective (affineLines t) := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem affine_pair_unique :
    ∀ t s i j, i ≠ j → covers (affineLines t) i j → covers (affineLines s) i j → t = s := by
  unfold covers
  decide

set_option maxRecDepth 8192 in
private theorem affine_pair_covered :
    ∀ i j : Fin 9, i ≠ j → ∃ t a b, affineLines t a = i ∧ affineLines t b = j := by decide

private theorem affine_compatible_iff (u : Fin 9 → ZMod 3) :
    IsOmissionPotential affineLines 0 u ↔ u 0 = 0 ∧ ∀ i, lineConstraint u i := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.2.2⟩
  · rintro ⟨h0, hline⟩
    have h012 : u 0 + u 1 + u 2 = 0 := hline 0
    have h345 : u 3 + u 4 + u 5 = 0 := hline 10
    have h678 : u 6 + u 7 + u 8 = 0 := hline 11
    refine ⟨h0, ?_, ?_, ?_, hline⟩
    · simp [Fin.sum_univ_succ]
      linear_combination h012 + h345 + h678
    · intro i
      rw [nsmul_eq_mul, show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
    · intro i j huncovered
      by_cases h : i = j
      · exact congrArg u h
      · exact (huncovered (affine_pair_covered i j h)).elim

/-- Ordered representatives of the unordered pairs remaining after two
coordinates have been eliminated. -/
def RemainingPair {I : Type*} [LinearOrder I] (root anchor : I) :=
  {ij : I × I // ij.1 < ij.2 ∧ ij.1 ≠ root ∧ ij.2 ≠ root ∧ ij.1 ≠ anchor ∧ ij.2 ≠ anchor}

/-- The omitted-triangle rows in the pair coordinates after eliminating a
root and a second coordinate. -/
noncomputable def reducedMatrix {I T R : Type*} [LinearOrder I] [CommRing R]
    (points : T → Fin 3 → I) (root anchor : I) : Matrix T (RemainingPair root anchor) R :=
  fun t ij =>
    let (i, j) := ij.val
    row (points t) 1 i j - row (points t) 1 anchor j + row (points t) 1 anchor i

private theorem row_mul {I R : Type*} [CommRing R] (triangle : Fin 3 → I)
    (c : R) (i j : I) : row triangle c i j = row triangle 1 i j * c := by
  classical
  by_cases h : forward triangle i j
  · simp [row, h]
  · by_cases h' : forward triangle j i <;> simp [row, h, h']

/-- The kernel of the transposed reduced matrix is precisely the space of
triangle coefficients satisfying the potential-difference equations. -/
private theorem reduced_transpose_kernel_iff {I T R : Type*} [LinearOrder I] [Fintype T] [CommRing R]
    (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (root anchor : I) (c : T → R) :
    (reducedMatrix points root anchor).transpose.mulVec c = 0 ↔
      IsReducedRelation points root anchor c := by
  classical
  let e := sumRows points c
  have coord (ij : RemainingPair root anchor) :
      ((reducedMatrix points root anchor).transpose.mulVec c) ij =
        e ij.val.1 ij.val.2 - e anchor ij.val.2 + e anchor ij.val.1 := by
    change (∑ t, (row (points t) (1 : R) ij.val.1 ij.val.2 -
        row (points t) 1 anchor ij.val.2 + row (points t) 1 anchor ij.val.1) * c t) = _
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← row_mul,
      e, sumRows]
  have diag (i : I) : e i i = 0 := Finset.sum_eq_zero fun t _ => row_diag (hinj t) (c t) i
  have flip (i j : I) : e i j = -e j i := by
    dsimp [e, sumRows]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => row_flip (hinj t) (c t) i j)
  constructor
  · intro h i j hi hj
    change e i j = e anchor j - e anchor i
    by_cases hia : i = anchor
    · subst i
      rw [diag, sub_zero]
    by_cases hja : j = anchor
    · subst j
      rw [diag, zero_sub, flip i anchor]
    have read (x y : I) (hlt : x < y) (hx : x ≠ root) (hy : y ≠ root)
        (hxa : x ≠ anchor) (hya : y ≠ anchor) : e x y = e anchor y - e anchor x := by
      let ij : RemainingPair root anchor := ⟨(x,y), hlt, hx, hy, hxa, hya⟩
      have hg := congrFun h ij
      rw [coord] at hg
      change e x y - e anchor y + e anchor x = 0 at hg
      calc
        e x y = (e x y - e anchor y + e anchor x) + (e anchor y - e anchor x) := by abel
        _ = _ := by rw [hg, zero_add]
    rcases lt_trichotomy i j with hij | hij | hij
    · exact read i j hij hi hj hia hja
    · subst j
      rw [diag, sub_self]
    · rw [flip i j, read j i hij hj hi hja hia, neg_sub]
  · intro h
    funext ij
    rw [coord]
    have he := h ij.val.1 ij.val.2 ij.prop.2.1 ij.prop.2.2.1
    change e ij.val.1 ij.val.2 = e anchor ij.val.2 - e anchor ij.val.1 at he
    rw [he]
    change e anchor ij.val.2 - e anchor ij.val.1 - e anchor ij.val.2 + e anchor ij.val.1 = 0
    abel

private noncomputable def marker {I R : Type*} [Zero R] [One R] (x y : I) : R :=
  open Classical in if x = y then 1 else 0

private noncomputable def edgeDet {I R : Type*} [Ring R] (i j x y : I) : R :=
  marker x i * marker y j - marker y i * marker x j

private theorem row_eq_edge_determinants {I R : Type*} [Ring R] (p : Fin 3 → I)
    (hp : Function.Injective p) (x y : I) :
    row p (1 : R) x y = edgeDet (p 0) (p 1) x y + edgeDet (p 1) (p 2) x y +
      edgeDet (p 2) (p 0) x y := by
  classical
  have h01 := hp.ne (by decide : (0 : Fin 3) ≠ 1)
  have h12 := hp.ne (by decide : (1 : Fin 3) ≠ 2)
  have h20 := hp.ne (by decide : (2 : Fin 3) ≠ 0)
  by_cases hx : x ∈ Set.range p
  · obtain ⟨i, rfl⟩ := hx
    by_cases hy : y ∈ Set.range p
    · obtain ⟨j, rfl⟩ := hy
      fin_cases i <;> fin_cases j <;>
        simp [row, forward, edgeDet, marker, h01, h01.symm, h12, h12.symm, h20, h20.symm]
    · have nh (j : Fin 3) : p j ≠ y := fun h => hy ⟨j, h⟩
      simp [row, forward, edgeDet, marker, nh, fun j => (nh j).symm]
  · have nh (i : Fin 3) : p i ≠ x := fun h => hx ⟨i, h⟩
    simp [row, forward, edgeDet, marker, nh, fun i => (nh i).symm]

/-- Each reduced row entry is the determinant of the corresponding two
quotient coordinates of the two differences of the triangle. -/
private theorem reducedMatrix_eq_determinant {I T R : Type*} [LinearOrder I] [CommRing R]
    (points : T → Fin 3 → I) (root anchor : I) (t : T)
    (ht : Function.Injective (points t)) (ij : RemainingPair root anchor) :
    let s (p x : I) : R := marker p x - marker anchor x
    let delta (k : Fin 3) (p : I) := s p (points t k) - s p (points t 0)
    (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) R) t ij =
      delta 1 ij.val.1 * delta 2 ij.val.2 - delta 1 ij.val.2 * delta 2 ij.val.1 := by
  intro s delta
  change row (points t) (1 : R) ij.val.1 ij.val.2 -
    row (points t) 1 anchor ij.val.2 + row (points t) 1 anchor ij.val.1 = _
  simp only [row_eq_edge_determinants _ ht, edgeDet, delta, s]
  ring


open Set.powersetCard

/-- The two active indices of a basis coordinate, taken in increasing order. -/
private noncomputable def pairIndexEquiv {I : Type*} [LinearOrder I] (root anchor : I) :
    RemainingPair root anchor ≃ {s : Set.powersetCard I 2 // root ∉ s.val ∧ anchor ∉ s.val} := by
  classical
  let asEmb : RemainingPair root anchor →
      {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} := fun p => by
    let e : Fin 2 → I := ![p.val.1, p.val.2]
    have he : StrictMono e := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (lt_irrefl _ hij).elim
      · exact p.prop.1
      · exact ((by decide : ¬ (1 : Fin 2) < 0) hij).elim
      · exact (lt_irrefl _ hij).elim
    refine ⟨OrderEmbedding.ofStrictMono e he, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact p.prop.2.1
      · exact p.prop.2.2.1
    · intro i
      fin_cases i
      · exact p.prop.2.2.2.1
      · exact p.prop.2.2.2.2
  let fromEmb :
      {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} →
        RemainingPair root anchor := fun e =>
    ⟨(e.val 0, e.val 1), e.val.strictMono (by decide), e.prop.1 0, e.prop.1 1,
      e.prop.2 0, e.prop.2 1⟩
  let embedded : RemainingPair root anchor ≃
      {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} :=
    { toFun := asEmb
      invFun := fromEmb
      left_inv := fun _ => rfl
      right_inv := by
        intro e
        apply Subtype.ext
        ext i
        fin_cases i <;> rfl }
  let subsets : {e : Fin 2 ↪o I // (∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)} ≃
      {s : Set.powersetCard I 2 // root ∉ s.val ∧ anchor ∉ s.val} := by
    apply ofFinEmbEquiv.subtypeEquiv
    intro e
    change ((∀ i, e i ≠ root) ∧ (∀ i, e i ≠ anchor)) ↔
      root ∉ ofFinEmbEquiv e ∧ anchor ∉ ofFinEmbEquiv e
    simp only [mem_ofFinEmbEquiv_iff_mem_range, Set.mem_range, not_exists]
  exact embedded.trans subsets

private theorem pairIndexEquiv_first {I : Type*} [LinearOrder I] (root anchor : I)
    (ij : RemainingPair root anchor) :
    ofFinEmbEquiv.symm ((pairIndexEquiv root anchor) ij).val 0 = ij.val.1 := by
  simp [pairIndexEquiv]
  rfl

private theorem pairIndexEquiv_second {I : Type*} [LinearOrder I] (root anchor : I)
    (ij : RemainingPair root anchor) :
    ofFinEmbEquiv.symm ((pairIndexEquiv root anchor) ij).val 1 = ij.val.2 := by
  simp [pairIndexEquiv]
  rfl

open Finset CircuitDifferenceBasis

/-- In the unit-weight case the root, total difference vector, and the other
point differences form an explicit integral basis. -/
private theorem unit_difference_basis {I : Type*} [Fintype I] [DecidableEq I]
    (root anchor : I) (h : anchor ≠ root) :
    ∃ b : Module.Basis I ℤ (I → ℤ),
      b root = Pi.single root 1 ∧
      b anchor = ∑ i ∈ univ.erase root, (Pi.single i 1 - Pi.single root 1) ∧
      ∀ i, i ≠ root → i ≠ anchor → b i = Pi.single i 1 - Pi.single root 1 := by
  obtain ⟨c, hc0, hc, _⟩ := exists_difference_basis {anchor} root anchor
    (by simpa [eq_comm] using h) (by simp)
  have hc' (i : I) (hi : i ≠ root) : c i = Pi.single i 1 - Pi.single root 1 := by
    simpa using hc i hi
  let w := ∑ i ∈ univ.erase root, c i
  let u := w - c anchor
  have hker : c.coord anchor u = 0 := by
    dsimp [u, w]
    rw [map_sub, map_sum]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, h]
  let b := c.map (LinearEquiv.transvection hker)
  have hb (i : I) : b i = c i + c.coord anchor (c i) • u := by
    rw [Module.Basis.map_apply]
    rfl
  have hcoord (i : I) : c.coord anchor (c i) = if i = anchor then 1 else 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb, hcoord, ite_eq_right h.symm, zero_smul, add_zero, hc0]
  · rw [hb, hcoord, ite_eq_left rfl, one_smul]
    have hadd : c anchor + u = w := by dsimp [u]; abel
    rw [hadd]
    apply sum_congr rfl
    intro i hi
    exact hc' i (ne_of_mem_erase hi)
  · intro i hi ha
    rw [hb, hcoord, ite_eq_right ha, zero_smul, add_zero, hc' i hi]

/-- The active coordinates of each original point difference have a
unit contribution at that point and a negative contribution at the anchor. -/
private theorem active_difference_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (root anchor k x : I) (hne : anchor ≠ root) (hk : k ≠ root) (hka : k ≠ anchor)
    (b : Module.Basis I ℤ (I → ℤ))
    (ha : b anchor = ∑ i ∈ univ.erase root, (Pi.single i 1 - Pi.single root 1))
    (hb : ∀ i, i ≠ root → i ≠ anchor → b i = Pi.single i 1 - Pi.single root 1) :
    b.coord k (Pi.single x 1 - Pi.single root 1) =
      (if x = k then 1 else 0) - (if x = anchor then 1 else 0) := by
  have eval (i : I) : b.coord k (b i) = if i = k then 1 else 0 := by
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have haMem : anchor ∈ univ.erase root := mem_erase.mpr ⟨hne, mem_univ _⟩
  by_cases hx : x = root
  · subst x
    simp [hk.symm, hne.symm]
  by_cases hxa : x = anchor
  · subst x
    have split :
        (∑ i ∈ (univ.erase root).erase anchor, b i) +
          (Pi.single anchor 1 - Pi.single root 1 : I → ℤ) = b anchor := by
      rw [ha, ← sum_erase_add _ _ haMem]
      congr 1
      apply sum_congr rfl
      intro i hi
      exact hb i (ne_of_mem_erase (mem_of_mem_erase hi)) (ne_of_mem_erase hi)
    have hcast := congrArg (b.coord k) split
    simp only [map_add, map_sum, eval, hka.symm] at hcast
    have hsum : (∑ i ∈ (univ.erase root).erase anchor, if i = k then (1 : ℤ) else 0) = 1 := by
      simp [mem_erase, hka, hk]
    rw [hsum] at hcast
    simp [hka.symm, ← neg_eq_of_add_eq_zero_right hcast]
  · rw [← hb x hx hxa, eval, ite_eq_right hxa, sub_zero]

open Finset UniformCircuitResidueForms Set.powersetCard

/-- Expand an alternating form by the determinants of its input coordinates
in the integral basis. -/
private theorem form_eval_eq_sum_det {I M N : Type*} [Fintype I] [LinearOrder I]
    [AddCommGroup M] [AddCommGroup N] {k : ℕ} (b : Module.Basis I ℤ M)
    (f : M [⋀^Fin k]→ₗ[ℤ] N) (v : Fin k → M) :
    f v = ∑ s : Set.powersetCard I k,
      (Matrix.of fun i j => b.coord (ofFinEmbEquiv.symm s j) (v i)).det •
        (basisFormEquiv b).symm f s := by
  classical
  let extBasis := b.exteriorPower k
  let form := exteriorPower.alternatingMapLinearEquiv f
  let z := exteriorPower.ιMulti ℤ k v
  have hsum := congrArg form (extBasis.sum_repr z)
  rw [map_sum] at hsum
  simp only [map_smul] at hsum
  calc
    f v = form z := by exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _).symm
    _ = ∑ s, extBasis.repr z s • form (extBasis s) := hsum.symm
    _ = _ := by
      apply sum_congr rfl
      intro s _
      rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
      congr 1

open UniformCircuitResidueForms

/-- A two-form vanishing at the two eliminated vectors reads each omitted
triangle through the corresponding row of the reduced matrix. -/
private theorem reduced_readout {I T N : Type*} [Fintype I] [LinearOrder I] [AddCommGroup N]
    (points : T → Fin 3 → I) (t : T) (ht : Function.Injective (points t))
    (root anchor : I) (hne : anchor ≠ root) [Fintype (RemainingPair root anchor)]
    (b : Module.Basis I ℤ (I → ℤ))
    (ha : b anchor = ∑ i ∈ Finset.univ.erase root, (Pi.single i 1 - Pi.single root 1))
    (hb : ∀ i, i ≠ root → i ≠ anchor → b i = Pi.single i 1 - Pi.single root 1)
    (f : (I → ℤ) [⋀^Fin 2]→ₗ[ℤ] N)
    (hfroot : f.curryLeft (b root) = 0) (hfanchor : f.curryLeft (b anchor) = 0) :
    let dif (i : I) := Pi.single i (1 : ℤ) - Pi.single root 1
    let term (p : RemainingPair root anchor) := (basisFormEquiv b).symm f ((pairIndexEquiv root anchor) p).val
    f ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] =
      ∑ ij, (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) ℤ) t ij • term ij := by
  classical
  intro dif term
  let vv : Fin 2 → I → ℤ :=
    ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)]
  let C (s : Set.powersetCard I 2) :=
    (Matrix.of fun i j => b.coord (ofFinEmbEquiv.symm s j) (vv i)).det • (basisFormEquiv b).symm f s
  let admissible (s : Set.powersetCard I 2) := root ∉ s.val ∧ anchor ∉ s.val
  have coord_zero (i : I) (hz : f.curryLeft (b i) = 0)
      (s : Set.powersetCard I 2) (hs : i ∈ s.val) : (basisFormEquiv b).symm f s = 0 := by
    have hh := ((curryLeft_smul_basis_eq_zero_iff b f (1 : ℤ) i).mp
      (by simpa only [one_smul] using hz)) s hs
    simpa only [one_smul] using hh
  have excluded : (∑ s : {s // ¬ admissible s}, C s.val) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    have hs : root ∈ s.val.val ∨ anchor ∈ s.val.val := by
      by_cases hr : root ∈ s.val.val
      · exact Or.inl hr
      · exact Or.inr (Classical.not_not.mp fun h => s.prop ⟨hr, h⟩)
    rcases hs with h | h
    · dsimp [C]
      rw [coord_zero _ hfroot _ h, smul_zero]
    · dsimp [C]
      rw [coord_zero _ hfanchor _ h, smul_zero]
  change f vv = _
  rw [form_eval_eq_sum_det b f vv]
  change (∑ s, C s) = _
  rw [← Fintype.sum_subtype_add_sum_subtype admissible C, excluded, add_zero]
  symm
  refine Fintype.sum_equiv (pairIndexEquiv root anchor) _ _ ?_
  intro ij
  change _ • term ij = C ((pairIndexEquiv root anchor) ij).val
  have markerCoord (k x : I) (hk : k ≠ root) (hka : k ≠ anchor) :
      b.coord k (dif x) = (marker k x : ℤ) - marker anchor x := by
    dsimp [dif, marker]
    rw [active_difference_coordinate root anchor k x hne hk hka b ha hb]
    by_cases hx : x = k
    · subst x
      simp [hka, hka.symm]
    by_cases hxa : x = anchor
    · subst x
      simp [hka, hka.symm]
    simp [hx, hxa, Ne.symm (show x ≠ k from hx), Ne.symm (show x ≠ anchor from hxa)]
  have coord1 (x : I) : b.coord ij.val.1 (dif x) =
      (marker ij.val.1 x : ℤ) - marker anchor x :=
    markerCoord _ _ ij.prop.2.1 ij.prop.2.2.2.1
  have coord2 (x : I) : b.coord ij.val.2 (dif x) =
      (marker ij.val.2 x : ℤ) - marker anchor x :=
    markerCoord _ _ ij.prop.2.2.1 ij.prop.2.2.2.2
  congr 1
  rw [reducedMatrix_eq_determinant points root anchor t ht ij]
  simp only [Matrix.det_fin_two, Matrix.of_apply, pairIndexEquiv_first,
    pairIndexEquiv_second, vv, Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, coord1, coord2]

open UniformCircuitResidueDiagonal

private noncomputable def activeCoordinates {I N : Type*} [LinearOrder I] [AddCommGroup N]
    (root anchor : I) (n : ℤ) :
    diagonalCoordinates N 2 root anchor n 1 ≃ₗ[ℤ]
      (RemainingPair root anchor → ↥(Submodule.torsionBy ℤ N n)) := by
  let P := Submodule.torsionBy ℤ N n
  let Q := P ⊓ Submodule.torsionBy ℤ N 1
  haveI : Subsingleton ↥Q := ⟨fun x y => Subtype.ext (by
    have hx : (1 : ℤ) • x.val = 0 := x.prop.2
    have hy : (1 : ℤ) • y.val = 0 := y.prop.2
    simpa only [one_smul] using hx.trans hy.symm)⟩
  let A := {F : Set.powersetCard I 2 // root ∉ F ∧ anchor ∈ F}
  letI : Unique (A → Q) := ⟨⟨0⟩, fun x => Subsingleton.elim x 0⟩
  exact ((diagonalCoordinatesEquiv (N := N) (r := 2) root anchor n 1).trans
    LinearEquiv.uniqueProd).trans
      (LinearEquiv.piCongrLeft' ℤ (fun _ => ↥P) (pairIndexEquiv root anchor).symm)

private theorem activeCoordinates_apply {I N : Type*} [LinearOrder I] [AddCommGroup N]
    (root anchor : I) (n : ℤ) (x : diagonalCoordinates N 2 root anchor n 1)
    (ij : RemainingPair root anchor) :
    ((activeCoordinates (N := N) root anchor n x ij) : N) = x.val ((pairIndexEquiv root anchor) ij).val := rfl

noncomputable instance instRemainingPairFintype {I : Type*} [Fintype I] [LinearOrder I]
    (root anchor : I) : Fintype (RemainingPair root anchor) := by
  classical
  let e := pairIndexEquiv root anchor
  exact Fintype.ofEquiv _ e.symm

private theorem unit_total_vector {I : Type*} [Fintype I] [DecidableEq I]
    (root anchor : I) (b : Module.Basis I ℤ (I → ℤ))
    (hr : b root = Pi.single root 1)
    (ha : b anchor = ∑ i ∈ Finset.univ.erase root, (Pi.single i 1 - Pi.single root 1)) :
    (∑ i, Pi.single i (1 : ℤ)) = (Fintype.card I : ℤ) • b root + b anchor := by
  rw [hr, ha, Finset.sum_sub_distrib, Finset.sum_const]
  have hn : ((Finset.univ.erase root : Finset I).card : ℤ) + 1 = Fintype.card I := by
    exact_mod_cast (by rw [Finset.card_erase_add_one (Finset.mem_univ root), Finset.card_univ] :
      (Finset.univ.erase root : Finset I).card + 1 = Fintype.card I)
  rw [← hn, add_zsmul, one_zsmul, Nat.cast_smul_eq_nsmul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ root)]
  abel



open Function Matrix
open scoped Matroid
open SparsePavingCircuitCoordinates ParallelCircuitObstruction UniformCircuitBasis
open RationalJointCircuitImage (RationalResidue)
open RankTwoCircuitInvariantFactors (ResidueTorsion residueTorsion_equiv_zmod gcd_torsion_iff)
open JointCircuitLiftingObstruction (JointSaturatedImage JointImageInSaturation)

private theorem reducedMatrix_intCast {I T R : Type*} [LinearOrder I] [CommRing R]
    (points : T → Fin 3 → I) (root anchor : I) (t : T) (ij : RemainingPair root anchor) :
    ↑((reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) ℤ) t ij) =
      (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) R) t ij := by
  classical
  have castRow (i j : I) : ↑(row (points t) (1 : ℤ) i j) = (row (points t) 1 i j : R) := by
    by_cases h : forward (points t) i j
    · simp [row, h]
    by_cases h' : forward (points t) j i <;> simp [row, h, h']
  simp [reducedMatrix, castRow]

/-- The integral joint lifting obstruction for a rank-three sparse-paving matroid
with singleton parallel classes is the kernel of its reduced omitted-triangle matrix. -/
theorem rank_three_lifting_obstruction_equiv_kernel {I T : Type*}
    [Fintype I] [LinearOrder I] (M : Matroid I) (triangles : T → Fin 3 ↪o I)
    (root anchor : I) (hne : anchor ≠ root) (hn : 3 < Fintype.card I)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (hground : M.E = Set.univ)
    (hbase : ∀ B : Finset I, M.IsBase (B : Set I) ↔
      B.card = 3 ∧ B ∉ Set.range fun t => (ofFinEmbEquiv (triangles t)).val) :
    Nonempty ((JointSaturatedImage (M.comap (id : I → I)) ⧸
      JointImageInSaturation (M.comap (id : I → I))) ≃ₗ[ℤ]
      ((reducedMatrix (fun t => triangles t) root anchor :
        Matrix T (RemainingPair root anchor) (ZMod (Fintype.card I))).mulVecLin.ker.restrictScalars ℤ)) := by
  classical
  let n := Fintype.card I
  have hn0 : n ≠ 0 := by omega
  let _ : Nonempty I := ⟨root⟩
  let points (t : T) : Fin 3 → I := triangles t
  let holes : Set (Finset I) := Set.range fun t => (ofFinEmbEquiv (triangles t)).val
  have hsize (H : Finset I) (hH : H ∈ holes) : H.card = 3 := by
    obtain ⟨t, rfl⟩ := hH
    exact (ofFinEmbEquiv (triangles t)).prop
  have hnonloop (i : I) : M.IsNonloop i := by
    apply Matroid.indep_singleton.mp
    rw [← coe_singleton, indep_iff_card_and_allowed (holes := holes) hn hsize hsparse hbase]
    refine ⟨by simp, fun h => ?_⟩
    have := hsize _ h
    simp at this
  obtain ⟨comparison, _⟩ := parallel_lifting_obstruction (M := M) Function.surjective_id
    (fun {_ _} h => h) hnonloop
  let standard := Pi.basisFun ℤ I
  let a := sumCovector I
  have ha (i : I) : a (standard i) = 1 := by simp [a, sumCovector, standard, Pi.basisFun]
  let idx (H : holes) : T := H.prop.choose
  have hidx (H : holes) : (ofFinEmbEquiv (triangles (idx H))).val = H.val := H.prop.choose_spec
  let rep (H : holes) : I := triangles (idx H) 0
  have hrep (H : holes) : rep H ∈ H.val := by
    rw [← hidx H]
    exact (mem_ofFinEmbEquiv_iff_mem_range _ _).mpr ⟨0, rfl⟩
  obtain ⟨pivot⟩ := sparse_paving_pivot_forms_equiv (id : I → I) (d := 1) hn
    hsize hsparse hground hbase standard a ha root rep hrep
  let y := ∑ i, (univ.filter fun x : I => id x = i).card • standard i
  have hstd (i : I) : standard i = Pi.single i 1 := Pi.basisFun_apply ℤ I i
  have hy : y = ∑ i, standard i := by
    simp only [y, id_eq, filter_eq', mem_univ, ite_true, card_singleton, one_nsmul]
  have hay : a y = n := by
    rw [hy, map_sum]
    simp [ha, n]
  obtain ⟨b, hbroot, hbanchor, hb⟩ := unit_difference_basis root anchor hne
  have hy' : y = (n : ℤ) • b root + b anchor :=
    hy.trans ((Finset.sum_congr rfl fun i _ => hstd i).trans
      (unit_total_vector root anchor b hbroot hbanchor))
  let F := (I → ℤ) [⋀^Fin 2]→ₗ[ℤ] RationalResidue
  let P := ((insertVector (N := RationalResidue) (n := 1) (standard root)).ker ⊓
    (insertVector y).ker) ⊓ Submodule.torsionBy ℤ F (a y)
  let tuple (H : holes) (i : Fin 2) :=
    let S : Set.powersetCard I 2 := ⟨H.val.erase (rep H), by
      change (H.val.erase (rep H)).card = 2
      rw [card_erase_of_mem (hrep H), hsize H.val H.prop]⟩
    standard (ofFinEmbEquiv.symm S i) - standard (rep H)
  let eval (H : holes) : F →ₗ[ℤ] RationalResidue :=
    { toFun := fun f => f (tuple H)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change weightedCircuitResidues M (id : I → I) ≃ₗ[ℤ] ↥(P ⊓ ⨅ H, (eval H).ker) at pivot
  let D := diagonalCoordinates RationalResidue 2 root anchor n 1
  have diag (f : F) : f ∈ P ↔ (basisFormEquiv b).symm f ∈ D := by
    change (f.curryLeft (standard root) = 0 ∧ f.curryLeft y = 0) ∧ a y • f = 0 ↔ _
    rw [hay]
    have hr : standard root = b root := (hstd root).trans hbroot.symm
    rw [hr, hy']
    simpa only [one_smul, and_assoc] using (reduced_equations b root anchor n 1 f)
  let diagonal : P ≃ₗ[ℤ] D := (basisFormEquiv b).symm.ofSubmodules P D (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext g
    change (basisFormEquiv b) g ∈ P ↔ g ∈ D
    rw [diag, LinearEquiv.symm_apply_apply])
  obtain ⟨zmod⟩ := residueTorsion_equiv_zmod n hn0
  let coord := (diagonal.trans (activeCoordinates root anchor n)).trans
    (LinearEquiv.piCongrRight fun _ : RemainingPair root anchor => zmod)
  let A : Matrix T (RemainingPair root anchor) (ZMod n) := reducedMatrix points root anchor
  let K := A.mulVecLin.ker.restrictScalars ℤ
  let dif (i : I) : I → ℤ := Pi.single i 1 - Pi.single root 1
  have read (f : P) (t : T) :
      A.mulVec (coord f) t = 0 ↔
        f.val ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] = 0 := by
    have hr : f.val.curryLeft (b root) = 0 := by
      rw [hbroot, ← hstd]
      exact f.prop.1.1
    have hyzero : f.val.curryLeft y = 0 := f.prop.1.2
    have hfanchor : f.val.curryLeft (b anchor) = 0 := by
      rwa [hy', map_add, map_smul, hr, smul_zero, zero_add] at hyzero
    let v := activeCoordinates (N := RationalResidue) root anchor (n : ℤ) (diagonal f)
    let w : ResidueTorsion n := ∑ ij,
      (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) ℤ) t ij • v ij
    have hz : A.mulVec (coord f) t = zmod w := by
      change (∑ ij, A t ij * zmod (v ij)) = zmod w
      simp only [w, map_sum, map_zsmul, zsmul_eq_mul, reducedMatrix_intCast, A]
    have hw : (w : RationalResidue) =
        f.val ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] := by
      rw [reduced_readout points t (triangles t).injective root anchor hne b hbanchor hb f.val hr hfanchor]
      change ((ResidueTorsion n).subtype w) = _
      simp only [w, map_sum, map_zsmul, v, activeCoordinates_apply]
      rfl
    rw [hz, ← hw, ← zmod.map_zero, zmod.injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext (by exact h)⟩
  have tuple_eq (t : T) (H : holes) (hH : (ofFinEmbEquiv (triangles t)).val = H.val)
      (he : triangles t = triangles (idx H)) :
      tuple H = ![dif (points t 1) - dif (points t 0), dif (points t 2) - dif (points t 0)] := by
    let E := (Fin.succAboveOrderEmb (0 : Fin 3)).trans (triangles t)
    have hr : triangles t 0 = rep H := congrArg (fun e : Fin 3 ↪o I => e 0) he
    have herm : (ofFinEmbEquiv E).val = H.val.erase (rep H) := by
      rw [face_embedding_erase, hH, hr]
    have hS : ofFinEmbEquiv E = ⟨H.val.erase (rep H), by
        change (H.val.erase (rep H)).card = 2
        rw [card_erase_of_mem (hrep H), hsize H.val H.prop]⟩ := Subtype.ext herm
    funext i
    dsimp only [tuple]
    rw [← hS, Equiv.symm_apply_apply, ← hr]
    simp only [hstd]
    fin_cases i <;> simp [E, dif, points] <;> abel
  have hcoord (f : P) : f.val ∈ (⨅ H, (eval H).ker) ↔ coord f ∈ K := by
    simp only [K, Submodule.restrictScalars_mem, Submodule.mem_iInf, LinearMap.mem_ker]
    change (∀ H, f.val (tuple H) = 0) ↔ A.mulVec (coord f) = 0
    rw [funext_iff]
    constructor
    · intro h t
      let H : holes := ⟨_, ⟨t, rfl⟩⟩
      have he : triangles t = triangles (idx H) :=
        ofFinEmbEquiv.injective (Subtype.ext (hidx H).symm)
      exact (read f t).mpr (tuple_eq t H rfl he ▸ h H)
    · intro h H
      rw [tuple_eq (idx H) H (hidx H) rfl]
      exact (read f (idx H)).mp (h _)
  let P' := (⨅ H, (eval H).ker).comap P.subtype
  let restrict : ↥(P ⊓ ⨅ H, (eval H).ker) ≃ₗ[ℤ] P' :=
    { toFun := fun f => ⟨⟨f.val, f.prop.1⟩, f.prop.2⟩
      invFun := fun f => ⟨f.val.val, ⟨f.val.prop, f.prop⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let finish := coord.ofSubmodules P' K (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext z
    change (coord.symm z).val ∈ (⨅ H, (eval H).ker) ↔ _
    rw [hcoord, LinearEquiv.apply_symm_apply])
  exact ⟨comparison.trans (pivot.trans (restrict.trans finish))⟩

/-- The cokernel of a matrix over a finite residue ring has the same size
as the kernel of its transpose. This uses the perfect character pairing. -/
private theorem transpose_kernel_card_eq_cokernel {m n : Type*} [Fintype m] [Fintype n]
    (q : ℕ) [NeZero q] (A : Matrix m n (ZMod q)) :
    Nat.card {y : m → ZMod q // A.transpose.mulVec y = 0} =
      Nat.card ((m → ZMod q) ⧸ LinearMap.range A.mulVecLin) := by
  classical
  let P := LinearMap.range A.mulVecLin
  let Q := (m → ZMod q) ⧸ P
  let dot := dotProductEquiv (ZMod q) m
  let χ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hχ : Injective χ := ZMod.injective_stdAddChar
  let pull (y : m → ZMod q) : AddChar (m → ZMod q) ℂ :=
    χ.compAddMonoidHom (dot y).toAddMonoidHom
  have hpull : Bijective pull := by
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    refine ⟨?_, rfl⟩
    intro y z h
    have he := AddChar.compAddMonoidHom_injective_right χ hχ h
    apply dot.injective
    exact LinearMap.ext fun x => congrArg (fun f : (m → ZMod q) →+ ZMod q => f x) he
  have transport (y : m → ZMod q) (x : n → ZMod q) :
      dot y (A.mulVec x) = dotProduct (A.transpose.mulVec y) x := by
    change dotProduct y (A.mulVec x) = _
    rw [dotProduct_mulVec, mulVec_transpose]
  have vanishes (y : m → ZMod q) (hy : A.transpose.mulVec y = 0) :
      P ≤ LinearMap.ker (dot y) := by
    rintro z ⟨x, rfl⟩
    change dot y (A.mulVec x) = 0
    rw [transport, hy, zero_dotProduct]
  let forward (y : {y : m → ZMod q // A.transpose.mulVec y = 0}) : AddChar Q ℂ :=
    χ.compAddMonoidHom (P.liftQ (dot y.val) (vanishes y.val y.prop)).toAddMonoidHom
  have eval (y : {y : m → ZMod q // A.transpose.mulVec y = 0}) (z : m → ZMod q) :
      forward y (P.mkQ z) = pull y.val z := rfl
  have hforward : Bijective forward := by
    constructor
    · intro y z h
      apply Subtype.ext
      apply hpull.injective
      ext x
      rw [← eval, ← eval, h]
    · intro ψ
      obtain ⟨y, hy⟩ := hpull.surjective (ψ.compAddMonoidHom P.mkQ.toAddMonoidHom)
      have hy' (x : n → ZMod q) : dotProduct (A.transpose.mulVec y) x = 0 := by
        have hmem : A.mulVec x ∈ P := ⟨x, rfl⟩
        have hzero : P.mkQ (A.mulVec x) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hmem
        have h := DFunLike.congr_fun hy (A.mulVec x)
        change χ (dot y (A.mulVec x)) = ψ (P.mkQ (A.mulVec x)) at h
        apply hχ
        rw [← transport, h, hzero, AddChar.map_zero_eq_one, AddChar.map_zero_eq_one]
      have hk : A.transpose.mulVec y = 0 := by
        funext i
        simpa only [dotProduct_single_one, Pi.zero_apply] using hy' (Pi.single i 1)
      let v : {y : m → ZMod q // A.transpose.mulVec y = 0} := ⟨y, hk⟩
      refine ⟨v, ?_⟩
      ext x
      obtain ⟨z, rfl⟩ := P.mkQ_surjective x
      rw [eval, show v.val = y from rfl, hy]
      rfl
  have hcard : Nat.card (AddChar Q ℂ) = Nat.card Q := by
    let _ : Fintype Q := Fintype.ofFinite Q
    simp only [Nat.card_eq_fintype_card, AddChar.card_eq]
  exact (Nat.card_congr (Equiv.ofBijective forward hforward)).trans hcard

/-- Counting the image in two ways relates the primal and transpose kernels. -/
private theorem primal_kernel_card_mul {m n : Type*} [Fintype m] [Fintype n]
    (q : ℕ) [NeZero q] (A : Matrix m n (ZMod q)) :
    Nat.card {x : n → ZMod q // A.mulVec x = 0} * q ^ Fintype.card m =
      q ^ Fintype.card n * Nat.card {y : m → ZMod q // A.transpose.mulVec y = 0} := by
  let f := A.mulVecLin
  have hX : Nat.card (n → ZMod q) = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
      Nat.card_congr f.quotKerEquivRange.toEquiv]
  have hY : Nat.card (m → ZMod q) = Nat.card (LinearMap.range f) *
      Nat.card {y : m → ZMod q // A.transpose.mulVec y = 0} := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range f),
      ← transpose_kernel_card_eq_cokernel q A]
  have cardM : Nat.card (m → ZMod q) = q ^ Fintype.card m := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card]
  have cardN : Nat.card (n → ZMod q) = q ^ Fintype.card n := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_eq_fintype_card]
  rw [← cardM, ← cardN, hY, hX]
  change Nat.card (LinearMap.ker f) * (_ * _) = _
  exact (Nat.mul_assoc _ _ _).symm

private theorem map_reducedMatrix_mulVec {I T R S : Type*}
    [Fintype I] [LinearOrder I] [CommRing R] [CommRing S]
    (points : T → Fin 3 → I) (root anchor : I) (f : R →+ S)
    (x : RemainingPair root anchor → R) :
    f ∘ (reducedMatrix points root anchor).mulVec x =
      (reducedMatrix points root anchor).mulVec (f ∘ x) := by
  funext t
  change f (∑ ij, (reducedMatrix points root anchor) t ij * x ij) =
    ∑ ij, (reducedMatrix points root anchor) t ij * f (x ij)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← reducedMatrix_intCast (R := R), ← reducedMatrix_intCast (R := S)]
  simpa only [zsmul_eq_mul] using f.map_zsmul
    ((reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) ℤ) t ij) (x ij)

private theorem affine_lines_increasing : ∀ t, StrictMono (affineLines t) := by decide

private def affineTriangle (t : Fin 12) : Fin 3 ↪o Fin 9 :=
  OrderEmbedding.ofStrictMono (affineLines t) (affine_lines_increasing t)

/-- The twelve affine lines on the nine points, numbered in row-major order. -/
def affineOmissions : Set (Finset (Fin 9)) :=
  Set.range fun t => (ofFinEmbEquiv (affineTriangle t)).val

private theorem zmod_torsion_embedding (q s : ℕ) (hq : 0 < q) :
    ∃ f : ZMod (q.gcd s) →+ ZMod q, Injective f ∧
      ∀ y : ZMod q, s • y = 0 ↔ y ∈ Set.range f := by
  obtain ⟨eqQ⟩ := residueTorsion_equiv_zmod q hq.ne'
  obtain ⟨eqG⟩ := residueTorsion_equiv_zmod (q.gcd s) (Nat.gcd_pos_of_pos_left s hq).ne'
  have incl : ResidueTorsion (q.gcd s) ≤ ResidueTorsion q :=
    fun x hx => ((gcd_torsion_iff q s x).mp hx).1
  let e := eqQ.toLinearMap.comp ((Submodule.inclusion incl).comp eqG.symm.toLinearMap)
  refine ⟨e.toAddMonoidHom, eqQ.injective.comp
    ((Submodule.inclusion_injective incl).comp eqG.symm.injective), fun y => ?_⟩
  constructor
  · intro hy
    let u := eqQ.symm y
    have hu : (s : ℤ) • u = 0 := by
      apply eqQ.injective
      rw [map_zsmul, LinearEquiv.apply_symm_apply, map_zero, natCast_zsmul, hy]
    have hg := (gcd_torsion_iff q s u.val).mpr
      ⟨u.prop, congrArg (fun x : ResidueTorsion q => x.val) hu⟩
    let v : ResidueTorsion (q.gcd s) := ⟨u.val, hg⟩
    refine ⟨eqG v, ?_⟩
    change eqQ (Submodule.inclusion incl (eqG.symm (eqG v))) = _
    rw [LinearEquiv.symm_apply_apply]
    exact eqQ.apply_symm_apply y
  · rintro ⟨x, rfl⟩
    let v := eqG.symm x
    have hk := ((gcd_torsion_iff q s v.val).mp v.prop).2
    rw [← natCast_zsmul]
    change (s : ℤ) • eqQ (Submodule.inclusion incl v) = 0
    rw [← map_zsmul, ← eqQ.map_zero]
    exact congrArg eqQ (Subtype.ext (by exact hk))

private theorem omissionPotential_card_of_torsion {I T : Type*} [Fintype I]
    (points : T → Fin 3 → I) (anchor : I) (q : ℕ) (hq : 0 < q) :
    Nat.card {u : I → ZMod q // IsOmissionPotential points anchor u} =
      Nat.card {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} := by
  obtain ⟨f, hf, hrange⟩ := zmod_torsion_embedding q 3 hq
  have preserves (u : I → ZMod (q.gcd 3)) :
      IsOmissionPotential points anchor (f ∘ u) ↔ IsOmissionPotential points anchor u := by
    simp only [IsOmissionPotential, Function.comp_apply, ← map_sum, ← map_nsmul, ← map_add,
      ← f.map_zero, hf.eq_iff]
  let e : {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} ≃
      {u : I → ZMod q // IsOmissionPotential points anchor u} := by
    refine Equiv.ofBijective (fun u => ⟨f ∘ u.val, (preserves _).mpr u.prop⟩) ?_
    constructor
    · intro u v h
      apply Subtype.ext
      funext i
      exact hf (congrFun (congrArg Subtype.val h) i)
    · intro u
      have h (i : I) : u.val i ∈ Set.range f := (hrange _).mp (u.prop.2.2.1 i)
      choose v hv using h
      have he : f ∘ v = u.val := funext hv
      exact ⟨⟨v, (preserves v).mp (he.symm ▸ u.prop)⟩, Subtype.ext he⟩
  exact Nat.card_congr e.symm

/-- At every divisor of the number of points, the cardinality of the reduced
kernel is determined by the corresponding ternary potential count. -/
private theorem rank_three_kernel_card_by_potential {I T : Type*}
    [Fintype I] [LinearOrder I] [Fintype T]
    (points : T → Fin 3 → I) (hinj : ∀ t, Function.Injective (points t))
    (hdis : ∀ t s i j, i ≠ j →
      (∃ a b, points t a = i ∧ points t b = j) →
      (∃ a b, points s a = i ∧ points s b = j) → t = s)
    (root anchor : I) (hne : anchor ≠ root) (q : ℕ) [NeZero q]
    (hqn : q ∣ Fintype.card I) :
    Nat.card {x : RemainingPair root anchor → ZMod q //
        (reducedMatrix points root anchor).mulVec x = 0} * q ^ Fintype.card T =
      q ^ Fintype.card (RemainingPair root anchor) *
        Nat.card {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} := by
  have annihilates (x : ZMod q) : Fintype.card I • x = 0 := by
    rw [nsmul_eq_mul, (ZMod.natCast_eq_zero_iff _ _).mpr hqn, zero_mul]
  let E : {u : I → ZMod q // IsOmissionPotential points anchor u} ≃
      {c : T → ZMod q // IsReducedRelation points root anchor c} :=
    Equiv.ofBijective _ (potential_to_relations_bijective points hinj hdis
      root anchor hne annihilates).bijective
  let F : {c : T → ZMod q // (reducedMatrix points root anchor).transpose.mulVec c = 0} ≃
      {c : T → ZMod q // IsReducedRelation points root anchor c} :=
    Equiv.subtypeEquivRight (reduced_transpose_kernel_iff points hinj root anchor)
  rw [primal_kernel_card_mul q, Nat.card_congr (F.trans E.symm),
    omissionPotential_card_of_torsion points anchor q (NeZero.pos q)]

private theorem remainingPair_card {I : Type*} [Fintype I] [LinearOrder I]
    (root anchor : I) (hne : anchor ≠ root) :
    Fintype.card (RemainingPair root anchor) = (Fintype.card I - 2).choose 2 := by
  classical
  let S := ((univ : Finset I).erase root).erase anchor
  let U := {s : Set.powersetCard I 2 // root ∉ s.val ∧ anchor ∉ s.val}
  have contained (s : Finset I) : s ⊆ S ↔ root ∉ s ∧ anchor ∉ s := by
    simp only [S, subset_erase, subset_univ, true_and]
  let e : U ≃ (S.powersetCard 2 : Finset (Finset I)) :=
    { toFun := fun s => ⟨s.val.val, mem_powersetCard.mpr
        ⟨(contained _).mpr s.prop, s.val.prop⟩⟩
      invFun := fun s =>
        let h := mem_powersetCard.mp s.prop
        ⟨⟨s.val, h.2⟩, (contained _).mp h.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr ((pairIndexEquiv root anchor).trans e), Fintype.card_coe,
    card_powersetCard, card_erase_of_mem (mem_erase.mpr ⟨hne, mem_univ _⟩),
    card_erase_of_mem (mem_univ _), card_univ, Nat.sub_sub]

private theorem reduced_kernel_torsion_card {I T : Type*} [Fintype I] [LinearOrder I]
    (points : T → Fin 3 → I) (root anchor : I) (n q : ℕ) (hn : 0 < n) (hqn : q ∣ n) :
    let K := (reducedMatrix points root anchor :
      Matrix T (RemainingPair root anchor) (ZMod n)).mulVecLin.ker.restrictScalars ℤ
    Nat.card {x : K // q • x = 0} =
      Nat.card {x : RemainingPair root anchor → ZMod q //
        (reducedMatrix points root anchor).mulVec x = 0} := by
  intro K
  have hEmbed := zmod_torsion_embedding n q hn
  rw [Nat.gcd_eq_right hqn] at hEmbed
  obtain ⟨f, hf, hrange⟩ := hEmbed
  have preserves (x : RemainingPair root anchor → ZMod q) :
      (reducedMatrix points root anchor).mulVec (f ∘ x) = 0 ↔
        (reducedMatrix points root anchor).mulVec x = 0 := by
    rw [← map_reducedMatrix_mulVec points root anchor f x]
    constructor
    · intro h
      funext t
      apply hf
      exact (congrFun h t).trans f.map_zero.symm
    · intro h
      funext t
      rw [h]
      exact f.map_zero
  let e : {x : RemainingPair root anchor → ZMod q //
      (reducedMatrix points root anchor).mulVec x = 0} ≃ {x : K // q • x = 0} := by
    let into (x : RemainingPair root anchor → ZMod q) (hx : _) : K :=
      ⟨f ∘ x, (preserves _).mpr hx⟩
    refine Equiv.ofBijective (fun x => ⟨into x.val x.prop, Subtype.ext ?_⟩) ?_
    · funext i
      exact (hrange _).mpr ⟨x.val i, rfl⟩
    constructor
    · intro x y h
      apply Subtype.ext
      funext i
      exact hf (congrArg (fun u : {x : K // q • x = 0} => u.val.val i) h)
    · intro y
      have hy (i : RemainingPair root anchor) : q • y.val.val i = 0 :=
        congrArg (fun x : K => x.val i) y.prop
      choose x hx using fun i => (hrange _).mp (hy i)
      have he : f ∘ x = y.val.val := funext hx
      have mem := (preserves x).mp (he.symm ▸ y.val.prop)
      exact ⟨⟨x, mem⟩, Subtype.ext (Subtype.ext he)⟩
  exact Nat.card_congr e.symm

private theorem sparse_triangle_unique_pair {I T : Type*} [LinearOrder I]
    (triangles : T → Fin 3 ↪o I) (ht : Injective triangles)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (t s : T) (i j : I) (hij : i ≠ j)
    (hi : covers (triangles t) i j) (hj : covers (triangles s) i j) : t = s := by
  let H := (ofFinEmbEquiv (triangles t)).val
  let J := (ofFinEmbEquiv (triangles s)).val
  have HJ : H = J := by
    by_contra hne
    have hs := hsparse (show H ∈ Set.range _ from ⟨t, rfl⟩)
      (show J ∈ Set.range _ from ⟨s, rfl⟩) hne
    have covered (b : T) (h : covers (triangles b) i j) :
        i ∈ (ofFinEmbEquiv (triangles b)).val ∧ j ∈ (ofFinEmbEquiv (triangles b)).val := by
      obtain ⟨x, y, hx, hy⟩ := h
      exact ⟨(mem_ofFinEmbEquiv_iff_mem_range _ _).mpr ⟨x, hx⟩,
        (mem_ofFinEmbEquiv_iff_mem_range _ _).mpr ⟨y, hy⟩⟩
    have hc := Finset.one_lt_card_iff.mpr
      ⟨i, j, mem_inter.mpr ⟨(covered t hi).1, (covered s hj).1⟩,
        mem_inter.mpr ⟨(covered t hi).2, (covered s hj).2⟩, hij⟩
    change 1 < (H ∩ J).card at hc
    omega
  exact ht (ofFinEmbEquiv.injective (Subtype.ext HJ))

/-- The point potentials count the elements of the integral obstruction
killed by any divisor of the ground-set size. -/
theorem rank_three_lifting_obstruction_torsion_card {I T : Type*}
    [Fintype I] [LinearOrder I] [Fintype T]
    (M : Matroid I) (triangles : T → Fin 3 ↪o I) (ht : Injective triangles)
    (root anchor : I) (hne : anchor ≠ root) (hn : 3 < Fintype.card I)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (hground : M.E = Set.univ)
    (hbase : ∀ B : Finset I, M.IsBase (B : Set I) ↔
      B.card = 3 ∧ B ∉ Set.range fun t => (ofFinEmbEquiv (triangles t)).val)
    (q : ℕ) [NeZero q] (hqn : q ∣ Fintype.card I) :
    let G := JointSaturatedImage (M.comap (id : I → I)) ⧸
      JointImageInSaturation (M.comap (id : I → I))
    Nat.card {x : G // q • x = 0} * q ^ Fintype.card T =
      q ^ ((Fintype.card I - 2).choose 2) *
        Nat.card {u : I → ZMod (q.gcd 3) //
          IsOmissionPotential (fun t => triangles t) anchor u} := by
  intro G
  let points (t : T) : Fin 3 → I := triangles t
  obtain ⟨equiv⟩ := rank_three_lifting_obstruction_equiv_kernel M triangles root anchor
    hne hn hsparse hground hbase
  have transform := equiv.toEquiv.subtypeEquiv
    (p := fun x : G => q • x = 0) (q := fun y => q • y = 0) (fun x => by
      change q • x = 0 ↔ q • equiv x = 0
      have hmap : equiv (q • x) = q • equiv x := by
        simpa only [natCast_zsmul] using equiv.map_smul (q : ℤ) x
      rw [← hmap, ← equiv.map_zero, equiv.injective.eq_iff])
  rw [Nat.card_congr transform, reduced_kernel_torsion_card points root anchor
    (Fintype.card I) q (by omega) hqn, ← remainingPair_card root anchor hne]
  exact rank_three_kernel_card_by_potential points (fun t => (triangles t).injective)
    (sparse_triangle_unique_pair triangles ht hsparse) root anchor hne q hqn

private theorem int_cast_matrix_rigidity {m n : Type*} [Fintype m]
    (A : Matrix n m ℤ) (q : ℕ) (hq : 3 < q)
    (hkill : ∀ x : m → ZMod q, (A.map (Int.castRingHom (ZMod q))).mulVec x = 0 →
      ∀ i, 3 • x i = 0) :
    ∀ x : m → ℤ, A.mulVec x = 0 → x = 0 := by
  classical
  let qZ : ℤ := q
  let g := Int.gcd qZ 3
  have gpos : 0 < g := Int.gcd_pos_of_ne_zero_right _ (by decide)
  obtain ⟨d, e, hde, hqde, h3de⟩ := Int.exists_gcd_one gpos
  have gnz : (g : ℤ) ≠ 0 := by exact_mod_cast gpos.ne'
  have gbound : (g : ℤ) ≤ 3 := Int.le_of_dvd (by decide) (Int.gcd_dvd_right qZ 3)
  have dpos : 1 < d := by
    have hq' : 3 < qZ := by
      change 3 < (q : ℤ)
      exact_mod_cast hq
    nlinarith
  have divisibility (x : m → ℤ) (hx : A.mulVec x = 0) (i : m) : d ∣ x i := by
    let cast := Int.castRingHom (ZMod q)
    have hm : (A.map cast).mulVec (cast ∘ x) = 0 := by
      funext j
      rw [← RingHom.map_mulVec, hx]
      exact cast.map_zero
    have h := hkill (cast ∘ x) hm i
    rw [nsmul_eq_mul] at h
    have h' : ((3 * x i : ℤ) : ZMod q) = 0 := by
      simpa [cast, Int.cast_mul, Function.comp_def] using h
    have hdiv : qZ ∣ 3 * x i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
    have hdiv' : d * (g : ℤ) ∣ e * x i * (g : ℤ) := by
      convert hdiv using 1
      · exact hqde.symm
      · rw [mul_right_comm, ← h3de]
    exact Int.dvd_of_dvd_mul_right_of_gcd_one (Int.dvd_of_mul_dvd_mul_right gnz hdiv') hde
  intro x hx
  funext i
  by_contra hi
  have existsPositive : ∃ a : ℕ, ∃ v : m → ℤ, A.mulVec v = 0 ∧
      v i ≠ 0 ∧ (v i).natAbs = a := ⟨_, x, hx, hi, rfl⟩
  obtain ⟨v, hv, hvi, hmin⟩ := Nat.find_spec existsPositive
  choose w hw using divisibility v hv
  have veq : v = d • w := funext hw
  have hscaled : d • A.mulVec w = 0 := by rwa [veq, Matrix.mulVec_smul] at hv
  have wker : A.mulVec w = 0 := by
    funext j
    have h := congrFun hscaled j
    change d * A.mulVec w j = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (by omega)
  have wi : w i ≠ 0 := by
    intro zero
    exact hvi (by rw [hw, zero, mul_zero])
  have less : (w i).natAbs < Nat.find existsPositive := by
    rw [← hmin, hw, Int.natAbs_mul]
    have habs : 1 < d.natAbs := by omega
    have hwpos : 0 < (w i).natAbs := Int.natAbs_pos.mpr wi
    nlinarith
  exact (Nat.find_min existsPositive less) ⟨w, wker, wi, rfl⟩

private theorem smith_kernel_split {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) (hA : Injective A.transpose.mulVecLin) (q : ℕ) :
    Fintype.card m ≤ Fintype.card n ∧ ∃ d : Fin (Fintype.card m) → ℤ,
      Nonempty (↥((A.map (Int.castRingHom (ZMod q))).mulVecLin.ker.restrictScalars ℤ) ≃ₗ[ℤ]
        (Fin (Fintype.card n - Fintype.card m) → ZMod q) ×
          ((i : Fin (Fintype.card m)) → Submodule.torsionBy ℤ (ZMod q) (d i))) := by
  classical
  let f := A.transpose.mulVecLin
  let b := Pi.basisFun ℤ n
  let c := Pi.basisFun ℤ m
  obtain ⟨r, S⟩ := (LinearMap.range f).smithNormalForm b
  have rcard : r = Fintype.card m := by
    let br := c.map (LinearEquiv.ofInjective f hA)
    simpa only [Fintype.card_fin] using Fintype.card_congr (S.bN.indexEquiv br)
  subst r
  let d := S.a
  let D (i : Fin (Fintype.card m)) := Submodule.torsionBy ℤ (ZMod q) (d i)
  refine ⟨by simpa using Fintype.card_le_of_injective S.f S.f.injective, d, ?_⟩
  let cast := Int.castRingHom (ZMod q)
  let K := (A.map cast).mulVecLin.ker.restrictScalars ℤ
  let P : Submodule ℤ (n → ZMod q) :=
    ⨅ i, (D i).comap (LinearMap.proj (R := ℤ) (φ := fun _ : n => ZMod q) (S.f i))
  let coord : (n → ZMod q) ≃ₗ[ℤ] (n → ZMod q) :=
    (b.constr ℤ).trans (S.bM.constr ℤ).symm
  have read (x : n → ZMod q) (i : m) :
      (A.map cast).mulVec x i = (b.constr ℤ x) (f (c i)) := by
    have col : f (c i) = fun j => A i j := by
      simp [f, c, Pi.basisFun_apply, Matrix.mulVec_single_one]
      rfl
    have expand : (fun j => A i j) = ∑ j, A i j • b j := by
      funext k
      simp [b, Pi.basisFun_apply, Finset.sum_apply, Pi.smul_apply,
        Pi.single_apply, mul_ite]
    rw [col]
    conv => rhs; arg 2; rw [expand]
    rw [map_sum]
    change (∑ j, cast (A i j) * x j) = _
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, Module.Basis.constr_basis]
    rw [zsmul_eq_mul]
    rfl
  have ann (x : n → ZMod q) : x ∈ K ↔ ∀ y : f.range, (b.constr ℤ x) y.val = 0 := by
    change (A.map cast).mulVec x = 0 ↔ _
    constructor
    · intro h y
      obtain ⟨z, hz⟩ := y.prop
      have hz' : (b.constr ℤ x).comp f = 0 := c.ext fun i => by
        exact (read x i).symm.trans (congrFun h i)
      rw [← hz]
      exact congrFun (congrArg DFunLike.coe hz') z
    · intro h
      funext i
      rw [read]
      exact h ⟨f (c i), ⟨c i, rfl⟩⟩
  have diag (x : n → ZMod q) : x ∈ K ↔ coord x ∈ P := by
    rw [ann]
    have eqn (i : Fin (Fintype.card m)) :
        (b.constr ℤ x) (S.bN i : f.range).val = d i • coord x (S.f i) := by
      rw [S.snf, map_zsmul]
      rfl
    have constraints : coord x ∈ P ↔ ∀ i, d i • coord x (S.f i) = 0 := by
      simp only [P, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply,
        Submodule.mem_torsionBy_iff, D]
    rw [constraints]
    constructor
    · intro h i
      rw [← eqn]
      exact h (S.bN i)
    · intro h y
      have hzero : (b.constr ℤ x).comp f.range.subtype = 0 := S.bN.ext fun i => by
        exact (eqn i).trans (h i)
      exact congrFun (congrArg DFunLike.coe hzero) y
  let e := coord.ofSubmodules K P (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    change coord.symm x ∈ K ↔ x ∈ P
    rw [diag, LinearEquiv.apply_symm_apply])
  let U := {j : n // j ∉ Set.range S.f}
  have accepts (x : n → ZMod q) : x ∈ P ↔ ∀ i, x (S.f i) ∈ D i := by
    simp only [P, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.proj_apply]
  let separate : P →ₗ[ℤ] (U → ZMod q) × ((i : Fin (Fintype.card m)) → D i) :=
    { toFun := fun x => (fun j => x.val j, fun i => ⟨x.val (S.f i), (accepts _).mp x.prop i⟩)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have bijective : Bijective separate := by
    constructor
    · intro x y h
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ Set.range S.f
      · obtain ⟨i, rfl⟩ := hj
        exact congrArg (fun v => (v.2 i).val) h
      · exact congrArg (fun v => v.1 ⟨j, hj⟩) h
    · intro y
      let x (j : n) : ZMod q :=
        if hj : j ∈ Set.range S.f then (y.2 hj.choose).val else y.1 ⟨j, hj⟩
      have some (i : Fin (Fintype.card m)) : x (S.f i) = (y.2 i).val := by
        have h : S.f i ∈ Set.range S.f := ⟨i, rfl⟩
        dsimp only [x]
        rw [dif_pos h, S.f.injective h.choose_spec]
      refine ⟨⟨x, (accepts _).mpr (fun i => (some i).symm ▸ (y.2 i).prop)⟩, Prod.ext ?_ ?_⟩
      · funext j
        exact dif_neg j.prop
      · funext i
        exact Subtype.ext (some i)
  have ucard : Fintype.card U = Fintype.card n - Fintype.card m := by
    rw [Fintype.card_subtype_compl, ← Fintype.card_congr (Equiv.ofInjective S.f S.f.injective),
      Fintype.card_fin]
  let free := LinearEquiv.piCongrLeft' ℤ (fun _ : U => ZMod q) (Fintype.equivFinOfCardEq ucard)
  exact ⟨e.trans ((LinearEquiv.ofBijective separate bijective).trans
    (free.prodCongr (LinearEquiv.refl ℤ _)))⟩

private theorem zmod_torsion_card (n q : ℕ) (hn : 0 < n) (hq : q ∣ n) :
    Nat.card {x : ZMod n // q • x = 0} = q := by
  have h := zmod_torsion_embedding n q hn
  rw [Nat.gcd_eq_right hq] at h
  obtain ⟨f, hf, hrange⟩ := h
  let e : ZMod q ≃ {x : ZMod n // q • x = 0} :=
    Equiv.ofBijective (fun x => ⟨f x, (hrange _).mpr ⟨x, rfl⟩⟩)
      ⟨fun _ _ hx => hf (congrArg Subtype.val hx), fun y => by
        obtain ⟨x, hx⟩ := (hrange _).mp y.prop
        exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e, Nat.card_zmod]

private theorem free_prod_torsion_card {G D : Type*} [AddCommGroup G] [AddCommGroup D]
    (n r q : ℕ) (hn : 0 < n) (hq : q ∣ n)
    (e : G ≃+ (Fin r → ZMod n) × D) :
    Nat.card {x : G // q • x = 0} = q ^ r * Nat.card {y : D // q • y = 0} := by
  let transfer : {x : G // q • x = 0} ≃ {x : (Fin r → ZMod n) × D // q • x = 0} :=
    e.toEquiv.subtypeEquiv (fun x => by
      change q • x = 0 ↔ q • e x = 0
      rw [← map_nsmul, ← e.map_zero, e.injective.eq_iff])
  let split : {x : (Fin r → ZMod n) × D // q • x = 0} ≃
      {f : Fin r → ZMod n // ∀ i, q • f i = 0} × {y : D // q • y = 0} :=
    (Equiv.subtypeEquivRight (fun x => by
      rcases x with ⟨f, y⟩
      change ((q • f, q • y) : (Fin r → ZMod n) × D) = (0, 0) ↔ _
      simp only [Prod.mk.injEq, funext_iff, Pi.smul_apply, Pi.zero_apply])).trans
      (@Equiv.subtypeProdEquivProd _ _ (fun f : Fin r → ZMod n => ∀ i, q • f i = 0)
        (fun y : D => q • y = 0))
  let pointwise : {f : Fin r → ZMod n // ∀ i, q • f i = 0} ≃
      (Fin r → {x : ZMod n // q • x = 0}) :=
    @Equiv.subtypePiEquivPi (Fin r) (fun _ => ZMod n) (fun _ x => q • x = 0)
  rw [Nat.card_congr (transfer.trans split), Nat.card_prod,
    Nat.card_congr pointwise, Nat.card_fun,
    zmod_torsion_card n q hn hq, Nat.card_fin]

/-- The integral lifting obstruction is the sum of the free residue coordinates
and a ternary vector space of the same size as the normalized point potentials. -/
theorem rank_three_lifting_obstruction_cyclic_factors {I T : Type*}
    [Fintype I] [LinearOrder I] [Fintype T]
    (M : Matroid I) (triangles : T → Fin 3 ↪o I) (ht : Injective triangles)
    (root anchor : I) (hne : anchor ≠ root) (hn : 3 < Fintype.card I)
    (hsparse : (Set.range fun t => (ofFinEmbEquiv (triangles t)).val).Pairwise
      (fun H J => (H ∩ J).card + 2 ≤ 3))
    (hground : M.E = Set.univ)
    (hbase : ∀ B : Finset I, M.IsBase (B : Set I) ↔
      B.card = 3 ∧ B ∉ Set.range fun t => (ofFinEmbEquiv (triangles t)).val) :
    let n := Fintype.card I
    let r := (n - 2).choose 2 - Fintype.card T
    let G := JointSaturatedImage (M.comap (id : I → I)) ⧸
      JointImageInSaturation (M.comap (id : I → I))
    ∃ d, Nat.card {u : I → ZMod (n.gcd 3) //
        IsOmissionPotential (fun t => triangles t) anchor u} = 3 ^ d ∧
      Nonempty (G ≃ₗ[ℤ] (Fin r → ZMod n) × (Fin d → ZMod 3)) := by
  classical
  intro n r G
  let b := (n - 2).choose 2
  let m := Fintype.card T
  let g := n.gcd 3
  have hnpos : 0 < n := by omega
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left 3 hnpos
  let _ : NeZero n := ⟨hnpos.ne'⟩
  let _ : NeZero g := ⟨hgpos.ne'⟩
  let points (t : T) : Fin 3 → I := triangles t
  let A : Matrix T (RemainingPair root anchor) ℤ := reducedMatrix points root anchor
  have castA : A.map (Int.castRingHom (ZMod n)) =
      (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) (ZMod n)) := by
    ext i j
    exact reducedMatrix_intCast points root anchor i j
  have castT : A.transpose.map (Int.castRingHom (ZMod n)) =
      (reducedMatrix points root anchor : Matrix T (RemainingPair root anchor) (ZMod n)).transpose := by
    ext j i
    exact reducedMatrix_intCast points root anchor i j
  have nKills (x : ZMod n) : n • x = 0 := by
    rw [nsmul_eq_mul, (ZMod.natCast_eq_zero_iff n n).mpr (dvd_refl _), zero_mul]
  have hA : Injective A.transpose.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply int_cast_matrix_rigidity A.transpose n hn _ x hx
    intro c hc
    rw [castT] at hc
    have rel := (reduced_transpose_kernel_iff points (fun t => (triangles t).injective)
      root anchor c).mp hc
    exact (triangle_relation_potential points (fun t => (triangles t).injective)
      (sparse_triangle_unique_pair triangles ht hsparse) root anchor hne nKills c rel).1
  obtain ⟨mb, coeff, ⟨split⟩⟩ := smith_kernel_split A hA n
  rw [remainingPair_card root anchor hne] at mb
  change m ≤ b at mb
  rw [castA, remainingPair_card root anchor hne] at split
  let D := (i : Fin m) → Submodule.torsionBy ℤ (ZMod n) (coeff i)
  obtain ⟨kernel⟩ := rank_three_lifting_obstruction_equiv_kernel M triangles root anchor
    hne hn hsparse hground hbase
  let e : G ≃ₗ[ℤ] (Fin r → ZMod n) × D := kernel.trans split
  let N := Nat.card {u : I → ZMod g // IsOmissionPotential points anchor u}
  have residual (q : ℕ) [NeZero q] (hq : q ∣ n) (hg : q.gcd 3 = g) :
      Nat.card {y : D // q • y = 0} = N := by
    have h := rank_three_lifting_obstruction_torsion_card M triangles ht root anchor hne hn
      hsparse hground hbase q hq
    change Nat.card {x : G // q • x = 0} * q ^ m =
      q ^ b * Nat.card {u : I → ZMod (q.gcd 3) // IsOmissionPotential points anchor u} at h
    rw [hg, free_prod_torsion_card n r q hnpos hq e.toAddEquiv, mul_right_comm] at h
    change q ^ r * q ^ m * _ = q ^ b * N at h
    have hr : r + m = b := Nat.sub_add_cancel mb
    rw [← pow_add, hr] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (NeZero.pos q)) h
  have nKillsD (x : D) : n • x = 0 := by
    funext i
    exact Subtype.ext (nKills (x i).val)
  have total : Nat.card D = N := by
    rw [← Nat.card_congr (Equiv.subtypeUnivEquiv nKillsD)]
    exact residual n (dvd_refl _) rfl
  have gSus : Nat.card {x : D // g • x = 0} = N :=
    residual g (Nat.gcd_dvd_left n 3) (Nat.gcd_eq_left (Nat.gcd_dvd_right n 3))
  have covers : Surjective (Subtype.val : {x : D // g • x = 0} → D) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨Subtype.val_injective, gSus.trans total.symm⟩).2
  have threeKills (x : D) : 3 • x = 0 := by
    obtain ⟨y, rfl⟩ := covers x
    obtain ⟨a, ha⟩ := Nat.gcd_dvd_right n 3
    change 3 = g * a at ha
    rw [ha, mul_nsmul, y.prop, nsmul_zero]
  let _ : Module (ZMod 3) D := AddCommGroup.zmodModule threeKills
  let s := Module.finrank (ZMod 3) D
  let ternary : D ≃ₗ[ℤ] (Fin s → ZMod 3) :=
    (Module.finBasis (ZMod 3) D).equivFun.toAddEquiv.toIntLinearEquiv
  refine ⟨s, ?_, ⟨e.trans ((LinearEquiv.refl ℤ _).prodCongr ternary)⟩⟩
  change N = 3 ^ s
  rw [← total, Nat.card_congr ternary.toEquiv, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

/-- The actual integral lifting obstruction on the affine plane has nine
cyclic factors of order nine and two of order three. -/
theorem affine_plane_lifting_obstruction_cyclic_factors (M : Matroid (Fin 9))
    (hground : M.E = Set.univ)
    (hbase : ∀ B : Finset (Fin 9), M.IsBase (B : Set (Fin 9)) ↔
      B.card = 3 ∧ B ∉ affineOmissions) :
    Nonempty ((JointSaturatedImage (M.comap (id : Fin 9 → Fin 9)) ⧸
      JointImageInSaturation (M.comap (id : Fin 9 → Fin 9))) ≃ₗ[ℤ]
        (Fin 9 → ZMod 9) × (Fin 2 → ZMod 3)) := by
  have sparse : affineOmissions.Pairwise (fun H J => (H ∩ J).card + 2 ≤ 3) := by
    rintro _ ⟨t, rfl⟩ _ ⟨s, rfl⟩ hne
    by_contra! bad
    have hcard : 1 < ((ofFinEmbEquiv (affineTriangle t)).val ∩
      (ofFinEmbEquiv (affineTriangle s)).val).card := by omega
    obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp hcard
    have cover (r : Fin 12) (hi : i ∈ (ofFinEmbEquiv (affineTriangle r)).val)
        (hj : j ∈ (ofFinEmbEquiv (affineTriangle r)).val) :
        covers (affineLines r) i j := by
      obtain ⟨a, ha⟩ := (mem_ofFinEmbEquiv_iff_mem_range (affineTriangle r) i).mp hi
      obtain ⟨b, hb⟩ := (mem_ofFinEmbEquiv_iff_mem_range (affineTriangle r) j).mp hj
      exact ⟨a, b, ha, hb⟩
    have h := affine_pair_unique t s i j hij
      (cover t (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hj).1)
      (cover s (Finset.mem_inter.mp hi).2 (Finset.mem_inter.mp hj).2)
    exact hne (congrArg (fun r => (ofFinEmbEquiv (affineTriangle r)).val) h)
  have ht : Injective affineTriangle := by
    intro t s h
    have h₀ := congrArg (fun e : Fin 3 ↪o Fin 9 => e 0) h
    have h₁ := congrArg (fun e : Fin 3 ↪o Fin 9 => e 1) h
    exact affine_pair_unique t s (affineLines t 0) (affineLines t 1)
      ((affine_triangle_injective t).ne (by decide)) ⟨0, 1, rfl, rfl⟩
      ⟨0, 1, h₀.symm, h₁.symm⟩
  obtain ⟨d, hd, E⟩ := rank_three_lifting_obstruction_cyclic_factors M affineTriangle ht
    8 0 (by decide) (by decide) sparse hground hbase
  change Nat.card {u : Fin 9 → ZMod 3 // IsOmissionPotential affineLines 0 u} = 3 ^ d at hd
  rw [Nat.card_congr (Equiv.subtypeEquivRight affine_compatible_iff),
    affine_plane_potential_card] at hd
  have htwo : d = 2 := Nat.pow_right_injective (by decide : 2 ≤ 3) hd.symm
  subst d
  exact E

end D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials
