/- GID: D5/S3/Quantum/Measurement/Auric/UnequalBlockBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalBlockBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Projection rigidity and common attained entropy maxima on zero and saturated trace faces. -/

import D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # Closed faces of the unequal rank-cap entropy problem

A zero or saturated trace forces a projection row. The remaining effects reduce to
a binary allocation on its orthogonal complement. The exact bounds use the original
row labels and four column types, with the same diagonal tuple attaining both scores.
-/

namespace D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder
open EqualBlockEffects (diagonal_entropy effect_le_one eigenvalues_mem_unit)

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The effective rank cap in dimension `d`. -/
def cap (d m : ℕ) : ℕ := min d m

/-- The number of coordinates reserved for the kernel of this row. -/
def missing (d m : ℕ) : ℕ := d - m

private theorem cap_add_missing (d m : ℕ) : cap d m + missing d m = d := by
  unfold cap missing
  omega

private theorem sum_three_labels {G : Type*} [AddCommMonoid G] (f : Fin 3 → G)
    {j i k : Fin 3} (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) :
    ∑ r, f r = f j + f i + f k := by
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    simp_all [Fin.sum_univ_three] <;> abel

private theorem eq_last_label {j i k r : Fin 3} (hji : j ≠ i) (hjk : j ≠ k)
    (hik : i ≠ k) (hrj : r ≠ j) (hri : r ≠ i) : r = k := by
  have h : (j : ℕ) ≠ i := fun e => hji (Fin.ext e)
  have h' : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
  have h'' : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
  have h₁ : (r : ℕ) ≠ j := fun e => hrj (Fin.ext e)
  have h₂ : (r : ℕ) ≠ i := fun e => hri (Fin.ext e)
  apply Fin.ext
  omega

/-- A zero row trace forces the effect itself to vanish. -/
theorem effect_eq_zero_of_trace_zero {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htrace : A.trace.re = 0) : A = 0 := by
  apply hA.trace_eq_zero_iff.mp
  exact Complex.ext htrace (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm

/-- A trace at the effective cap uses all of its rank in unit eigenvalues. -/
theorem effect_sq_eq_self_of_trace_cap {A : Matrix n n ℂ} {m : ℕ}
    (hA : A.PosSemidef) (hA1 : A ≤ 1) (hr : A.rank ≤ m)
    (htrace : A.trace.re = (cap (Fintype.card n) m : ℝ)) : A * A = A := by
  classical
  let e := hA.isHermitian.eigenvalues
  let S := univ.filter (fun a => e a ≠ 0)
  have hrS : S.card = A.rank := by
    rw [hA.isHermitian.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hrCap : S.card ≤ cap (Fintype.card n) m := by
    exact le_min (card_le_univ S) (hrS.trans_le hr)
  have hsumTrace : ∑ a, hA.isHermitian.eigenvalues a = A.trace.re := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    rfl
  have hsum : (∑ a ∈ S, e a) = (cap (Fintype.card n) m : ℝ) := by
    rw [← htrace, ← hsumTrace]
    apply sum_subset (filter_subset _ _)
    intro a ha hnot
    by_contra hne
    exact hnot (mem_filter.mpr ⟨ha, hne⟩)
  have hdeficit (a : n) (_ : a ∈ S) : 0 ≤ 1 - e a :=
    sub_nonneg.mpr (eigenvalues_mem_unit hA hA1 a).2
  have htotal : (∑ a ∈ S, (1 - e a)) = 0 := by
    have hnonneg := sum_nonneg hdeficit
    have hcast : (S.card : ℝ) ≤ (cap (Fintype.card n) m : ℝ) := by exact_mod_cast hrCap
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hsum] at hnonneg ⊢
    linarith
  have he (a : n) : e a = 0 ∨ e a = 1 := by
    by_cases ha : e a = 0
    · exact Or.inl ha
    · have hh := (sum_eq_zero_iff_of_nonneg hdeficit).mp htotal a
          (mem_filter.mpr ⟨mem_univ _, ha⟩)
      exact Or.inr (by linarith)
  let g := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.isHermitian.eigenvectorUnitary
  let D := diagonal (fun a => (e a : ℂ))
  have hAD : A = g D := hA.isHermitian.spectral_theorem
  have hDD : D * D = D := by
    change diagonal (fun a => (e a : ℂ)) * diagonal (fun a => (e a : ℂ)) =
      diagonal (fun a => (e a : ℂ))
    rw [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext a
    rcases he a with h | h <;> simp [h]
  rw [hAD, ← map_mul, hDD]

/-- Positivity forces each summand of `I - P` to annihilate the range of `P`. -/
theorem projection_mul_effect_eq_zero {P B C : Matrix n n ℂ}
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hB : B.PosSemidef) (hC : C.PosSemidef) (hs : B + C = 1 - P) :
    P * B = 0 ∧ B * P = 0 := by
  have hright : B * P = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    let x := P *ᵥ v
    have hPx : P *ᵥ x = x := by
      change P *ᵥ (P *ᵥ v) = P *ᵥ v
      rw [Matrix.mulVec_mulVec, hPP]
    have hsum : star x ⬝ᵥ (B *ᵥ x) + star x ⬝ᵥ (C *ᵥ x) = 0 := by
      rw [← dotProduct_add, ← add_mulVec, hs, sub_mulVec, one_mulVec, hPx, sub_self,
        dotProduct_zero]
    have hBx := hB.dotProduct_mulVec_zero_iff.mp
      ((add_eq_zero_iff_of_nonneg (hB.dotProduct_mulVec_nonneg x)
        (hC.dotProduct_mulVec_nonneg x)).mp hsum).1
    simpa only [x, Matrix.mulVec_mulVec, zero_mulVec] using hBx
  have hleft := congrArg Matrix.conjTranspose hright
  rw [Matrix.conjTranspose_mul, hP.eq, hB.isHermitian.eq, Matrix.conjTranspose_zero] at hleft
  exact ⟨hleft, hright⟩

/-- A projection row gives one projection summand and a binary effect on its complement. -/
theorem projection_row_reduces {A : Fin 3 → Matrix n n ℂ}
    (hp : ∀ r, (A r).PosSemidef) (hs : ∑ r, A r = 1)
    {j i k : Fin 3} (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hP : A j * A j = A j) :
    A i + A k = 1 - A j ∧ A j * A i = 0 ∧ A i * A j = 0 ∧
      A j * A k = 0 ∧ A k * A j = 0 ∧ Commute (A i) (A k) := by
  rw [sum_three_labels A hji hjk hik] at hs
  have hsplit : A i + A k = 1 - A j := by
    apply eq_sub_iff_add_eq.mpr
    calc
      A i + A k + A j = A j + A i + A k := by abel
      _ = 1 := hs
  obtain ⟨hPi, hiP⟩ :=
    projection_mul_effect_eq_zero (hp j).isHermitian hP (hp i) (hp k) hsplit
  obtain ⟨hPk, hkP⟩ :=
    projection_mul_effect_eq_zero (hp j).isHermitian hP (hp k) (hp i)
      (by simpa only [add_comm (A k) (A i)] using hsplit)
  have hk : A k = 1 - A j - A i := by
    rw [eq_sub_iff_add_eq, add_comm (A k) (A i)]
    exact hsplit
  refine ⟨hsplit, hPi, hiP, hPk, hkP, ?_⟩
  change A i * A k = A k * A i
  rw [hk, mul_sub, mul_sub, sub_mul, sub_mul, mul_one, one_mul, hiP, hPi]

private theorem commute_of_projection_row {A : Fin 3 → Matrix n n ℂ}
    (hp : ∀ r, (A r).PosSemidef) (hs : ∑ r, A r = 1)
    {j i k : Fin 3} (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hP : A j * A j = A j) : ∀ r s, Commute (A r) (A s) := by
  obtain ⟨_, hPi, hiP, hPk, hkP, hikComm⟩ := projection_row_reduces hp hs hji hjk hik hP
  have hjI : Commute (A j) (A i) := hPi.trans hiP.symm
  have hjK : Commute (A j) (A k) := hPk.trans hkP.symm
  intro r s
  have hr : r = j ∨ r = i ∨ r = k := by
    by_cases hrj : r = j
    · exact Or.inl hrj
    by_cases hri : r = i
    · exact Or.inr (Or.inl hri)
    exact Or.inr (Or.inr (eq_last_label hji hjk hik hrj hri))
  have hs' : s = j ∨ s = i ∨ s = k := by
    by_cases hsj : s = j
    · exact Or.inl hsj
    by_cases hsi : s = i
    · exact Or.inr (Or.inl hsi)
    exact Or.inr (Or.inr (eq_last_label hji hjk hik hsj hsi))
  rcases hr with rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl
  all_goals
    first
    | exact Commute.refl _
    | exact hjI
    | exact hjI.symm
    | exact hjK
    | exact hjK.symm
    | exact hikComm
    | exact hikComm.symm

private theorem projection_of_boundary {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} (hA : Feasible m τ A) {j : Fin 3}
    (hj : τ j = 0 ∨ τ j = (cap (Fintype.card n) (m j) : ℝ)) :
    A j * A j = A j := by
  rcases hj with hz | ht
  · rw [effect_eq_zero_of_trace_zero (hA.1 j) ((hA.2.2.1 j).trans hz), zero_mul]
  · exact effect_sq_eq_self_of_trace_cap (hA.1 j) (effect_le_one A hA.1 hA.2.1 j)
      (hA.2.2.2 j) ((hA.2.2.1 j).trans ht)

/-- Every feasible tuple on either kind of boundary face commutes, irrespective of optimality. -/
theorem commute_on_boundary {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} (hA : Feasible m τ A) {j : Fin 3}
    (hj : τ j = 0 ∨ τ j = (cap (Fintype.card n) (m j) : ℝ)) :
    ∀ r s, Commute (A r) (A s) := by
  have hP := projection_of_boundary hA hj
  fin_cases j
  · exact commute_of_projection_row hA.1 hA.2.1
      (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
      (by decide : (1 : Fin 3) ≠ 2) hP
  · exact commute_of_projection_row hA.1 hA.2.1
      (by decide : (1 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 0) hP
  · exact commute_of_projection_row hA.1 hA.2.1
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 1) hP

private theorem rank_diagonal_real (v : n → ℝ) :
    (diagonal fun a => (v a : ℂ)).rank = (univ.filter fun a => v a ≠ 0).card := by
  classical
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  simp

private theorem spectral_of_diagonal (f : ℝ → ℝ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (v : n → ℝ) (hv : A = diagonal (fun a => (v a : ℂ))) :
    (∑ a, f (hA.eigenvalues a)) = ∑ a, f (v a) := by
  subst A
  exact diagonal_entropy f v hA

private structure BoundaryCoordinates
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) (A : Fin 3 → Matrix n n ℂ)
    (hp : ∀ r, (A r).PosSemidef) (j i k : Fin 3) where
  v : Fin 3 → n → ℝ
  nonneg : ∀ r a, 0 ≤ v r a
  column : ∀ a, v j a + v i a + v k a = 1
  projection : ∀ a, v j a = 0 ∨ v j a = 1
  mass : ∀ r, ∑ a, v r a = τ r
  support : ∀ r, (univ.filter fun a => v r a ≠ 0).card ≤ m r
  spectral : ∀ f : ℝ → ℝ, spectralSum f A hp = ∑ a, (f (v j a) + f (v i a) + f (v k a))

private theorem boundary_coordinates {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} (hA : Feasible m τ A)
    {j i k : Fin 3} (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hP : A j * A j = A j) : Nonempty (BoundaryCoordinates m τ A hA.1 j i k) := by
  classical
  have hComm := commute_of_projection_row hA.1 hA.2.1 hji hjk hik hP
  obtain ⟨U, hUj, hUi⟩ := Commute.exists_unitary
    (hA.1 j).isHermitian (hA.1 i).isHermitian (hComm j i)
  let g := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
  let D (r : Fin 3) := g (A r)
  have hsum : D j + D i + D k = 1 := by
    have hs := hA.2.1
    rw [sum_three_labels A hji hjk hik] at hs
    have h := congrArg g hs
    simpa only [map_add, map_one, D] using h
  have hDj : (D j).IsDiag := by
    simpa only [D, g, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hUj
  have hDi : (D i).IsDiag := by
    simpa only [D, g, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hUi
  have hDk : (D k).IsDiag := by
    intro a b hab
    have h := congrArg (fun M : Matrix n n ℂ => M a b) hsum
    simpa only [Matrix.add_apply, hDj hab, hDi hab, zero_add, Matrix.one_apply_ne hab] using h
  have hDiag (r : Fin 3) : (D r).IsDiag := by
    by_cases hrj : r = j
    · simpa only [hrj] using hDj
    by_cases hri : r = i
    · simpa only [hri] using hDi
    simpa only [eq_last_label hji hjk hik hrj hri] using hDk
  have hps (r : Fin 3) : (D r).PosSemidef := by
    change (g (A r)).PosSemidef
    rw [Unitary.conjStarAlgAut_apply]
    exact (Unitary.isUnit_coe (U := U)).posSemidef_star_right_conjugate_iff.mpr (hA.1 r)
  let v (r : Fin 3) (a : n) := (D r a a).re
  have hD (r : Fin 3) : D r = diagonal (fun a => (v r a : ℂ)) := by
    calc
      D r = diagonal (diag (D r)) := (hDiag r).diagonal_diag.symm
      _ = diagonal (fun a => (v r a : ℂ)) :=
        congrArg diagonal (funext fun a => ((hps r).isHermitian.coe_re_apply_self a).symm)
  have hchar (r : Fin 3) : (A r).charpoly = (D r).charpoly := by
    symm
    change (g (A r)).charpoly = _
    rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc,
      Unitary.coe_star_mul_self, one_mul]
  have heigs (r : Fin 3) :
      (hA.1 r).isHermitian.eigenvalues = (hps r).isHermitian.eigenvalues :=
    ((hA.1 r).isHermitian.eigenvalues_eq_eigenvalues_iff (hps r).isHermitian).mpr (hchar r)
  have hrank (r : Fin 3) : (D r).rank = (A r).rank := by
    rw [(hps r).isHermitian.rank_eq_card_non_zero_eigs,
      (hA.1 r).isHermitian.rank_eq_card_non_zero_eigs, heigs r]
  have htrace (r : Fin 3) : (D r).trace = (A r).trace := by
    change (g (A r)).trace = _
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]
  have hscores (f : ℝ → ℝ) (r : Fin 3) :
      ∑ a, f ((hA.1 r).isHermitian.eigenvalues a) = ∑ a, f (v r a) := by
    simp only [heigs r]
    exact spectral_of_diagonal f (hps r).isHermitian (v r) (hD r)
  refine ⟨⟨v, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r a
    exact (Complex.nonneg_iff.mp ((hps r).diag_nonneg (i := a))).1
  · intro a
    have h := congrArg (fun M : Matrix n n ℂ => (M a a).re) hsum
    simpa only [Matrix.add_apply, Complex.add_re, Matrix.one_apply_eq, Complex.one_re, v] using h
  · intro a
    have h : D j * D j = D j := by
      change g (A j) * g (A j) = g (A j)
      rw [← map_mul, hP]
    rw [hD j, Matrix.diagonal_mul_diagonal] at h
    have ha := congrArg (fun M : Matrix n n ℂ => (M a a).re) h
    have heq : v j a * v j a = v j a := by
      simpa only [Matrix.diagonal_apply_eq, Pi.mul_apply, ← Complex.ofReal_mul,
        Complex.ofReal_re] using ha
    rcases mul_eq_zero.mp (show v j a * (v j a - 1) = 0 by nlinarith only [heq]) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · intro r
    calc
      ∑ a, v r a = (D r).trace.re := by rw [hD r, trace_diagonal, Complex.re_sum]; simp
      _ = τ r := by rw [htrace, hA.2.2.1]
  · intro r
    rw [← rank_diagonal_real, ← hD, hrank]
    exact hA.2.2.2 r
  · intro f
    unfold spectralSum
    simp_rw [hscores]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun a _ => sum_three_labels _ hji hjk hik

private theorem binary_scores {p x y : ℝ}
    (hp : p = 0 ∨ p = 1) (hx : 0 ≤ x) (hy : 0 ≤ y) (hs : p + x + y = 1) :
    Real.negMulLog p + Real.negMulLog x + Real.negMulLog y = Real.binEntropy x ∧
      Real.negMulLog (1 - p) + Real.negMulLog (1 - x) + Real.negMulLog (1 - y)
        = Real.binEntropy x := by
  rcases hp with rfl | rfl
  · have hy' : y = 1 - x := by linarith
    rw [hy']
    have h : 1 - (1 - x) = x := by ring
    rw [h, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp [add_comm]
  · have hx' : x = 0 := by linarith
    have hy' : y = 0 := by linarith
    simp [hx', hy']

private theorem boundary_scores {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} {hp : ∀ r, (A r).PosSemidef} {j i k : Fin 3}
    (B : BoundaryCoordinates m τ A hp j i k) :
    spectralSum Real.negMulLog A hp = ∑ a, Real.binEntropy (B.v i a) ∧
      spectralSum (fun x => Real.negMulLog (1 - x)) A hp = ∑ a, Real.binEntropy (B.v i a) := by
  have he (a : n) :=
    binary_scores (B.projection a) (B.nonneg i a) (B.nonneg k a) (B.column a)
  refine ⟨(B.spectral _).trans (sum_congr rfl fun a _ => (he a).1),
    (B.spectral _).trans (sum_congr rfl fun a _ => (he a).2)⟩

/-- The common direct and complementary objective at every tuple of a boundary fiber. -/
theorem spectralSum_eq_complement_on_boundary {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} (hA : Feasible m τ A) {j i k : Fin 3}
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hj : τ j = 0 ∨ τ j = (cap (Fintype.card n) (m j) : ℝ)) :
    spectralSum Real.negMulLog A hA.1 =
      spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1 := by
  obtain ⟨B⟩ := boundary_coordinates hA hji hjk hik (projection_of_boundary hA hj)
  obtain ⟨hd, hc⟩ := boundary_scores B
  exact hd.trans hc.symm

/-- The binary entropy of `mass` split uniformly across `count` coordinates.
The zero-dimensional value is zero. -/
def boundaryValue (count : ℕ) (mass : ℝ) : ℝ :=
  (count : ℝ) * Real.binEntropy (mass / count)

private theorem binary_jensen {S : Finset n} {x : n → ℝ}
    (hx : ∀ a ∈ S, x a ∈ Set.Icc (0 : ℝ) 1) :
    (∑ a ∈ S, Real.binEntropy (x a)) ≤ boundaryValue S.card (∑ a ∈ S, x a) ∧
    ((∑ a ∈ S, Real.binEntropy (x a)) = boundaryValue S.card (∑ a ∈ S, x a) →
      ∀ a ∈ S, x a = (∑ b ∈ S, x b) / S.card) := by
  classical
  by_cases hS : S = ∅
  · simp [hS, boundaryValue]
  have hd : (0 : ℝ) < S.card := by
    exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
  let w : n → ℝ := fun _ => (S.card : ℝ)⁻¹
  have hw (a : n) (_ : a ∈ S) : 0 < w a := inv_pos.mpr hd
  have hw1 : ∑ a ∈ S, w a = 1 := by
    simp [w, nsmul_eq_mul, hd.ne']
  have hscale (f : ℝ → ℝ) : ∑ a ∈ S, w a • f (x a) = (∑ a ∈ S, f (x a)) / S.card := by
    simp only [w, smul_eq_mul, ← mul_sum, div_eq_mul_inv]
    exact mul_comm _ _
  have hle := Real.strictConcave_binEntropy.concaveOn.le_map_sum (fun a ha => (hw a ha).le) hw1 hx
  have havg : ∑ a ∈ S, w a • x a = (∑ a ∈ S, x a) / S.card := by
    simpa only [id_eq] using hscale id
  rw [havg, hscale Real.binEntropy] at hle
  refine ⟨by simpa only [boundaryValue, mul_comm (S.card : ℝ)] using
    (div_le_iff₀ hd).mp hle, ?_⟩
  intro heq
  have hJ : Real.binEntropy (∑ a ∈ S, w a • x a) = ∑ a ∈ S, w a • Real.binEntropy (x a) := by
    rw [havg, hscale Real.binEntropy, heq, boundaryValue,
      mul_comm (S.card : ℝ), mul_div_cancel_right₀ _ hd.ne']
  simpa only [havg] using (Real.strictConcave_binEntropy.map_sum_eq_iff hw hw1 hx).mp hJ

private theorem complement_support_count (v : n → ℝ) :
    (univ.filter fun a => v a = 0).card =
      Fintype.card n - (univ.filter fun a => v a ≠ 0).card := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset n)) (fun a => v a = 0)
  rw [card_univ] at h
  exact Nat.eq_sub_of_add_eq h

private theorem saturated_bound {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} {hp : ∀ r, (A r).PosSemidef} {j i k : Fin 3}
    (B : BoundaryCoordinates m τ A hp j i k)
    (hτ : τ j = (cap (Fintype.card n) (m j) : ℝ)) :
    (∑ a, Real.binEntropy (B.v i a)) ≤ boundaryValue (missing (Fintype.card n) (m j)) (τ i) := by
  let S := univ.filter (fun a => B.v j a = 0)
  let T := univ.filter (fun a => B.v j a ≠ 0)
  have hT (a : n) (ha : a ∈ T) : B.v j a = 1 :=
    (B.projection a).resolve_left (mem_filter.mp ha).2
  have hmass : (T.card : ℝ) = τ j := by
    calc
      (T.card : ℝ) = ∑ a ∈ T, (1 : ℝ) := by simp
      _ = ∑ a ∈ T, B.v j a := sum_congr rfl fun a ha => (hT a ha).symm
      _ = ∑ a, B.v j a := by
        apply sum_subset (filter_subset _ _)
        intro a ha hna
        by_contra hn
        exact hna (mem_filter.mpr ⟨ha, hn⟩)
      _ = τ j := B.mass j
  have hTc : T.card = cap (Fintype.card n) (m j) := by
    rw [hτ] at hmass
    exact_mod_cast hmass
  have hSc : S.card = missing (Fintype.card n) (m j) := by
    change (univ.filter fun a => B.v j a = 0).card = _
    rw [complement_support_count, show (univ.filter fun a => B.v j a ≠ 0).card =
      cap (Fintype.card n) (m j) from hTc]
    have h := cap_add_missing (Fintype.card n) (m j)
    omega
  have hzero (a : n) (ha : a ∈ univ) (hs : a ∉ S) : B.v i a = 0 := by
    have hp1 := hT a (mem_filter.mpr ⟨ha, fun h => hs (mem_filter.mpr ⟨ha, h⟩)⟩)
    linarith only [B.column a, B.nonneg i a, B.nonneg k a, hp1]
  have hx (a : n) (_ : a ∈ S) : B.v i a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨B.nonneg i a, by linarith only [B.column a, B.nonneg j a, B.nonneg k a]⟩
  have hsum : (∑ a ∈ S, B.v i a) = τ i :=
    (sum_subset (filter_subset _ _) hzero).trans (B.mass i)
  have hent : (∑ a ∈ S, Real.binEntropy (B.v i a)) = ∑ a, Real.binEntropy (B.v i a) :=
    sum_subset (filter_subset _ _) fun a ha hs => by rw [hzero a ha hs, Real.binEntropy_zero]
  simpa only [hsum, hSc, hent] using (binary_jensen hx).1

private theorem zero_row_bound {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    {A : Fin 3 → Matrix n n ℂ} {hp : ∀ r, (A r).PosSemidef} {j i k : Fin 3}
    (B : BoundaryCoordinates m τ A hp j i k) (hτ : τ j = 0) :
    (∑ a, Real.binEntropy (B.v i a)) ≤
      boundaryValue (Fintype.card n - missing (Fintype.card n) (m i) -
        missing (Fintype.card n) (m k)) (τ i - missing (Fintype.card n) (m k)) := by
  classical
  let d := Fintype.card n
  let l (r : Fin 3) := missing d (m r)
  have hz (a : n) : B.v j a = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun b _ => B.nonneg j b)).mp ((B.mass j).trans hτ) a (mem_univ a)
  have hcomplement (a : n) : B.v i a + B.v k a = 1 := by
    simpa only [hz a, zero_add] using B.column a
  have enough (r : Fin 3) :
      l r ≤ (univ.filter fun a => B.v r a = 0).card := by
    rw [complement_support_count]
    exact Nat.sub_le_sub_left (B.support r) d
  obtain ⟨Z, hZsub, hZcard⟩ := exists_subset_card_eq (enough i)
  obtain ⟨O, hOsub, hOcard⟩ := exists_subset_card_eq (enough k)
  have hZ (a : n) (ha : a ∈ Z) : B.v i a = 0 := (mem_filter.mp (hZsub ha)).2
  have hO (a : n) (ha : a ∈ O) : B.v i a = 1 := by
    have h := (mem_filter.mp (hOsub ha)).2
    linarith only [hcomplement a, h]
  have hdis : Disjoint Z O := by
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    exact zero_ne_one ((hZ a ha).symm.trans (hO a hb))
  let S := univ \ (Z ∪ O)
  have hcover : S ∪ (Z ∪ O) = (univ : Finset n) := by
    ext a
    by_cases ha : a ∈ Z ∪ O <;> simp [S, ha]
  have hdis' : Disjoint S (Z ∪ O) := by
    exact Finset.disjoint_left.mpr fun a ha hb => (mem_sdiff.mp ha).2 hb
  have hSc : S.card = d - l i - l k := by
    change ((univ : Finset n) \ (Z ∪ O)).card = d - l i - l k
    rw [card_sdiff_of_subset (subset_univ _), card_union_of_disjoint hdis, card_univ,
      hZcard, hOcard, Nat.sub_sub]
  have hsplit (f : ℝ → ℝ) :
      ∑ a, f (B.v i a) =
        (∑ a ∈ S, f (B.v i a)) + (l i : ℝ) * f 0 + (l k : ℝ) * f 1 := by
    have hZsum : (∑ a ∈ Z, f (B.v i a)) = (l i : ℝ) * f 0 := by
      rw [sum_congr rfl (fun a ha => congrArg f (hZ a ha))]
      simp [hZcard, nsmul_eq_mul]
    have hOsum : (∑ a ∈ O, f (B.v i a)) = (l k : ℝ) * f 1 := by
      rw [sum_congr rfl (fun a ha => congrArg f (hO a ha))]
      simp [hOcard, nsmul_eq_mul]
    have h := sum_union hdis' (f := fun a => f (B.v i a))
    rw [hcover, sum_union hdis, hZsum, hOsum] at h
    simpa only [add_assoc] using h
  have hmass : (∑ a ∈ S, B.v i a) = τ i - l k := by
    have h := hsplit id
    simp only [id_eq, mul_zero, add_zero, mul_one, B.mass] at h
    linarith
  have hent : (∑ a ∈ S, Real.binEntropy (B.v i a)) = ∑ a, Real.binEntropy (B.v i a) := by
    simpa only [Real.binEntropy_zero, Real.binEntropy_one, mul_zero, add_zero] using
      (hsplit Real.binEntropy).symm
  have hx (a : n) (_ : a ∈ S) : B.v i a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨B.nonneg i a, by linarith only [hcomplement a, B.nonneg k a]⟩
  simpa only [hSc, hmass, hent, d, l] using (binary_jensen hx).1

/-- A single feasible tuple attains both objectives, and the objectives agree at every
feasible tuple on the face. -/
def CommonMaximum (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) (v : ℝ) : Prop :=
  (∃ (A : Fin 3 → Matrix n n ℂ) (hA : Feasible m τ A),
    spectralSum Real.negMulLog A hA.1 = v ∧
    spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1 = v) ∧
  ∀ (A : Fin 3 → Matrix n n ℂ) (hA : Feasible m τ A),
    spectralSum Real.negMulLog A hA.1 =
      spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1 ∧
    spectralSum Real.negMulLog A hA.1 ≤ v

private def binaryRows (j i : Fin 3) (p x : ℝ) (r : Fin 3) : ℝ :=
  if r = j then p else if r = i then x else 1 - p - x

private theorem binaryRows_j {j i : Fin 3} (p x : ℝ) :
    binaryRows j i p x j = p := by simp [binaryRows]

private theorem binaryRows_i {j i : Fin 3} (hji : j ≠ i) (p x : ℝ) :
    binaryRows j i p x i = x := by simp [binaryRows, hji.symm]

private theorem binaryRows_k {j i k : Fin 3} (hjk : j ≠ k) (hik : i ≠ k) (p x : ℝ) :
    binaryRows j i p x k = 1 - p - x := by simp [binaryRows, hjk.symm, hik.symm]

/-- Realize the four original column types using the prescribed coordinate multiplicities. -/
private theorem diagonal_attainment {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ}
    (w : Fin 4 → ℕ) (hw : ∑ c, w c = Fintype.card n)
    (hwMiss : ∀ r, w r.castSucc = missing (Fintype.card n) (m r))
    (v : Fin 3 → Fin 4 → ℝ)
    (hv : ∀ r c, 0 ≤ v r c) (hcol : ∀ c, ∑ r, v r c = 1)
    (hrow : ∀ r, ∑ c, (w c : ℝ) * v r c = τ r) (hmiss : ∀ r, v r r.castSucc = 0) :
    ∃ (A : Fin 3 → Matrix n n ℂ) (hA : Feasible m τ A),
      ∀ f : ℝ → ℝ, spectralSum f A hA.1 = ∑ c, (w c : ℝ) * ∑ r, f (v r c) := by
  classical
  let E : n ≃ (Σ c : Fin 4, Fin (w c)) :=
    Fintype.equivOfCardEq (by simpa [Fintype.card_sigma] using hw.symm)
  let u (r : Fin 3) (a : n) := v r (E a).1
  let A (r : Fin 3) : Matrix n n ℂ := diagonal (fun a => (u r a : ℂ))
  have hsum (r : Fin 3) (f : ℝ → ℝ) :
      ∑ a, f (u r a) = ∑ c, (w c : ℝ) * f (v r c) := by
    rw [Fintype.sum_equiv E _ (fun y => f (v r y.1)) fun _ => rfl]
    simp [Fintype.sum_sigma, nsmul_eq_mul]
  have hp (r : Fin 3) : (A r).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro a
    exact Complex.nonneg_iff.mpr ⟨hv r (E a).1, by simp⟩
  have hs : ∑ r, A r = 1 := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp only [Matrix.sum_apply, A, diagonal_apply_eq, one_apply_eq, ← Complex.ofReal_sum, u]
      rw [hcol, Complex.ofReal_one]
    · simp [A, hab, Matrix.sum_apply]
  have htr (r : Fin 3) : (A r).trace.re = τ r := by
    simpa [A, trace_diagonal, Complex.re_sum] using (hsum r id).trans (hrow r)
  have hrank (r : Fin 3) : (A r).rank ≤ m r := by
    let count (z : ℝ) : ℝ := if z = 0 then 0 else 1
    have hcount : ((A r).rank : ℝ) = ∑ a, count (u r a) := by
      change ((diagonal fun a => (u r a : ℂ)).rank : ℝ) = _
      rw [rank_diagonal_real, Finset.natCast_card_filter]
      apply sum_congr rfl
      intro a _
      by_cases h : u r a = 0 <;> simp [count, h]
    have hreal : ((A r).rank : ℝ) ≤ m r := by
      rw [hcount, hsum]
      calc
        _ ≤ ∑ c ∈ univ.erase r.castSucc, (w c : ℝ) := by
          rw [← Finset.sum_erase_add _ _ (mem_univ r.castSucc), hmiss,
            show count 0 = 0 by simp [count], mul_zero, add_zero]
          apply sum_le_sum
          intro c _
          exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by unfold count; split <;> norm_num)
        _ = (Fintype.card n : ℝ) - (missing (Fintype.card n) (m r) : ℝ) := by
          have he := sum_erase_add univ (fun c => (w c : ℝ)) (mem_univ r.castSucc)
          have hwR : (∑ c, (w c : ℝ)) = (Fintype.card n : ℝ) := by exact_mod_cast hw
          rw [hwR, hwMiss] at he
          linarith
        _ ≤ (m r : ℝ) := by
          have h := cap_add_missing (Fintype.card n) (m r)
          have hR : (cap (Fintype.card n) (m r) : ℝ) + (missing (Fintype.card n) (m r) : ℝ)
              = Fintype.card n := by exact_mod_cast h
          have hm : (cap (Fintype.card n) (m r) : ℝ) ≤ m r := by
            exact_mod_cast (min_le_right (Fintype.card n) (m r))
          linarith
    exact_mod_cast hreal
  refine ⟨A, ⟨hp, hs, htr, hrank⟩, fun f => ?_⟩
  unfold spectralSum
  calc
    _ = ∑ r, ∑ c, (w c : ℝ) * f (v r c) := by
      exact sum_congr rfl fun r _ => (diagonal_entropy f (u r) (hp r).isHermitian).trans (hsum r f)
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

private theorem attain_binary_columns {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ} {j i k : Fin 3}
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hcap : ∑ r, missing (Fintype.card n) (m r) ≤ Fintype.card n)
    (htotal : ∑ r, τ r = Fintype.card n)
    (p x : Fin 4 → ℝ)
    (hp : ∀ c, p c = 0 ∨ p c = 1)
    (hx : ∀ c, 0 ≤ x c) (hpx : ∀ c, p c + x c ≤ 1)
    (hmissP : p j.castSucc = 0) (hmissX : x i.castSucc = 0)
    (hmissK : p k.castSucc + x k.castSucc = 1)
    (hrowP : ∑ c, (multiplicity (fun r => missing (Fintype.card n) (m r))
      (Fintype.card n - ∑ r, missing (Fintype.card n) (m r)) c : ℝ) * p c = τ j)
    (hrowX : ∑ c, (multiplicity (fun r => missing (Fintype.card n) (m r))
      (Fintype.card n - ∑ r, missing (Fintype.card n) (m r)) c : ℝ) * x c = τ i)
    (value : ℝ)
    (hvalue : ∑ c, (multiplicity (fun r => missing (Fintype.card n) (m r))
      (Fintype.card n - ∑ r, missing (Fintype.card n) (m r)) c : ℝ) * Real.binEntropy (x c)
        = value) :
    ∃ (A : Fin 3 → Matrix n n ℂ) (hA : Feasible m τ A),
      spectralSum Real.negMulLog A hA.1 = value ∧
      spectralSum (fun q => Real.negMulLog (1 - q)) A hA.1 = value := by
  let l (r : Fin 3) := missing (Fintype.card n) (m r)
  let b := Fintype.card n - ∑ r, l r
  let w := multiplicity l b
  have hw : ∑ c, w c = Fintype.card n := by
    rw [Fin.sum_univ_castSucc]
    simp only [w, UnequalBlockEffects.multiplicity_missing, show multiplicity l b (Fin.last 3) = b by rfl]
    exact Nat.add_sub_of_le hcap
  have hwR : (∑ c, (w c : ℝ)) = (Fintype.card n : ℝ) := by exact_mod_cast hw
  let v (r : Fin 3) (c : Fin 4) := binaryRows j i (p c) (x c) r
  have hj (c : Fin 4) : v j c = p c := binaryRows_j _ _
  have hi (c : Fin 4) : v i c = x c := binaryRows_i hji _ _
  have hk (c : Fin 4) : v k c = 1 - p c - x c := binaryRows_k hjk hik _ _
  have hv (r : Fin 3) (c : Fin 4) : 0 ≤ v r c := by
    by_cases hrj : r = j
    · rw [hrj, hj]
      rcases hp c with h | h <;> simp [h]
    by_cases hri : r = i
    · rw [hri, hi]
      exact hx c
    rw [eq_last_label hji hjk hik hrj hri, hk]
    linarith only [hpx c]
  have hcol (c : Fin 4) : ∑ r, v r c = 1 := by
    rw [sum_three_labels (fun r => v r c) hji hjk hik, hj, hi, hk]
    ring
  have hrow (r : Fin 3) : ∑ c, (w c : ℝ) * v r c = τ r := by
    by_cases hrj : r = j
    · simpa only [hrj, hj] using hrowP
    by_cases hri : r = i
    · simpa only [hri, hi] using hrowX
    rw [eq_last_label hji hjk hik hrj hri]
    simp only [hk, mul_sub, mul_one, sum_sub_distrib, hwR]
    change (_ - (∑ c, (w c : ℝ) * p c) - (∑ c, (w c : ℝ) * x c)) = _
    have hP : (∑ c, (w c : ℝ) * p c) = τ j := hrowP
    have hX : (∑ c, (w c : ℝ) * x c) = τ i := hrowX
    rw [hP, hX]
    rw [sum_three_labels τ hji hjk hik] at htotal
    linarith
  have hmiss (r : Fin 3) : v r r.castSucc = 0 := by
    by_cases hrj : r = j
    · simpa only [hrj, hj] using hmissP
    by_cases hri : r = i
    · simpa only [hri, hi] using hmissX
    rw [eq_last_label hji hjk hik hrj hri, hk]
    linarith only [hmissK]
  obtain ⟨A, hA, hscore⟩ := diagonal_attainment w hw (UnequalBlockEffects.multiplicity_missing l b) v hv hcol hrow hmiss
  have hbinary (c : Fin 4) : ∑ r, Real.negMulLog (v r c) = Real.binEntropy (x c) ∧
      ∑ r, Real.negMulLog (1 - v r c) = Real.binEntropy (x c) := by
    rw [sum_three_labels (fun r => Real.negMulLog (v r c)) hji hjk hik,
      sum_three_labels (fun r => Real.negMulLog (1 - v r c)) hji hjk hik, hj, hi]
    exact binary_scores (hp c) (hx c) (hv k c)
      (by simpa only [sum_three_labels _ hji hjk hik, hj, hi] using hcol c)
  have hval : (∑ c, (w c : ℝ) * Real.binEntropy (x c)) = value := hvalue
  exact ⟨A, hA, (hscore _).trans (by simp only [fun c => (hbinary c).1, hval]),
    (hscore _).trans (by simp only [fun c => (hbinary c).2, hval])⟩

private theorem normalized_mass {N : ℕ} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ N) :
    t / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ (N : ℝ) * (t / (N : ℝ)) = t := by
  by_cases hN : N = 0
  · have ht : t = 0 := le_antisymm (by simpa [hN] using h1) h0
    simp [hN, ht]
  · have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    exact ⟨⟨div_nonneg h0 hpos.le, (div_le_iff₀ hpos).mpr (by simpa using h1)⟩,
      by rw [mul_comm, div_mul_cancel₀ _ hpos.ne']⟩

private theorem sum_four_columns {G : Type*} [AddCommMonoid G] (f : Fin 4 → G)
    {j i k : Fin 3} (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k) :
    ∑ c, f c = f j.castSucc + f i.castSucc + f k.castSucc + f (Fin.last 3) := by
  rw [Fin.sum_univ_castSucc, sum_three_labels (fun r => f r.castSucc) hji hjk hik]

/-- At a saturated row, the other two rows split the complementary support uniformly.
The projection itself occupies all coordinates except the type missing its original label. -/
theorem saturated_face_maximum (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) {j i k : Fin 3}
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hcap : ∑ r, missing (Fintype.card n) (m r) ≤ Fintype.card n)
    (h0 : ∀ r, 0 ≤ τ r) (htotal : ∑ r, τ r = Fintype.card n)
    (hτ : τ j = (cap (Fintype.card n) (m j) : ℝ)) :
    CommonMaximum (n := n) m τ (boundaryValue (missing (Fintype.card n) (m j)) (τ i)) := by
  let d := Fintype.card n
  let l (r : Fin 3) := missing d (m r)
  let b := d - ∑ r, l r
  let w := multiplicity l b
  have hsum : τ j + τ i + τ k = (d : ℝ) :=
    (sum_three_labels τ hji hjk hik).symm.trans htotal
  have hcapJ : (cap d (m j) : ℝ) + (l j : ℝ) = d := by
    exact_mod_cast cap_add_missing d (m j)
  have hτi : τ i ≤ (l j : ℝ) := by linarith only [hsum, hcapJ, hτ, h0 k]
  obtain ⟨ha, hamass⟩ := normalized_mass (h0 i) hτi
  let a := τ i / (l j : ℝ)
  let p (c : Fin 4) : ℝ := if c = j.castSucc then 0 else 1
  let x (c : Fin 4) : ℝ := if c = j.castSucc then a else 0
  have hIJ : i.castSucc ≠ j.castSucc := fun h => hji.symm (Fin.castSucc_injective 3 h)
  have hKJ : k.castSucc ≠ j.castSucc := fun h => hjk.symm (Fin.castSucc_injective 3 h)
  have hLJ : Fin.last 3 ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
  have hwJ : w j.castSucc = l j := UnequalBlockEffects.multiplicity_missing _ _ _
  have hwI : w i.castSucc = l i := UnequalBlockEffects.multiplicity_missing _ _ _
  have hwK : w k.castSucc = l k := UnequalBlockEffects.multiplicity_missing _ _ _
  have hwL : w (Fin.last 3) = b := rfl
  have hbNat : l j + l i + l k + b = d := by
    have h := Nat.add_sub_of_le hcap
    change (∑ r, l r) + b = d at h
    rw [sum_three_labels l hji hjk hik] at h
    exact h
  have hb : (l j : ℝ) + (l i : ℝ) + (l k : ℝ) + (b : ℝ) = d := by exact_mod_cast hbNat
  refine ⟨?_, ?_⟩
  · refine attain_binary_columns (n := n) hji hjk hik hcap htotal p x ?_ ?_ ?_
      (by simp [p]) (by simp [x, hIJ]) (by simp [p, x, hKJ]) ?_ ?_
      (boundaryValue (l j) (τ i)) ?_
    · intro c
      by_cases h : c = j.castSucc <;> simp [p, h]
    · intro c
      by_cases h : c = j.castSucc
      · simpa [x, h, a] using ha.1
      · simp [x, h]
    · intro c
      by_cases h : c = j.castSucc
      · simpa [p, x, h, a] using ha.2
      · simp [p, x, h]
    · change (∑ c, (w c : ℝ) * p c) = τ j
      rw [sum_four_columns (fun c => (w c : ℝ) * p c) hji hjk hik]
      simp only [hwJ, hwI, hwK, hwL, p, hIJ, hKJ, hLJ, ite_false, ite_true, mul_zero,
        mul_one, zero_add]
      linarith only [hb, hcapJ, hτ]
    · change (∑ c, (w c : ℝ) * x c) = τ i
      rw [sum_four_columns (fun c => (w c : ℝ) * x c) hji hjk hik]
      simpa only [x, hIJ, hKJ, hLJ, hwJ, a, ite_true, ite_false, mul_zero,
        add_zero] using hamass
    · change (∑ c, (w c : ℝ) * Real.binEntropy (x c)) = boundaryValue (l j) (τ i)
      rw [sum_four_columns (fun c => (w c : ℝ) * Real.binEntropy (x c)) hji hjk hik]
      simp only [boundaryValue, x, a, hIJ, hKJ, hLJ, hwJ, ite_true, ite_false,
        Real.binEntropy_zero, mul_zero, add_zero]
  · intro A hA
    obtain ⟨B⟩ := boundary_coordinates hA hji hjk hik (projection_of_boundary hA (Or.inr hτ))
    obtain ⟨hd, hc⟩ := boundary_scores B
    exact ⟨hd.trans hc.symm, by rw [hd]; exact saturated_bound B hτ⟩

/-- At a zero row, the missing type of `i` forces zeros, the missing type of `k`
forces ones, and the missing type of `j` and the common type share the free allocation. -/
theorem zero_row_face_maximum (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) {j i k : Fin 3}
    (hji : j ≠ i) (hjk : j ≠ k) (hik : i ≠ k)
    (hcap : ∑ r, missing (Fintype.card n) (m r) ≤ Fintype.card n)
    (h0 : ∀ r, 0 ≤ τ r)
    (hle : ∀ r, τ r ≤ (cap (Fintype.card n) (m r) : ℝ))
    (htotal : ∑ r, τ r = Fintype.card n) (hτ : τ j = 0) :
    CommonMaximum (n := n) m τ
      (boundaryValue
        (Fintype.card n - missing (Fintype.card n) (m i) - missing (Fintype.card n) (m k))
        (τ i - missing (Fintype.card n) (m k))) := by
  let d := Fintype.card n
  let l (r : Fin 3) := missing d (m r)
  let b := d - ∑ r, l r
  let w := multiplicity l b
  let N := d - l i - l k
  have hsum : τ j + τ i + τ k = (d : ℝ) :=
    (sum_three_labels τ hji hjk hik).symm.trans htotal
  have hcapI : (cap d (m i) : ℝ) + (l i : ℝ) = d := by
    exact_mod_cast cap_add_missing d (m i)
  have hcapK : (cap d (m k) : ℝ) + (l k : ℝ) = d := by
    exact_mod_cast cap_add_missing d (m k)
  have hcount : l j + l i + l k + b = d := by
    have h := Nat.add_sub_of_le hcap
    change (∑ r, l r) + b = d at h
    rw [sum_three_labels l hji hjk hik] at h
    exact h
  have hN : l j + b = N := by
    change l j + b = d - l i - l k
    omega
  have hNR : (l j : ℝ) + (b : ℝ) = N := by exact_mod_cast hN
  have hcountR : (l j : ℝ) + (l i : ℝ) + (l k : ℝ) + (b : ℝ) = d := by
    exact_mod_cast hcount
  have hlo : 0 ≤ τ i - (l k : ℝ) := by linarith only [hτ, hsum, hcapK, hle k]
  have hhi : τ i - (l k : ℝ) ≤ (N : ℝ) := by
    linarith only [hcountR, hNR, hcapI, hle i]
  let a := (τ i - (l k : ℝ)) / (N : ℝ)
  obtain ⟨ha, hamass⟩ := normalized_mass hlo hhi
  let p (_ : Fin 4) : ℝ := 0
  let x (c : Fin 4) : ℝ := if c = i.castSucc then 0 else if c = k.castSucc then 1 else a
  have hJI : j.castSucc ≠ i.castSucc := fun h => hji (Fin.castSucc_injective 3 h)
  have hJK : j.castSucc ≠ k.castSucc := fun h => hjk (Fin.castSucc_injective 3 h)
  have hKI : k.castSucc ≠ i.castSucc := fun h => hik.symm (Fin.castSucc_injective 3 h)
  have hLI : Fin.last 3 ≠ i.castSucc := (Fin.castSucc_ne_last i).symm
  have hLK : Fin.last 3 ≠ k.castSucc := (Fin.castSucc_ne_last k).symm
  have hwJ : w j.castSucc = l j := UnequalBlockEffects.multiplicity_missing _ _ _
  have hwI : w i.castSucc = l i := UnequalBlockEffects.multiplicity_missing _ _ _
  have hwK : w k.castSucc = l k := UnequalBlockEffects.multiplicity_missing _ _ _
  have hwL : w (Fin.last 3) = b := rfl
  have hxa (c : Fin 4) : x c ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [x]
    split
    · exact ⟨le_rfl, zero_le_one⟩
    split
    · exact ⟨zero_le_one, le_rfl⟩
    exact ha
  refine ⟨?_, ?_⟩
  · refine attain_binary_columns (n := n) hji hjk hik hcap htotal p x (fun _ => Or.inl rfl)
      (fun c => (hxa c).1) (fun c => by simpa [p] using (hxa c).2) rfl
      (by simp [x]) (by simp [p, x, hKI]) ?_ ?_ (boundaryValue N (τ i - l k)) ?_
    · simp [p, hτ]
    · change (∑ c, (w c : ℝ) * x c) = τ i
      rw [sum_four_columns (fun c => (w c : ℝ) * x c) hji hjk hik]
      simp only [x, hJI, hJK, hKI, hLI, hLK, hwJ, hwK, hwL, ite_true, ite_false,
        mul_zero, mul_one, add_zero]
      have hm : (N : ℝ) * a = τ i - (l k : ℝ) := hamass
      rw [← hNR, add_mul] at hm
      linarith
    · change (∑ c, (w c : ℝ) * Real.binEntropy (x c)) = boundaryValue N (τ i - l k)
      rw [sum_four_columns (fun c => (w c : ℝ) * Real.binEntropy (x c)) hji hjk hik]
      simp only [x, hJI, hJK, hKI, hLI, hLK, hwJ, hwL, ite_true, ite_false,
        Real.binEntropy_zero, Real.binEntropy_one, mul_zero, add_zero]
      rw [← add_mul, hNR] <;> rfl
  · intro A hA
    obtain ⟨B⟩ := boundary_coordinates hA hji hjk hik (projection_of_boundary hA (Or.inl hτ))
    obtain ⟨hd, hc⟩ := boundary_scores B
    exact ⟨hd.trans hc.symm, by rw [hd]; exact zero_row_bound B hτ⟩

end
end D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary
