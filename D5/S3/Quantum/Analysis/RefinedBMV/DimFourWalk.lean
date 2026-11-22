/- GID: D5/S3/Quantum/Analysis/RefinedBMV/DimFourWalk
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/DimFourWalk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A four-vertex cubic walk bound from columnwise positive quadratic forms. -/

import D5.S3.Quantum.Analysis.RefinedBMVDimThree

/-! # The four-vertex cubic walk bound -/

open Matrix
open scoped ComplexOrder BigOperators

namespace RefinedBMV.DimFour

noncomputable section

private abbrev Vertex := Fin 4
private abbrev Mat := Matrix Vertex Vertex ℂ

private def first : Vertex → Vertex := ![1, 0, 0, 0]
private def second : Vertex → Vertex := ![2, 2, 1, 1]
private def third : Vertex → Vertex := ![3, 3, 3, 2]

private def omitted (i j k : Vertex) : Vertex := Fin.ofNat 4 (6 - i.val - j.val - k.val)

private def oriented (F : Vertex → Vertex → Vertex → ℝ) (f : Vertex) : ℝ :=
  F (first f) (second f) (third f) + F (second f) (third f) (first f) +
    F (third f) (first f) (second f)

private theorem face_order (F : Vertex → Vertex → Vertex → ℝ)
    (hs : ∀ i j k, F j i k = F i j k) (hr : ∀ i j k, F j k i = F i j k)
    (i j k : Vertex) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    F i j k = F (first (omitted i j k)) (second (omitted i j k))
      (third (omitted i j k)) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all (config := {decide := true}) only [omitted, first, second, third] <;>
    first | exact (hr ..).symm | exact (hs ..).trans (hr ..)

private theorem omitted_vertex (i j k h : Vertex)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    omitted i j k = h ↔ h ≠ i ∧ h ≠ j ∧ h ≠ k := by
  revert hki hjk hij i j k h
  decide +kernel

private theorem oriented_ne (f : Vertex) :
    first f ≠ second f ∧ second f ≠ third f ∧ third f ≠ first f ∧
      omitted (first f) (second f) (third f) = f ∧
      omitted (second f) (third f) (first f) = f ∧
      omitted (third f) (first f) (second f) = f := by
  revert f
  decide +kernel

private def cycleProduct (B : Mat) (i j k : Vertex) : ℂ :=
  B i j * B j k * B k i

private theorem conj_entry (B : Mat) (hB : B.IsHermitian) (i j : Vertex) :
    star (B i j) = B j i := congrFun (congrFun hB j) i

private theorem cycleProduct_rotate (B : Mat) (i j k : Vertex) :
    cycleProduct B j k i = cycleProduct B i j k := by
  unfold cycleProduct
  ring

private theorem cycleProduct_reverse (B : Mat) (hB : B.IsHermitian) (i j k : Vertex) :
    cycleProduct B j i k = star (cycleProduct B i j k) := by
  simp only [cycleProduct, star_mul, conj_entry B hB]
  ring

private def faceValue (B : Mat) (f : Vertex) : ℝ :=
  (cycleProduct B (first f) (second f) (third f)).re

private theorem re_cycle (B : Mat) (hB : B.IsHermitian)
    (i j k : Vertex) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    (cycleProduct B i j k).re = faceValue B (omitted i j k) := by
  apply face_order (fun i j k ↦ (cycleProduct B i j k).re) _ _ i j k hij hjk hki
  · intro i j k
    rw [cycleProduct_reverse B hB]
    rfl
  · intro i j k
    rw [cycleProduct_rotate]

private def adjusted (B U : Mat) (i j k : Vertex) : ℂ :=
  cycleProduct B i j k * star (U i k) * U j k

private theorem adjusted_reverse (B U : Mat) (hB : B.IsHermitian) (i j k : Vertex) :
    adjusted B U j i k = star (adjusted B U i j k) := by
  simp only [adjusted, cycleProduct_reverse B hB i j k, star_mul, star_star]
  ring

private def unitPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

private theorem norm_unitPhase (z : ℂ) : ‖unitPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [unitPhase, hz]
  · simp [unitPhase, hz, norm_ne_zero_iff.mpr hz]

private theorem mul_star_unitPhase (z : ℂ) : z * star (unitPhase z) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    rw [unitPhase, ite_eq_right hz, star_div₀, show star (‖z‖ : ℂ) = (‖z‖ : ℂ) from
      Complex.conj_ofReal _, ← mul_div_assoc, Complex.star_def, Complex.mul_conj',
      pow_two, mul_div_cancel_right₀ _ hn]

private def hubPhase (B : Mat) (h : Vertex) : Mat :=
  fun i k ↦ if i = h ∨ k = h then 1 else -star (unitPhase (cycleProduct B h i k))

private theorem norm_hubPhase (B : Mat) (h i k : Vertex) : ‖hubPhase B h i k‖ = 1 := by
  unfold hubPhase
  split <;> simp [norm_unitPhase]

private theorem adjusted_hub_edge (B : Mat) (h i k : Vertex) (hi : i ≠ h) (hk : k ≠ h) :
    adjusted B (hubPhase B h) h i k = -(‖cycleProduct B h i k‖ : ℂ) := by
  simp only [adjusted, hubPhase, true_or, ite_true, hi, hk, or_self, ite_false,
    star_one, mul_one, mul_neg, mul_star_unitPhase]

private theorem adjusted_hub_opposite (B : Mat) (hB : B.IsHermitian)
    (h i j k : Vertex) (hi : i ≠ h) (hj : j ≠ h) (hk : k ≠ h)
    (h₁ : cycleProduct B h i k ≠ 0) (h₂ : cycleProduct B h j k ≠ 0) :
    (adjusted B (hubPhase B h) i j k).re =
      ((‖B i k‖ ^ 2 * ‖B j k‖ ^ 2 * ‖B h k‖ ^ 2) /
        (‖cycleProduct B h i k‖ * ‖cycleProduct B h j k‖)) *
        (cycleProduct B i j h).re := by
  have hprod : cycleProduct B i j k * cycleProduct B h i k *
      star (cycleProduct B h j k) =
      (↑(‖B i k‖ ^ 2 * ‖B j k‖ ^ 2 * ‖B h k‖ ^ 2) : ℂ) * cycleProduct B i j h := by
    have hnorm (x y : Vertex) :
        B x y * B y x = (↑(‖B x y‖ ^ 2) : ℂ) := by
      rw [← conj_entry B hB x y, Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    rw [cycleProduct_reverse B hB h j k |>.symm]
    simp only [cycleProduct, Complex.ofReal_mul]
    rw [← hnorm i k, ← hnorm j k, ← hnorm h k]
    ring
  have heq : adjusted B (hubPhase B h) i j k =
      (cycleProduct B i j k * cycleProduct B h i k * star (cycleProduct B h j k)) /
        ((‖cycleProduct B h i k‖ : ℂ) * (‖cycleProduct B h j k‖ : ℂ)) := by
    simp only [adjusted, hubPhase, hi, hj, hk, or_self, ite_false, star_neg, star_star,
      mul_neg, neg_mul, neg_neg, unitPhase, ite_eq_right h₁, ite_eq_right h₂, star_div₀,
      show ∀ r : ℝ, star (r : ℂ) = r from Complex.conj_ofReal]
    rw [← mul_div_assoc (cycleProduct B i j k) (cycleProduct B h i k),
      div_mul_div_comm]
  rw [heq, hprod, ← Complex.ofReal_mul, mul_comm, mul_div_assoc, ← Complex.ofReal_div,
    Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero, mul_comm]

private theorem hub_phase_bounds (B : Mat) (hB : B.IsHermitian) (h : Vertex)
    (hn : ∀ f, f ≠ h → faceValue B f < 0)
    (i j k : Vertex) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    (adjusted B (hubPhase B h) i j k).re ≤
      if omitted i j k = h then 0 else faceValue B (omitted i j k) := by
  have hmiss := omitted_vertex i j k h hij hjk hki
  have nonzero (x y : Vertex) (hx : x ≠ h) (hy : y ≠ h) (hxy : x ≠ y) :
      (cycleProduct B h x y).re < 0 := by
    rw [re_cycle B hB h x y hx.symm hxy hy]
    exact hn _ (fun e ↦ (omitted_vertex h x y h hx.symm hxy hy |>.mp e).1 rfl)
  by_cases hk : k = h
  · subst k
    rw [ite_eq_right (fun e ↦ (hmiss.mp e).2.2 rfl), ← re_cycle B hB i j h hij hjk hki]
    simp [adjusted, hubPhase]
  by_cases hi : i = h
  · subst i
    rw [ite_eq_right (fun e ↦ (hmiss.mp e).1 rfl), adjusted_hub_edge B h j k hij.symm hk,
      ← re_cycle B hB h j k hij hjk hki, Complex.neg_re, Complex.ofReal_re]
    exact (abs_le.mp (Complex.abs_re_le_norm _)).1
  by_cases hj : j = h
  · subst j
    rw [ite_eq_right (fun e ↦ (hmiss.mp e).2.1 rfl), ← re_cycle B hB i h k hij hjk hki,
      adjusted_reverse B (hubPhase B h) hB h i k,
      adjusted_hub_edge B h i k hij hk, cycleProduct_reverse B hB h i k]
    simpa only [Complex.star_def, Complex.conj_re, Complex.neg_re, Complex.ofReal_re] using
      (abs_le.mp (Complex.abs_re_le_norm (cycleProduct B h i k))).1
  rw [ite_eq_left (hmiss.mpr ⟨Ne.symm hi, Ne.symm hj, Ne.symm hk⟩)]
  have nz (x y : Vertex) (hx : x ≠ h) (hy : y ≠ h) (hxy : x ≠ y) :
      cycleProduct B h x y ≠ 0 := by
    intro e
    simpa [e] using nonzero x y hx hy hxy
  rw [adjusted_hub_opposite B hB h i j k hi hj hk (nz i k hi hk hki.symm) (nz j k hj hk hjk),
    re_cycle B hB i j h hij hj (Ne.symm hi)]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (hn _ ?_).le
  exact fun e ↦ (omitted_vertex i j h h hij hj (Ne.symm hi) |>.mp e).2.2 rfl

-- A row equal to the column on this table represents an unflipped column.
private def flip (a b c d : Bool) : Vertex → Vertex :=
  match a, b, c, d with
  | false, false, false, false => ![1, 0, 3, 2]
  | true,  false, false, false => ![0, 0, 0, 0]
  | false, true,  false, false => ![0, 0, 1, 1]
  | true,  true,  false, false => ![1, 0, 2, 3]
  | false, false, true,  false => ![0, 2, 0, 2]
  | true,  false, true,  false => ![2, 1, 0, 3]
  | false, true,  true,  false => ![0, 2, 1, 3]
  | false, false, false, true  => ![0, 3, 3, 0]
  | true,  false, false, true  => ![3, 1, 2, 0]
  | false, true,  false, true  => ![0, 3, 2, 1]
  | false, false, true,  true  => ![0, 1, 3, 2]
  | _, _, _, _ => ![0, 1, 2, 3]

private def agree (m : Vertex → Vertex) (i j k : Vertex) : Bool :=
  (i == m k) == (j == m k)

private def realPhase (m : Vertex → Vertex) : Mat :=
  fun i k ↦ if i = m k then -1 else 1

private theorem adjusted_real (B : Mat) (m : Vertex → Vertex) (i j k : Vertex) :
    (adjusted B (realPhase m) i j k).re =
      if agree m i j k then (cycleProduct B i j k).re else -(cycleProduct B i j k).re := by
  by_cases hi : i = m k <;> by_cases hj : j = m k <;> simp [adjusted, realPhase, agree, hi, hj]

private def threeNeg (b : Vertex → Bool) : Prop :=
  ∃ f, b f = false ∧ ∀ g, g ≠ f → b g = true

private theorem flip_spec (a b c d : Bool) (h : ¬ threeNeg ![a, b, c, d]) (f : Vertex) :
    let m := flip a b c d
    let x := agree m (first f) (second f) (third f)
    let y := agree m (second f) (third f) (first f)
    let z := agree m (third f) (first f) (second f)
    if (![a, b, c, d] : Vertex → Bool) f then x = true ∧ y = true ∧ z = true
    else (x = false ∧ y = false) ∨ (y = false ∧ z = false) ∨ (z = false ∧ x = false) := by
  revert h a b c d f
  unfold threeNeg
  decide +kernel

private theorem signed_sum (x y z : Bool) (u v w d t : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hU : u ≤ d) (hV : v ≤ d) (hW : w ≤ d)
    (ht : 0 ≤ t)
    (hs : (x = false ∧ y = false) ∨ (y = false ∧ z = false) ∨ (z = false ∧ x = false)) :
    u * (if x then t else -t) + v * (if y then t else -t) +
      w * (if z then t else -t) ≤ d * t := by
  cases x <;> cases y <;> cases z <;> simp_all <;>
    nlinarith only [mul_nonneg hu ht, mul_nonneg hv ht, mul_nonneg hw ht,
      mul_le_mul_of_nonneg_right hU ht, mul_le_mul_of_nonneg_right hV ht,
      mul_le_mul_of_nonneg_right hW ht]

private theorem choose_phase (B : Mat) (hB : B.IsHermitian)
    (P : Vertex → Vertex → Vertex → ℝ) (D : Vertex → ℝ)
    (hn : ∀ i j k, 0 ≤ P i j k)
    (hone : ∀ f, P (first f) (second f) (third f) ≤ D f ∧
      P (second f) (third f) (first f) ≤ D f ∧ P (third f) (first f) (second f) ≤ D f)
    (hsum : ∀ f, D f ≤ oriented P f) :
    ∃ U : Mat, (∀ i k, ‖U i k‖ = 1) ∧ ∀ f,
      oriented (fun i j k ↦ P i j k * (adjusted B U i j k).re) f ≤ D f * faceValue B f := by
  classical
  let b (f : Vertex) : Bool := decide (faceValue B f < 0)
  by_cases h : threeNeg b
  · obtain ⟨v, hv, hneg⟩ := h
    have hn' (f : Vertex) (hf : f ≠ v) : faceValue B f < 0 := of_decide_eq_true (hneg f hf)
    have hp : 0 ≤ faceValue B v := le_of_not_gt (of_decide_eq_false hv)
    refine ⟨hubPhase B v, norm_hubPhase B v, fun f ↦ ?_⟩
    obtain ⟨hij, hjk, hki, he₁, he₂, he₃⟩ := oriented_ne f
    have h₁ := mul_le_mul_of_nonneg_left
      (hub_phase_bounds B hB v hn' _ _ _ hij hjk hki) (hn (first f) (second f) (third f))
    have h₂ := mul_le_mul_of_nonneg_left
      (hub_phase_bounds B hB v hn' _ _ _ hjk hki hij) (hn (second f) (third f) (first f))
    have h₃ := mul_le_mul_of_nonneg_left
      (hub_phase_bounds B hB v hn' _ _ _ hki hij hjk) (hn (third f) (first f) (second f))
    simp only [he₁, he₂, he₃] at h₁ h₂ h₃
    have hc := add_le_add (add_le_add h₁ h₂) h₃
    by_cases hf : f = v
    · subst f
      have hc' : oriented (fun i j k ↦ P i j k * (adjusted B (hubPhase B v) i j k).re) v ≤ 0 := by
        simpa [oriented] using hc
      exact hc'.trans (mul_nonneg ((hn _ _ _).trans (hone v).1) hp)
    · simpa [ite_eq_right hf, oriented, add_mul] using hc.trans
        (show _ ≤ D f * faceValue B f from by
          simp only [ite_eq_right hf, ← add_mul]
          exact mul_le_mul_of_nonpos_right (hsum f) (hn' f hf).le)
  · have hb : (![b 0, b 1, b 2, b 3] : Vertex → Bool) = b := by
      funext i
      fin_cases i <;> rfl
    let m := flip (b 0) (b 1) (b 2) (b 3)
    refine ⟨realPhase m, fun i k ↦ by unfold realPhase; split <;> simp, fun f ↦ ?_⟩
    obtain ⟨hij, hjk, hki, he₁, he₂, he₃⟩ := oriented_ne f
    have hs := flip_spec (b 0) (b 1) (b 2) (b 3) (hb ▸ h) f
    dsimp only at hs
    change (if (![b 0, b 1, b 2, b 3] : Vertex → Bool) f then
      _ else _) at hs
    rw [hb] at hs
    have hr₁ := re_cycle B hB _ _ _ hij hjk hki
    have hr₂ := re_cycle B hB _ _ _ hjk hki hij
    have hr₃ := re_cycle B hB _ _ _ hki hij hjk
    rw [he₁] at hr₁
    rw [he₂] at hr₂
    rw [he₃] at hr₃
    simp only [oriented, adjusted_real, hr₁, hr₂, hr₃]
    cases hf : b f
    · simp only [hf, Bool.false_eq_true, ite_false] at hs
      exact signed_sum _ _ _ _ _ _ _ _ (hn _ _ _) (hn _ _ _) (hn _ _ _)
        (hone f).1 (hone f).2.1 (hone f).2.2 (le_of_not_gt (of_decide_eq_false hf)) hs
    · simp only [hf, ite_true] at hs
      change agree m _ _ _ = true ∧ agree m _ _ _ = true ∧ agree m _ _ _ = true at hs
      simp only [hs.1, hs.2.1, hs.2.2, ite_true, ← add_mul]
      exact mul_le_mul_of_nonpos_right (hsum f) (of_decide_eq_true hf).le

private theorem sum_swap (F : Vertex → Vertex → Vertex → ℝ)
    (hs : ∀ i j k, F j i k = F i j k) :
    (∑ i, ∑ j, ∑ k, F i j k) =
      (∑ i, ∑ k, F i i k) +
      2 * (∑ i, ∑ j, if i = j then 0 else F i j i) +
      2 * ∑ f, oriented F f := by
  simp (config := {decide := true}) only [Fin.sum_univ_four, oriented, first, second, third,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, ite_true, ite_false,
    hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
  ring

private def repeated (B : Mat) (δ : Vertex → Vertex → ℝ) (i k : Vertex) : ℝ :=
  (B i i).re * ‖B i k‖ ^ 2 * δ i k

private theorem diagonal_cycle (B : Mat) (hB : B.IsHermitian) (i k : Vertex) :
    (cycleProduct B i i k).re = (B i i).re * ‖B i k‖ ^ 2 := by
  have he : B i k * B k i = (↑(‖B i k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← conj_entry B hB i k, Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
  rw [cycleProduct, mul_assoc, he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private def columnWitness (B U : Mat) (δ : Vertex → Vertex → ℝ) : Mat :=
  fun i k ↦ B i k * U i k * (Real.sqrt (δ i k) : ℂ)

private theorem trace_witness (B U : Mat) (hB : B.PosSemidef) (hu : ∀ i k, ‖U i k‖ = 1)
    (δ : Vertex → Vertex → ℝ) (hn : ∀ i k, 0 ≤ δ i k) (hz : ∀ i, δ i i = 0) :
    0 ≤ (∑ i, ∑ k, repeated B δ i k) +
      2 * ∑ f, oriented (fun i j k ↦
        (Real.sqrt (δ i k) * Real.sqrt (δ j k)) * (adjusted B U i j k).re) f := by
  let V := columnWitness B U δ
  let F (i j k : Vertex) := (Real.sqrt (δ i k) * Real.sqrt (δ j k)) *
    (adjusted B U i j k).re
  have hs (i j k : Vertex) : F j i k = F i j k := by
    simp only [F, adjusted_reverse B U hB.isHermitian i j k, Complex.star_def, Complex.conj_re,
      mul_comm (Real.sqrt (δ j k))]
  have htrace : (trace (Vᴴ * B * V)).re = ∑ i, ∑ j, ∑ k, F i j k := by
    simp only [trace, diag, Matrix.mul_apply, Finset.sum_mul, Complex.re_sum]
    calc
      _ = ∑ k, ∑ j, ∑ i, F i j k := by
        refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦
          Finset.sum_congr rfl fun i _ ↦ ?_
        change ((star (V i k) * B i j) * V j k).re = _
        have he : star (V i k) * B i j * V j k =
            (↑(Real.sqrt (δ i k) * Real.sqrt (δ j k)) : ℂ) * adjusted B U i j k := by
          simp only [V, columnWitness, adjusted, cycleProduct, star_mul,
            show ∀ x : ℝ, star (x : ℂ) = x from Complex.conj_ofReal,
            conj_entry B hB.isHermitian i k, Complex.ofReal_mul]
          ring
        rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = _ := by
        calc
          _ = ∑ j, ∑ k, ∑ i, F i j k := Finset.sum_comm
          _ = ∑ j, ∑ i, ∑ k, F i j k :=
            Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
          _ = _ := Finset.sum_comm
  have hdiag (i k : Vertex) : F i i k = repeated B δ i k := by
    have hunit : star (U i k) * U i k = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hu, Complex.ofReal_one, one_pow]
    simp only [F, adjusted, mul_assoc, hunit, mul_one, diagonal_cycle B hB.isHermitian]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hn i k)]
    unfold repeated
    ring
  have hrep (i j : Vertex) : F i j i = 0 := by simp [F, hz]
  have hp := (Complex.nonneg_iff.mp (hB.conjTranspose_mul_mul_same V).trace_nonneg).1
  simpa only [htrace, sum_swap F hs, hdiag, hrep, ite_self, Finset.sum_const_zero,
    mul_zero, add_zero] using hp

/-- A symmetric defect on four vertices has a nonnegative PSD walk if its
mixed value lies between every individual geometric mean and their sum. -/
theorem walk_nonneg (d : ℝ → ℝ → ℝ → ℝ) (a : Vertex → ℝ)
    (B : Mat) (hB : B.PosSemidef)
    (hn : ∀ i j k, 0 ≤ d (a i) (a j) (a k)) (hz : ∀ x, d x x x = 0)
    (hs : ∀ x y z, d y x z = d x y z) (hr : ∀ x y z, d y z x = d x y z)
    (hone : ∀ i j k, d (a i) (a i) (a k) * d (a j) (a j) (a k) ≤ d (a i) (a j) (a k) ^ 2)
    (hsum : ∀ i j k, d (a i) (a j) (a k) ≤ DimThree.paired d (a i) (a j) (a k)) :
    0 ≤ walk B (fun i j k ↦ (d (a i) (a j) (a k) : ℂ)) := by
  let δ (i k : Vertex) := d (a i) (a i) (a k)
  let P (i j k : Vertex) := Real.sqrt (δ i k) * Real.sqrt (δ j k)
  let D (f : Vertex) := d (a (first f)) (a (second f)) (a (third f))
  have hP (i j k : Vertex) : 0 ≤ P i j k := by dsimp [P]; positivity
  have hle (i j k : Vertex) : P i j k ≤ d (a i) (a j) (a k) := by
    apply (sq_le_sq₀ (hP i j k) (hn i j k)).mp
    simpa only [P, δ, mul_pow, Real.sq_sqrt (hn i i k), Real.sq_sqrt (hn j j k)] using hone i j k
  have hrot (i j k : Vertex) : d (a k) (a i) (a j) = d (a i) (a j) (a k) :=
    (hr _ _ _).symm
  have hpair (f : Vertex) : D f ≤ oriented P f := by
    simpa only [D, oriented, P, δ, DimThree.paired, Real.sqrt_mul (hn _ _ _),
      mul_comm, add_comm, add_left_comm, add_assoc] using hsum (first f) (second f) (third f)
  obtain ⟨U, hu, hU⟩ := choose_phase B hB.isHermitian P D hP
    (fun f ↦ ⟨hle _ _ _,
      (hle (second f) (third f) (first f)).trans_eq (hr _ _ _),
      (hle (third f) (first f) (second f)).trans_eq (hrot _ _ _)⟩) hpair
  have hp := trace_witness B U hB hu δ (fun i k ↦ hn i i k) (fun i ↦ hz (a i))
  have htotal : 0 ≤ (∑ i, ∑ k, repeated B δ i k) +
      2 * ∑ f, D f * faceValue B f := by
    have hf := Finset.sum_le_sum (s := Finset.univ) fun f _ ↦ hU f
    have hh := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ 2 by norm_num)
    exact hp.trans (add_le_add (le_refl _) hh)
  let F (i j k : Vertex) := d (a i) (a j) (a k) * (cycleProduct B i j k).re
  have hswap (i j k : Vertex) : F j i k = F i j k := by
    simp only [F, hs (a i) (a j) (a k), cycleProduct_reverse B hB.isHermitian i j k,
      Complex.star_def, Complex.conj_re]
  have hcycle (i j k : Vertex) : F j k i = F i j k := by
    simp only [F, hr (a i) (a j) (a k), cycleProduct_rotate B i j k]
  have hdiag (i k : Vertex) : F i i k = repeated B δ i k := by
    rw [show F i i k = δ i k * (cycleProduct B i i k).re from rfl,
      diagonal_cycle B hB.isHermitian, repeated, mul_comm]
  have hrep (i j : Vertex) : (if i = j then 0 else F i j i) = repeated B δ i j := by
    by_cases hij : i = j
    · subst j; simp [repeated, δ, hz]
    · rw [ite_eq_right hij, hcycle i i j, hdiag]
  have hface (f : Vertex) : oriented F f = 3 * (D f * faceValue B f) := by
    simp only [oriented, hcycle (first f) (second f) (third f),
      hcycle (second f) (third f) (first f)]
    change D f * faceValue B f + D f * faceValue B f + D f * faceValue B f = _
    ring
  let Z (i j k : Vertex) := cycleProduct B i j k * (d (a i) (a j) (a k) : ℂ)
  change 0 ≤ ∑ i, ∑ j, ∑ k, Z i j k
  have hconj (i j k : Vertex) : star (Z i j k) = Z j i k := by
    simp only [Z, star_mul, cycleProduct_reverse B hB.isHermitian i j k, hs (a i) (a j) (a k),
      show ∀ x : ℝ, star (x : ℂ) = x from Complex.conj_ofReal]
    ring
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · have hRe (i j k : Vertex) : (Z i j k).re = F i j k := by
      simp [Z, F, Complex.mul_re, mul_comm]
    simp only [Complex.re_sum, hRe, sum_swap F hswap, hdiag, hrep, hface, ← Finset.mul_sum]
    linarith only [htotal]
  · have he : star (∑ i, ∑ j, ∑ k, Z i j k) = ∑ i, ∑ j, ∑ k, Z i j k := by
      simp only [star_sum, hconj]
      exact Finset.sum_comm
    exact ((Complex.im_eq_zero_iff_isSelfAdjoint _).mpr he).symm

#print axioms walk_nonneg

end

end RefinedBMV.DimFour
