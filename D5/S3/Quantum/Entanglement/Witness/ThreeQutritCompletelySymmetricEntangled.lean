/- GID: D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.claim; result=D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.result; claim=D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.claim
   digest: A completely symmetric three-qutrit density matrix is entangled. -/

import D5.S3.Quantum.Entanglement.OccupancyWordSectors
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum

/-! A count-invariant density matrix separated from pure product mixtures. -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled

open Matrix MultilinearMap
open D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.MMDCounts
  (count_ofFn)
open D5.S3.Quantum.Entanglement.OccupancyWordSectors (Word occupation)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open scoped BigOperators ComplexOrder

/-- Invariance under all permutations of the ket and bra index positions. -/
def IsCompletelySymmetric {d : ℕ} (ρ : Matrix (Word (Fin 3) d) (Word (Fin 3) d) ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin d ⊕ Fin d)) (i j : Word (Fin 3) d),
    ρ (fun k => Sum.elim i j (π (Sum.inl k)))
      (fun k => Sum.elim i j (π (Sum.inr k))) = ρ i j

/-- A finite convex combination of projectors onto unit pure product vectors. -/
def IsFullySeparable {d : ℕ} (ρ : Matrix (Word (Fin 3) d) (Word (Fin 3) d) ℂ) : Prop :=
  ∃ (n : ℕ) (wt : Fin n → ℝ) (v : Fin n → Fin d → Fin 3 → ℂ),
    (∀ i, 0 < wt i) ∧ (∑ i, wt i) = 1 ∧
    (∀ i k, ∑ j, Complex.normSq (v i k j) = 1) ∧
    ρ = ∑ i, (wt i : ℂ) •
      vecMulVec (piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin d) ℂ) (v i))
        (star (piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin d) ℂ) (v i)))

/-- Every completely symmetric state of at least three qutrits is fully separable. -/
def claim : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ ρ : Matrix (Word (Fin 3) d) (Word (Fin 3) d) ℂ,
    IsDensity ρ → IsCompletelySymmetric ρ → IsFullySeparable ρ

private def counts (w : Word (Fin 3) 3) : Fin 3 → ℕ :=
  fun j => (occupation w).count j

private def moment (q : Fin 3 → ℕ) : ℝ :=
  if q = ![6, 0, 0] ∨ q = ![0, 6, 0] then 132
  else if q = ![0, 0, 6] then 3
  else if q = ![4, 2, 0] ∨ q = ![2, 4, 0] ∨ q = ![2, 2, 2] then 4
  else if q = ![4, 0, 2] ∨ q = ![0, 4, 2] then 20
  else if q = ![2, 0, 4] ∨ q = ![0, 2, 4] then 6
  else 0

private def state : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ :=
  fun a b => ((moment (fun j => counts a j + counts b j) / 471 : ℝ) : ℂ)

private def gramVector (k : Fin 7) (w : Word (Fin 3) 3) : ℂ :=
  ![if counts w = ![3, 0, 0] ∨ counts w = ![1, 2, 0] ∨ counts w = ![1, 0, 2]
      then 1 else 0,
    if counts w = ![3, 0, 0] then 8 else if counts w = ![1, 0, 2] then 1 else 0,
    if counts w = ![0, 3, 0] ∨ counts w = ![2, 1, 0] ∨ counts w = ![0, 1, 2]
      then 1 else 0,
    if counts w = ![0, 3, 0] then 8 else if counts w = ![0, 1, 2] then 1 else 0,
    if counts w = ![0, 0, 3] then 1
      else if counts w = ![2, 0, 1] ∨ counts w = ![0, 2, 1] then 2 else 0,
    if counts w = ![2, 0, 1] then 1 else if counts w = ![0, 2, 1] then -1 else 0,
    if counts w = ![1, 1, 1] then 1 else 0] k

private def gramWeight (k : Fin 7) : ℝ := ![4, 2, 4, 2, 3, 8, 4] k / 471

private def witness (w : Word (Fin 3) 3) : ℝ :=
  if counts w = ![2, 1, 0] ∨ counts w = ![1, 2, 0] then 1 / 3
  else if counts w = ![0, 0, 3] then 1
  else if counts w = ![1, 1, 1] then -1 / 2
  else 0

private theorem counts_three (w : Word (Fin 3) 3) (j : Fin 3) :
    counts w j = (if w 0 = j then 1 else 0) + (if w 1 = j then 1 else 0) +
      (if w 2 = j then 1 else 0) := by
  change (occupation w).count j = _
  simpa only [occupation, Multiset.coe_count, Fin.sum_univ_three] using count_ofFn w j

private theorem sum_words (f : Word (Fin 3) 3 → ℝ) :
    ∑ w, f w = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f ![a, b, c] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ w : Fin 2 → Fin 3, f (Fin.cons a w)) = _
  rw [← (Fin.consEquiv (fun _ : Fin 2 => Fin 3)).sum_comp
    (fun w => f (Fin.cons a w)), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ w : Fin 1 → Fin 3, f (Fin.cons a (Fin.cons b w))) = _
  rw [← (Fin.consEquiv (fun _ : Fin 1 => Fin 3)).sum_comp
    (fun w => f (Fin.cons a (Fin.cons b w))), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ w : Fin 0 → Fin 3, f (Fin.cons a (Fin.cons b (Fin.cons c w)))) = _
  simp only [Fintype.sum_unique]
  rfl

private theorem counts_classes (w : Word (Fin 3) 3) :
    counts w = ![3, 0, 0] ∨ counts w = ![1, 2, 0] ∨ counts w = ![1, 0, 2] ∨
    counts w = ![0, 3, 0] ∨ counts w = ![2, 1, 0] ∨ counts w = ![0, 1, 2] ∨
    counts w = ![0, 0, 3] ∨ counts w = ![2, 0, 1] ∨ counts w = ![0, 2, 1] ∨
    counts w = ![1, 1, 1] := by
  have he : w = ![w 0, w 1, w 2] := by ext i; fin_cases i <;> rfl
  rw [he]
  generalize w 0 = a, w 1 = b, w 2 = c
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    norm_num [funext_iff, counts_three, Fin.forall_fin_succ]

private theorem state_cs : IsCompletelySymmetric state := by
  intro π a b
  have hc : (fun j => counts (fun k => Sum.elim a b (π (Sum.inl k))) j +
      counts (fun k => Sum.elim a b (π (Sum.inr k))) j) =
      (fun j => counts a j + counts b j) := by
    funext j
    change (occupation (fun k => Sum.elim a b (π (Sum.inl k)))).count j +
        (occupation (fun k => Sum.elim a b (π (Sum.inr k)))).count j =
      (occupation a).count j + (occupation b).count j
    simp only [occupation, Multiset.coe_count, count_ofFn]
    let f : Fin 3 ⊕ Fin 3 → ℕ := fun k => if Sum.elim a b k = j then 1 else 0
    calc
      _ = ∑ k : Fin 3 ⊕ Fin 3, f (π k) := by rw [Fintype.sum_sum_type]
      _ = ∑ k : Fin 3 ⊕ Fin 3, f k := Equiv.sum_comp π f
      _ = _ := by rw [Fintype.sum_sum_type]; rfl
  change ((moment _ / 471 : ℝ) : ℂ) = ((moment _ / 471 : ℝ) : ℂ)
  rw [hc]

set_option maxHeartbeats 4000000 in
-- The Gram identity checks the hundred pairs of occupation classes.
private theorem gram_factor : state =
    ∑ k : Fin 7, (gramWeight k : ℂ) • vecMulVec (gramVector k) (star (gramVector k)) := by
  ext a b
  rcases counts_classes a with ha | ha | ha | ha | ha | ha | ha | ha | ha | ha <;>
    rcases counts_classes b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;>
    (delta state moment gramWeight gramVector
     norm_num [ha, hb, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ,
       Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
       smul_eq_mul, map_ofNat])

private theorem state_psd : state.PosSemidef := by
  rw [gram_factor]
  have hp (k : Fin 7) :
      ((gramWeight k : ℂ) • vecMulVec (gramVector k) (star (gramVector k))).PosSemidef := by
    apply (Matrix.posSemidef_vecMulVec_self_star (gramVector k)).smul
    have hw : 0 ≤ gramWeight k := by
      delta gramWeight
      fin_cases k <;> norm_num
    exact_mod_cast hw
  exact Matrix.posSemidef_sum _ (fun k _ => hp k)

private theorem state_trace : trace state = 1 := by
  apply Complex.ext
  · change (∑ w, state w w).re = 1
    rw [Complex.re_sum, sum_words]
    delta state moment
    norm_num [Fin.sum_univ_three, counts_three, funext_iff,
      Fin.forall_fin_succ]
  · change (∑ w, state w w).im = 0
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro w _
    exact Complex.ofReal_im _

private theorem decomposition_support (n : ℕ) (wt : Fin n → ℝ)
    (ψ : Fin n → Word (Fin 3) 3 → ℂ) (hwt : ∀ i, 0 < wt i)
    (he : state = ∑ i, (wt i : ℂ) • vecMulVec (ψ i) (star (ψ i))) :
    ∀ i a b, counts a = counts b → ψ i a = ψ i b := by
  intro i a b hab
  have hentry (x y : Word (Fin 3) 3) :
      state x y = ∑ j, (wt j : ℂ) * (ψ j x * star (ψ j y)) := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Pi.star_apply] using
      congrArg (fun m : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ => m x y) he
  have hzero : state a a + state b b - state a b - state b a = 0 := by
    change ((moment _ / 471 : ℝ) : ℂ) + ((moment _ / 471 : ℝ) : ℂ) -
      ((moment _ / 471 : ℝ) : ℂ) - ((moment _ / 471 : ℝ) : ℂ) = 0
    rw [hab]
    ring
  have hz : (∑ j, wt j * Complex.normSq (ψ j a - ψ j b)) = 0 := by
    calc
      _ = (state a a + state b b - state a b - state b a).re := by
        rw [hentry a a, hentry b b, hentry a b, hentry b a]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Complex.normSq_sub, Complex.add_re, Complex.sub_re,
          Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
      _ = 0 := by rw [hzero]; rfl
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hwt j).le (Complex.normSq_nonneg _))).mp hz i (Finset.mem_univ i)
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp
    ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hwt i))))

private theorem symmetric_product_power (v : Fin 3 → Fin 3 → ℂ)
    (hs : ∀ a b, counts a = counts b →
      piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v a =
        piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v b) :
    ∃ (c : ℂ) (x : Fin 3 → ℂ),
      ∀ w, piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v w = c * ∏ k : Fin 3, x (w k) := by
  classical
  by_cases hz : ∀ w, piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v w = 0
  · refine ⟨0, fun _ => 0, ?_⟩
    intro w
    rw [hz w, zero_mul]
  obtain ⟨w, hw⟩ := not_forall.mp hz
  have hp : piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v w =
      v 0 (w 0) * v 1 (w 1) * v 2 (w 2) := by
    change (∏ k : Fin 3, v k (w k)) = _
    exact Fin.prod_univ_three _
  rw [hp] at hw
  have h0 : v 0 (w 0) ≠ 0 := fun h => hw (by rw [h, zero_mul, zero_mul])
  have h1 : v 1 (w 1) ≠ 0 := fun h => hw (by rw [h, mul_zero, zero_mul])
  have h2 : v 2 (w 2) ≠ 0 := fun h => hw (by rw [h, mul_zero])
  have hs01 (a b c : Fin 3) :
      v 0 a * v 1 b * v 2 c = v 0 b * v 1 a * v 2 c := by
    have hc : counts ![a, b, c] = counts ![b, a, c] := by
      funext j
      rw [counts_three, counts_three]
      change (if a = j then 1 else 0) + (if b = j then 1 else 0) +
          (if c = j then 1 else 0) =
        (if b = j then 1 else 0) + (if a = j then 1 else 0) +
          (if c = j then 1 else 0)
      omega
    have h := hs _ _ hc
    simpa only [piFamily_apply, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hs02 (a b c : Fin 3) :
      v 0 a * v 1 b * v 2 c = v 0 c * v 1 b * v 2 a := by
    have hc : counts ![a, b, c] = counts ![c, b, a] := by
      funext j
      rw [counts_three, counts_three]
      change (if a = j then 1 else 0) + (if b = j then 1 else 0) +
          (if c = j then 1 else 0) =
        (if c = j then 1 else 0) + (if b = j then 1 else 0) +
          (if a = j then 1 else 0)
      omega
    have h := hs _ _ hc
    simpa only [piFamily_apply, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using h
  have hb (z : Fin 3) : v 1 z = (v 1 (w 0) / v 0 (w 0)) * v 0 z := by
    have h := mul_right_cancel₀ h2 (hs01 (w 0) z (w 2))
    apply mul_left_cancel₀ h0
    calc
      v 0 (w 0) * v 1 z = v 0 z * v 1 (w 0) := h
      _ = v 0 (w 0) * (v 1 (w 0) / v 0 (w 0) * v 0 z) := by
        rw [← mul_assoc, mul_div_cancel₀ _ h0, mul_comm]
  have hc (z : Fin 3) : v 2 z = (v 2 (w 0) / v 0 (w 0)) * v 0 z := by
    have h : v 0 (w 0) * v 2 z = v 0 z * v 2 (w 0) := by
      apply mul_left_cancel₀ h1
      calc
        v 1 (w 1) * (v 0 (w 0) * v 2 z) = v 0 (w 0) * v 1 (w 1) * v 2 z := by
          ring
        _ = v 0 z * v 1 (w 1) * v 2 (w 0) := hs02 (w 0) (w 1) z
        _ = v 1 (w 1) * (v 0 z * v 2 (w 0)) := by ring
    apply mul_left_cancel₀ h0
    calc
      v 0 (w 0) * v 2 z = v 0 z * v 2 (w 0) := h
      _ = v 0 (w 0) * (v 2 (w 0) / v 0 (w 0) * v 0 z) := by
        rw [← mul_assoc, mul_div_cancel₀ _ h0, mul_comm]
  refine ⟨(v 1 (w 0) / v 0 (w 0)) * (v 2 (w 0) / v 0 (w 0)), v 0, ?_⟩
  intro q
  change (∏ k : Fin 3, v k (q k)) = _
  rw [Fin.prod_univ_three, Fin.prod_univ_three, hb, hc]
  ring

private theorem motzkin_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ a ^ 2 * b + a * b ^ 2 + c ^ 3 - 3 * a * b * c := by
  have hp : 0 ≤ a ^ 2 * b := mul_nonneg (sq_nonneg a) hb
  have hq : 0 ≤ a * b ^ 2 := mul_nonneg ha (sq_nonneg b)
  have hr : 0 ≤ c ^ 3 := pow_nonneg hc 3
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hp hq hr (by norm_num)
  rw [← Real.mul_rpow hp hq, ← Real.mul_rpow (mul_nonneg hp hq) hr] at h
  rw [show (a ^ 2 * b) * (a * b ^ 2) * c ^ 3 = (a * b * c) ^ 3 by ring,
    ← Real.rpow_natCast_mul (mul_nonneg (mul_nonneg ha hb) hc)] at h
  norm_num at h
  linarith

private theorem power_witness_nonneg (c : ℂ) (x : Fin 3 → ℂ) :
    0 ≤ ∑ w : Word (Fin 3) 3,
      witness w * Complex.normSq (c * ∏ k : Fin 3, x (w k)) := by
  have he : (∑ w : Word (Fin 3) 3,
      witness w * Complex.normSq (c * ∏ k : Fin 3, x (w k))) =
      Complex.normSq c * (Complex.normSq (x 0) ^ 2 * Complex.normSq (x 1) +
        Complex.normSq (x 0) * Complex.normSq (x 1) ^ 2 + Complex.normSq (x 2) ^ 3 -
        3 * Complex.normSq (x 0) * Complex.normSq (x 1) * Complex.normSq (x 2)) := by
    rw [sum_words]
    delta witness
    norm_num [Fin.sum_univ_three, Fin.prod_univ_three, counts_three,
      funext_iff, Fin.forall_fin_succ, Complex.normSq_mul]
    ring
  rw [he]
  exact mul_nonneg (Complex.normSq_nonneg c) (motzkin_nonneg _ _ _
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))

private theorem symmetric_product_witness_nonneg (v : Fin 3 → Fin 3 → ℂ)
    (hs : ∀ a b, counts a = counts b →
      piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v a =
        piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v b) :
    0 ≤ ∑ w : Word (Fin 3) 3, witness w *
      Complex.normSq (piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) v w) := by
  obtain ⟨c, x, hx⟩ := symmetric_product_power v hs
  simp_rw [hx]
  exact power_witness_nonneg c x

private theorem state_witness_value :
    (∑ w : Word (Fin 3) 3, witness w * (state w w).re) = -1 / 471 := by
  rw [sum_words]
  delta witness state moment
  norm_num [Fin.sum_univ_three, counts_three,
    funext_iff, Fin.forall_fin_succ]

private theorem state_entangled : ¬ IsFullySeparable state := by
  intro h
  obtain ⟨n, wt, v, hwt, _, _, he⟩ := h
  have hs := decomposition_support n wt
    (fun i => piFamily (R := ℂ) (M := fun (_ : Fin 3) (_ : Fin 3) => ℂ)
      (N := fun _ => ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) (v i)) hwt he
  have hp (i : Fin n) := symmetric_product_witness_nonneg (v i) (hs i)
  have hd (w : Word (Fin 3) 3) :
      (state w w).re = ∑ i, wt i *
        Complex.normSq (piFamily (R := ℂ) (fun _ => .mkPiAlgebra ℂ (Fin 3) ℂ) (v i) w) := by
    have hew := congrArg
      (fun m : Matrix (Word (Fin 3) 3) (Word (Fin 3) 3) ℂ => m w w) he
    rw [hew]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Pi.star_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul, Complex.ofReal_re]
  have hn : 0 ≤ ∑ w : Word (Fin 3) 3, witness w * (state w w).re := by
    simp_rw [hd, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro i _
    have h := mul_nonneg (hwt i).le (hp i)
    simpa only [Finset.mul_sum, mul_assoc, mul_left_comm (wt i)] using h
  rw [state_witness_value] at hn
  norm_num at hn

/-- A completely symmetric three-qutrit state refutes the universal claim. -/
theorem result : ¬ claim := by
  intro h
  exact state_entangled (h 3 (by decide) state ⟨state_psd, state_trace⟩ state_cs)

end D5.S3.Quantum.Entanglement.Witness.ThreeQutritCompletelySymmetricEntangled
