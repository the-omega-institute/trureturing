/- GID: D5/S3/Quantum/Recovery/PetzWeightedHessianOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzWeightedHessianOptimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The weighted trace-norm quotient on the full Hermitian fibre has a unique maximizer. -/


import D5.S3.Quantum.Recovery.PetzProjectedHessian
import D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality
import D5.S3.Quantum.Recovery.PetzTwoFlagContraction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Sharp trace-norm optimization in diagonal Hessian coordinates. -/


noncomputable section

set_option autoImplicit false

namespace D5.S3.Quantum.Recovery.PetzWeightedHessianOptimum

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U traceNorm_nonneg)
open D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality (exists_hermitian_traceNorm_test)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Recovery.PetzProjectedHessian

/-- The full Hermitian fibre with zero retained marginal. -/
def fibre : Set Joint := {Z | Z.IsHermitian ∧ partialTraceRight Z = 0}

def partner (i : Slot) : Slot := (1 - i.1, i.2)

/-- Two real within-flag swaps, with upper and lower entries equal. -/
def swaps (a b : ℝ) : Joint := fun i j =>
  if j = partner i then (if i.2 = 0 then a else b : ℝ) else 0

/-- The fixed Hermitian offset in the quotient. -/
def offset (f g : ℝ) : Joint := swaps (-f / 2) (g / 2)

/-- The unique maximizing tangent. -/
def optimizer (m C f g : ℝ) : Joint := swaps (-(4 * C * m / (f + g))) (4 * C * m / (f + g))

/-- The margin at flag `s` for the indicated offset amplitude. -/
def margin (β : Slot → ℝ) (m C f g : ℝ) (s : Fin 2) : ℝ :=
  8 * m + (if s = 0 then f else g) * (f + g) / C - 2 * (β (0, s) + β (1, s))

private theorem partner_involution : Function.Involutive partner := by
  rintro ⟨b, s⟩
  fin_cases b <;> simp only [partner, Prod.mk.injEq, and_true] <;> decide

private theorem partner_eq_iff {i j : Slot} : j = partner i ↔ i = partner j := by
  constructor
  · rintro rfl
    exact (partner_involution i).symm
  · rintro rfl
    exact (partner_involution j).symm

private theorem swaps_hermitian (a b : ℝ) : (swaps a b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases h : j = partner i
  · subst j
    have hi := partner_involution i
    have ht : (partner i).2 = i.2 := rfl
    simp only [swaps, hi, ht, ite_true, Complex.star_def, Complex.conj_ofReal]
  · have h' := (not_congr partner_eq_iff).mp h
    simp [swaps, h, h']

private theorem swap_trace_zero (a : ℝ) : partialTraceRight (swaps (-a) a) = 0 := by
  ext i j
  by_cases h : j = 1 - i <;> simp [partialTraceRight, Fin.sum_univ_two, swaps, partner, h]

private theorem trace_swaps (Y : Joint) (hY : Y.IsHermitian) (a b : ℝ) :
    (Y * swaps a b).trace.re =
      2 * (a * (Y (0, 0) (1, 0)).re + b * (Y (0, 1) (1, 1)).re) := by
  have hr (s : Fin 2) : (Y (1, s) (0, s)).re = (Y (0, s) (1, s)).re := by
    rw [← hY.apply (1, s) (0, s)]
    exact Complex.conj_re _
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    swaps, partner, Complex.mul_re, hr]
  ring

private theorem energy_nonneg (w : Weights) (hw : ∀ i j, 0 < w i j) (Z : Joint) :
    0 ≤ energy w Z :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (Complex.normSq_nonneg _) (hw i j).le

private theorem energy_eq_zero (w : Weights) (hw : ∀ i j, 0 < w i j) {Z : Joint}
    (h : energy w Z = 0) : Z = 0 := by
  have hn (i j : Slot) : 0 ≤ Complex.normSq (Z i j) / w i j :=
    div_nonneg (Complex.normSq_nonneg _) (hw i j).le
  ext i j
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => hn i j).mp h i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn i j).mp hi j (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp ((div_eq_zero_iff.mp hj).resolve_right (hw i j).ne')

private theorem pairing_smul (w : Weights) (r : ℝ) (V Z : Joint) :
    pairing w ((r : ℂ) • V) Z = r * pairing w V Z := by
  simp only [pairing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem pairing_self (w : Weights) (Z : Joint) : pairing w Z Z = energy w Z := by
  unfold pairing energy
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

private theorem energy_sub_smul (w : Weights) (V Z : Joint) (r : ℝ) :
    energy w (V - (r : ℂ) • Z) = energy w V - 2 * r * pairing w V Z + r ^ 2 * energy w Z := by
  simp only [energy, pairing, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- Completion of squares in the direct sum of the weighted matrix space and a scalar. -/
private theorem quotient_le_dual (w : Weights) (hw : ∀ i j, 0 < w i j)
    (V Z : Joint) (C o : ℝ) (hC : 0 < C) :
    let D := C + energy w Z / 2
    let b := pairing w V Z
    (b + o) ^ 2 / D ≤ 2 * energy w V + o ^ 2 / C ∧
      ((b + o) ^ 2 / D = 2 * energy w V + o ^ 2 / C ↔ V = ((o / (2 * C) : ℝ) : ℂ) • Z) := by
  dsimp only
  set D := C + energy w Z / 2
  set b := pairing w V Z
  set t := (b + o) / D
  have hD : 0 < D := by dsimp [D]; linarith [energy_nonneg w hw Z]
  have ht : D * t = b + o := by dsimp [t]; field_simp
  have hsq :
      2 * energy w (V - ((t / 2 : ℝ) : ℂ) • Z) + (o - C * t) ^ 2 / C =
        2 * energy w V + o ^ 2 / C - (b + o) ^ 2 / D := by
    rw [energy_sub_smul]
    change 2 * (energy w V - 2 * (t / 2) * b + (t / 2) ^ 2 * energy w Z) +
      (o - C * t) ^ 2 / C = 2 * energy w V + o ^ 2 / C - (b + o) ^ 2 / D
    rw [show (b + o) ^ 2 / D = t * (b + o) by dsimp [t]; ring]
    have hpoly := congrArg (fun r : ℝ => t * r) ht
    change t * ((C + energy w Z / 2) * t) = t * (b + o) at hpoly
    have hc : (o - C * t) ^ 2 / C = o ^ 2 / C - 2 * o * t + C * t ^ 2 := by
      field_simp [hC.ne']
      ring
    rw [hc]
    linarith only [show (C + energy w Z / 2) * t ^ 2 = t * (b + o) by
      linear_combination hpoly]
  have hfirst := energy_nonneg w hw (V - ((t / 2 : ℝ) : ℂ) • Z)
  have hsecond : 0 ≤ (o - C * t) ^ 2 / C := by positivity
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    have hzero : energy w (V - ((t / 2 : ℝ) : ℂ) • Z) = 0 := by linarith
    have hval : (o - C * t) ^ 2 / C = 0 := by linarith
    have hval' := (div_eq_zero_iff.mp hval).resolve_right hC.ne'
    have ht' : t / 2 = o / (2 * C) := by
      have heq := sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hval')
      field_simp [hC.ne']
      linarith
    rw [← ht']
    exact sub_eq_zero.mp (energy_eq_zero w hw hzero)
  · intro hv
    have hb : b = o / (2 * C) * energy w Z := by
      change pairing w V Z = _
      rw [hv, pairing_smul, pairing_self]
    have htt : t = o / C := by
      change (b + o) / (C + energy w Z / 2) = o / C
      rw [hb]
      apply (div_eq_iff hD.ne').2
      field_simp [hC.ne']
      ring
    have hcoef : t / 2 = o / (2 * C) := by rw [htt]; ring
    have hVzero : V - ((t / 2 : ℝ) : ℂ) • Z = 0 :=
      sub_eq_zero.mpr (by rwa [hcoef])
    have hscalar : o - C * t = 0 := by rw [htt]; field_simp; ring
    have henergy : energy w 0 = 0 := by simp [energy]
    rw [hVzero, hscalar, henergy, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero, add_zero] at hsq
    exact (sub_eq_zero.mp hsq.symm).symm

private theorem normSq_symm (Y : Joint) (hY : Y.IsHermitian) (i j : Slot) :
    Complex.normSq (Y i j) = Complex.normSq (Y j i) := by
  rw [← hY.apply i j]
  exact Complex.normSq_conj _

private theorem reduced_energy_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (y z : ℂ) :
    a * b / (a + b) * Complex.normSq (y - z) ≤ a * Complex.normSq y + b * Complex.normSq z := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (add_pos ha hb)]
  have h := Complex.normSq_nonneg ((a : ℂ) * y + (b : ℂ) * z)
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero] at h ⊢
  linarith only [h]

private def rest (a : Weights) (Y : Joint) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase (partner i), a i j * Complex.normSq (Y i j)

private theorem rest_as_sum (a : Weights) (Y : Joint) :
    rest a Y = ∑ i, ∑ j, if j = partner i then 0 else a i j * Complex.normSq (Y i j) := by
  unfold rest
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.filter_ne' Finset.univ (partner i), Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by by_cases h : j = partner i <;> simp [h]

private theorem representative_energy_le (w : Weights) (Y : Joint)
    (hw : ∀ i j, 0 < w i j) (hs : ∀ i j, w i j = w j i) (hY : Y.IsHermitian) :
    energy w (representative w Y) ≤ rest w Y + 2 * reducedWeight w 0 1 *
      Complex.normSq (Y (0, 0) (1, 0) - Y (0, 1) (1, 1)) := by
  have hsym : reducedWeight w 1 0 = reducedWeight w 0 1 := by
    unfold reducedWeight
    rw [hs (1, 0) (0, 0), hs (1, 1) (0, 1)]
  have hconj : Complex.normSq (Y (1, 0) (0, 0) - Y (1, 1) (0, 1)) =
      Complex.normSq (Y (0, 0) (1, 0) - Y (0, 1) (1, 1)) := by
    rw [← hY.apply (1, 0) (0, 0), ← hY.apply (1, 1) (0, 1), ← star_sub]
    exact Complex.normSq_conj _
  rw [(representative_spec w Y hw hs hY).2.2.2, rest_as_sum]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, hsym, hconj]
  simp only [partner, show (1 : Fin 2) - 0 = 1 by decide, show (1 : Fin 2) - 1 = 0 by decide,
    Prod.mk.injEq, false_and, and_false, show (0 : Fin 2) ≠ 1 by decide,
    show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false, add_zero, zero_add]
  have han (b : Fin 2) := reduced_energy_le (w (b, 0) (b, 0)) (w (b, 1) (b, 1))
    (hw _ _) (hw _ _) (Y (b, 0) (b, 0)) (Y (b, 1) (b, 1))
  have h₀ : reducedWeight w 0 0 * Complex.normSq (Y (0, 0) (0, 0) - Y (0, 1) (0, 1)) ≤ _ :=
    han 0
  have h₁ : reducedWeight w 1 1 * Complex.normSq (Y (1, 0) (1, 0) - Y (1, 1) (1, 1)) ≤ _ :=
    han 1
  linarith only [h₀, h₁]

private theorem rest_le_rows (w : Weights) (β : Slot → ℝ) (Y : Joint) (hY : Y.IsHermitian)
    (hβ : ∀ i j, j ≠ partner i → w i j ≤ (β i + β j) / 2) :
    2 * rest w Y ≤
      ∑ i, (2 * β i) * ∑ j ∈ Finset.univ.erase (partner i), Complex.normSq (Y i j) := by
  have hsum : rest w Y ≤ rest (fun i j => (β i + β j) / 2) Y := by
    unfold rest
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right (hβ i j (Finset.mem_erase.mp hj).1) (Complex.normSq_nonneg _)
  have hflip : rest (fun _ j => β j) Y = rest (fun i _ => β i) Y := by
    rw [rest_as_sum, rest_as_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [normSq_symm Y hY j i]
    by_cases h : j = partner i
    · simp [h, partner_involution i]
    · simp [h, (not_congr partner_eq_iff).mp h]
  have havg : 2 * rest (fun i j => (β i + β j) / 2) Y =
      rest (fun i _ => β i) Y + rest (fun _ j => β j) Y := by
    simp only [rest, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hrow : 2 * rest (fun i _ => β i) Y =
      ∑ i, (2 * β i) * ∑ j ∈ Finset.univ.erase (partner i), Complex.normSq (Y i j) := by
    simp only [rest, Finset.mul_sum, mul_assoc]
  linarith

private theorem square_le_one (Y : Joint) (hY : Y.IsHermitian) (hn : ‖Y‖ ≤ 1) :
    (1 - Y * Y).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply sub_nonneg.mpr
  have hh : star Y * Y ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg Y)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg Y]
  simpa only [hY.star_eq] using hh

private theorem corners_force_swaps (Y : Joint) (hY : Y.IsHermitian)
    (hY₂ : (1 - Y * Y).PosSemidef) (a b : ℝ)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h₀ : Y (0, 0) (1, 0) = (a : ℂ)) (h₁ : Y (0, 1) (1, 1) = (b : ℂ)) :
    Y = swaps a b := by
  have hentry (i : Slot) : Y i (partner i) = (if i.2 = 0 then a else b : ℝ) := by
    obtain ⟨r, s⟩ := i
    have h₀' : Y (1, 0) (0, 0) = (a : ℂ) := by
      rw [← hY.apply (1, 0) (0, 0), h₀, Complex.star_def, Complex.conj_ofReal]
    have h₁' : Y (1, 1) (0, 1) = (b : ℂ) := by
      rw [← hY.apply (1, 1) (0, 1), h₁, Complex.star_def, Complex.conj_ofReal]
    fin_cases r <;> fin_cases s <;> first | exact h₀ | exact h₁ | exact h₀' | exact h₁'
  have hmag (i : Slot) : Complex.normSq (Y i (partner i)) = 1 := by
    rw [hentry, Complex.normSq_ofReal]
    split
    · simpa [pow_two] using ha
    · simpa [pow_two] using hb
  have hrow (i : Slot) : ∑ j, Complex.normSq (Y i j) ≤ 1 := by
    have hdiag := (Complex.nonneg_iff.mp (hY₂.diag_nonneg (i := i))).1
    have hsum : ((Y * Y) i i).re = ∑ j, Complex.normSq (Y i j) := by
      rw [Matrix.mul_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hY.apply j i]
      simp [Complex.mul_conj]
    simpa [Matrix.sub_apply, Complex.sub_re, hsum] using hdiag
  ext i j
  by_cases h : j = partner i
  · subst j
    simpa [swaps] using hentry i
  · have hr := hrow i
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (partner i)), hmag] at hr
    have hnonneg (k : Slot) : 0 ≤ Complex.normSq (Y i k) := Complex.normSq_nonneg _
    have hzero : ∑ k ∈ Finset.univ.erase (partner i), Complex.normSq (Y i k) = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun k _ => hnonneg k)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hnonneg k).mp hzero j
      (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)
    simpa [swaps, h] using Complex.normSq_eq_zero.mp hj

private theorem swaps_square (a b : ℝ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    swaps a b * swaps a b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner i)]
  · simp only [swaps, ite_true, partner_involution i]
    by_cases h : j = i
    · subst j
      rw [ite_eq_left rfl, Matrix.one_apply_eq]
      have hi : (partner i).2 = i.2 := rfl
      rw [hi, ← Complex.ofReal_mul]
      split <;> first
        | simpa [pow_two] using congrArg Complex.ofReal ha
        | simpa [pow_two] using congrArg Complex.ofReal hb
    · simp [h, Ne.symm h]
  · intro k _ hk
    simp [swaps, hk]
  · simp

private theorem representative_swaps (w : Weights) (hs : ∀ i j, w i j = w j i)
    (a b : ℝ) :
    representative w (swaps a b) =
      swaps (reducedWeight w 0 1 * (a - b)) (-(reducedWeight w 0 1 * (a - b))) := by
  have hm : reducedWeight w 1 0 = reducedWeight w 0 1 := by
    unfold reducedWeight
    rw [hs (1, 0) (0, 0), hs (1, 1) (0, 1)]
  ext ⟨i,s⟩ ⟨j,t⟩
  fin_cases i <;> fin_cases s <;> fin_cases j <;> fin_cases t <;>
    simp [representative, swaps, partner, hm]

private theorem swaps_smul (r a b : ℝ) :
    (r : ℂ) • swaps a b = swaps (r * a) (r * b) := by
  ext i j
  by_cases h : j = partner i <;> by_cases hs : i.2 = 0 <;>
    simp [Matrix.smul_apply, smul_eq_mul, swaps, h, hs]

private theorem swaps_entries (a b : ℝ) :
    swaps a b (0, 0) (1, 0) = (a : ℂ) ∧ swaps a b (0, 1) (1, 1) = (b : ℂ) := by
  constructor <;> rfl

private theorem dual_bound (w : Weights) (β : Slot → ℝ) (C f g : ℝ) (Y : Joint)
    (hw : ∀ i j, 0 < w i j) (hs : ∀ i j, w i j = w j i)
    (hβ : ∀ i, 0 ≤ β i) (hmean : ∀ i j, j ≠ partner i → w i j ≤ (β i + β j) / 2)
    (hC : 0 < C) (hf : 0 < f) (hg : 0 < g)
    (h₀ : 0 ≤ margin β (reducedWeight w 0 1) C f g 0)
    (h₁ : 0 ≤ margin β (reducedWeight w 0 1) C f g 1)
    (hstrict : 0 < margin β (reducedWeight w 0 1) C f g 0 +
      margin β (reducedWeight w 0 1) C f g 1)
    (hY : Y.IsHermitian) (hY₂ : (1 - Y * Y).PosSemidef) :
    let m := reducedWeight w 0 1
    let dual := 2 * energy w (representative w Y) + (Y * offset f g).trace.re ^ 2 / C
    let opt := 16 * m + (f + g) ^ 2 / C
    dual ≤ opt ∧ (dual = opt → Y = swaps (-1) 1 ∨ Y = swaps 1 (-1)) := by
  dsimp only
  set m := reducedWeight w 0 1
  have hm : 0 ≤ m := by
    dsimp [m, reducedWeight]
    exact div_nonneg (mul_nonneg (hw _ _).le (hw _ _).le) (add_pos (hw _ _) (hw _ _)).le
  have he := representative_energy_le w Y hw hs hY
  have hr := rest_le_rows w β Y hY hmean
  have hv (s : Fin 2) : 2 * β (0, s) + 2 * β (1, s) = 2 * (β (0, s) + β (1, s)) := by ring
  obtain ⟨hb, hc⟩ :=
    PetzTwoFlagContraction.matrix_twoFlag_maximum Y (fun i => 2 * β i) m C f g hY hY₂
      (fun i => mul_nonneg (by norm_num) (hβ i)) hm hC hf hg
      (by simpa [margin, hv] using h₀) (by simpa [margin, hv] using h₁)
      (by simpa [margin, hv] using hstrict)
  change (∑ i, 2 * β i * ∑ j ∈ Finset.univ.erase (partner i), Complex.normSq (Y i j)) +
    4 * m * Complex.normSq (Y (0, 0) (1, 0) - Y (0, 1) (1, 1)) +
    (f * (Y (0, 0) (1, 0)).re - g * (Y (0, 1) (1, 1)).re) ^ 2 / C ≤ _ at hb
  have ho : (Y * offset f g).trace.re ^ 2 / C =
      (f * (Y (0, 0) (1, 0)).re - g * (Y (0, 1) (1, 1)).re) ^ 2 / C := by
    rw [offset, trace_swaps Y hY]
    congr 1
    ring
  rw [ho]
  refine ⟨by linarith only [he, hr, hb], ?_⟩
  intro h
  unfold partner at hr
  unfold partner at hb
  have hsaturation := hc.mp (by linarith only [he, hr, hb, h])
  rcases hsaturation with ⟨hp, hn⟩ | ⟨hn, hp⟩
  · exact Or.inr (corners_force_swaps Y hY hY₂ 1 (-1) (by norm_num) (by norm_num)
      (by simpa using hp) (by simpa using hn))
  · exact Or.inl (corners_force_swaps Y hY hY₂ (-1) 1 (by norm_num) (by norm_num)
      (by simpa using hn) (by simpa using hp))

private theorem corner_offset (f g : ℝ) :
    (swaps (-1) 1 * offset f g).trace.re = f + g ∧
    (swaps 1 (-1) * offset f g).trace.re = -(f + g) := by
  constructor <;> rw [offset, trace_swaps _ (swaps_hermitian _ _)] <;>
    simp only [(swaps_entries _ _).1, (swaps_entries _ _).2, Complex.ofReal_re] <;> ring

private theorem corner_representative (w : Weights) (hs : ∀ i j, w i j = w j i)
    (C f g : ℝ) (hC : 0 < C) (hF : 0 < f + g) :
    let m := reducedWeight w 0 1
    representative w (swaps (-1) 1) = (((f + g) / (2 * C) : ℝ) : ℂ) • optimizer m C f g ∧
    representative w (swaps 1 (-1)) = ((-(f + g) / (2 * C) : ℝ) : ℂ) • optimizer m C f g := by
  dsimp only
  constructor <;> rw [representative_swaps w hs, optimizer, swaps_smul] <;>
    congr 1 <;> field_simp [hC.ne', hF.ne'] <;> ring

private theorem corner_energy (w : Weights) (hw : ∀ i j, 0 < w i j) (hs : ∀ i j, w i j = w j i) :
    energy w (representative w (swaps (-1) 1)) = 8 * reducedWeight w 0 1 := by
  rw [(representative_spec w _ hw hs (swaps_hermitian (-1) 1)).2.2.2]
  have hr : reducedWeight w 1 0 = reducedWeight w 0 1 := by
    unfold reducedWeight
    rw [hs (1, 0) (0, 0), hs (1, 1) (0, 1)]
  simp only [Fin.sum_univ_two, hr]
  simp [swaps, partner, Complex.normSq_apply]
  ring

/-- The weighted Hessian quotient attains its sharp value on the full Hermitian
partial-trace-zero fibre, and its unique optimizer is the indicated pair of swaps. -/
theorem weighted_hessian_maximum (w : Weights) (β : Slot → ℝ) (C f g : ℝ)
    (hw : ∀ i j, 0 < w i j) (hs : ∀ i j, w i j = w j i)
    (hβ : ∀ i, 0 ≤ β i) (hmean : ∀ i j, j ≠ partner i → w i j ≤ (β i + β j) / 2)
    (hC : 0 < C) (hf : 0 < f) (hg : 0 < g)
    (h₀ : 0 ≤ margin β (reducedWeight w 0 1) C f g 0)
    (h₁ : 0 ≤ margin β (reducedWeight w 0 1) C f g 1)
    (hstrict : 0 < margin β (reducedWeight w 0 1) C f g 0 +
      margin β (reducedWeight w 0 1) C f g 1) :
    let m := reducedWeight w 0 1
    let ratio (Z : Joint) := traceNorm (Z + offset f g) ^ 2 / (C + energy w Z / 2)
    let opt := 16 * m + (f + g) ^ 2 / C
    IsGreatest (ratio '' fibre) opt ∧
      ∀ Z ∈ fibre, ratio Z = opt ↔ Z = optimizer m C f g := by
  dsimp only
  set m := reducedWeight w 0 1
  set F := f + g
  set opt := 16 * m + F ^ 2 / C
  set Z₀ := optimizer m C f g
  let ratio (Z : Joint) := traceNorm (Z + offset f g) ^ 2 / (C + energy w Z / 2)
  change IsGreatest (ratio '' fibre) opt ∧ ∀ Z ∈ fibre, ratio Z = opt ↔ Z = Z₀
  have hF : 0 < F := add_pos hf hg
  have hZ₀ : Z₀ ∈ fibre := ⟨swaps_hermitian _ _, swap_trace_zero _⟩
  have hbound (Z : Joint) (hZ : Z ∈ fibre) : ratio Z ≤ opt ∧ (ratio Z = opt → Z = Z₀) := by
    obtain ⟨Y, hY, hn, htest⟩ :=
      exists_hermitian_traceNorm_test (Z + offset f g) (hZ.1.add (swaps_hermitian _ _))
    set V := representative w Y
    set o := (Y * offset f g).trace.re
    have htrace : pairing w V Z + o = traceNorm (Z + offset f g) := by
      rw [← htest, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
        (representative_spec w Y hw hs hY).2.2.1 Z hZ.2]
    obtain ⟨hle, heq⟩ := quotient_le_dual w hw V Z C o hC
    rw [htrace] at hle heq
    obtain ⟨hdual, hcorners⟩ :=
      dual_bound w β C f g Y hw hs hβ hmean hC hf hg h₀ h₁ hstrict hY (square_le_one Y hY hn)
    change 2 * energy w V + o ^ 2 / C ≤ opt at hdual
    change ratio Z ≤ 2 * energy w V + o ^ 2 / C at hle
    refine ⟨hle.trans hdual, ?_⟩
    intro hz
    have hdual' : 2 * energy w V + o ^ 2 / C = opt := le_antisymm hdual (hz ▸ hle)
    have hv := heq.mp (hz.trans hdual'.symm)
    have hcorner := hcorners hdual'
    have hc := corner_representative w hs C f g hC hF
    have ho := corner_offset f g
    have cancel (k : ℝ) (hk : k ≠ 0) (h : (k : ℂ) • Z₀ = (k : ℂ) • Z) : Z = Z₀ := by
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      ext i j
      have he := congrFun (congrFun h i) j
      exact (mul_left_cancel₀ hk' he).symm
    change representative w Y = ((o / (2 * C) : ℝ) : ℂ) • Z at hv
    change representative w Y = ((((Y * offset f g).trace.re) / (2 * C) : ℝ) : ℂ) • Z at hv
    rcases hcorner with hh | hh
    · rw [hh, hc.1, ho.1] at hv
      exact cancel _ (by positivity : 0 < F / (2 * C)).ne' hv
    · rw [hh, hc.2, ho.2] at hv
      exact cancel _ (div_ne_zero (neg_ne_zero.mpr hF.ne') (by positivity : 0 < 2 * C).ne') hv
  have hattain : ratio Z₀ = opt := by
    let Y₀ := swaps (-1) 1
    have hY₀ : Y₀.IsHermitian := swaps_hermitian _ _
    let V₀ := representative w Y₀
    have ho : (Y₀ * offset f g).trace.re = F := (corner_offset f g).1
    have hv : V₀ = ((F / (2 * C) : ℝ) : ℂ) • Z₀ :=
      (corner_representative w hs C f g hC hF).1
    have hpair : (Y₀ * (Z₀ + offset f g)).trace.re = pairing w V₀ Z₀ + F := by
      rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, ho,
        (representative_spec w Y₀ hw hs hY₀).2.2.1 Z₀ hZ₀.2]
    have htest : (Y₀ * (Z₀ + offset f g)).trace.re ≤ traceNorm (Z₀ + offset f g) := by
      have hunit : Y₀ ∈ unitaryGroup Slot ℂ := by
        apply Matrix.mem_unitaryGroup_iff'.mpr
        rw [hY₀.star_eq]
        exact swaps_square (-1) 1 (by norm_num) (by norm_num)
      exact (traceNorm_eq_max_re_tr_U (Z₀ + offset f g)).2 ⟨⟨Y₀, hunit⟩, rfl⟩
    have hnonneg : 0 ≤ (Y₀ * (Z₀ + offset f g)).trace.re := by
      rw [hpair, hv, pairing_smul, pairing_self]
      have hk : 0 ≤ F / (2 * C) := by positivity
      linarith [mul_nonneg hk (energy_nonneg w hw Z₀)]
    have hsq : (Y₀ * (Z₀ + offset f g)).trace.re ^ 2 ≤ traceNorm (Z₀ + offset f g) ^ 2 :=
      pow_le_pow_left₀ hnonneg htest 2
    have heq := (quotient_le_dual w hw V₀ Z₀ C F hC).2.mpr hv
    rw [← hpair, corner_energy w hw hs] at heq
    have hD : 0 < C + energy w Z₀ / 2 := by linarith [energy_nonneg w hw Z₀]
    have hlower : opt ≤ ratio Z₀ := by
      change opt ≤ traceNorm (Z₀ + offset f g) ^ 2 / (C + energy w Z₀ / 2)
      convert div_le_div_of_nonneg_right hsq hD.le using 1
      dsimp [opt, m]
      linarith only [heq]
    exact le_antisymm (hbound Z₀ hZ₀).1 hlower
  refine ⟨⟨⟨Z₀, hZ₀, hattain⟩, ?_⟩, ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact (hbound Z hZ).1
  · intro Z hZ
    exact ⟨(hbound Z hZ).2, fun he => he ▸ hattain⟩

#print axioms weighted_hessian_maximum

end D5.S3.Quantum.Recovery.PetzWeightedHessianOptimum
