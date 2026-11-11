/- GID: D5/S3/Fourier/MO511715Source
   generality: I
   mirror-B: D5/B/S3/Fourier/MO511715Source
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/MO511715Source.claim; result=D5/S3/Fourier/MO511715Source.result; claim=D5/S3/Fourier/MO511715Source.claim
   digest: The Euclidean five-dimensional cutoff series and its original nested time integral. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # The exact five-dimensional Euclidean cutoff series

The scalar conventions cover real and complex cutoffs. The mask has precisely the
published range and support implication. No zero lattice mode is removed.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Fourier.MO511715Source

noncomputable section

abbrev Lattice := Fin 5 → ℤ
abbrev Space := EuclideanSpace ℝ (Fin 5)

/-- Coordinate casting into Euclidean space, rather than the supremum-norm function space. -/
def embed (k : Lattice) : Space := WithLp.toLp 2 (fun i => (k i : ℝ))

def length (k : Lattice) : ℝ := ‖embed k‖

def frequency (k : Lattice) : ℝ := ‖(2 * Real.pi) • embed k‖

def LegalMask (ψ : Lattice → Lattice → ℝ) : Prop :=
  (∀ k l, 0 ≤ ψ k l ∧ ψ k l ≤ 1) ∧
  ∀ k l, ψ k l ≠ 0 → (9 / 64 : ℝ) * length k ≤ length l ∧
    length l ≤ (64 / 9 : ℝ) * length k

/-- The source uses the complete closed square with its product Lebesgue measure. -/
def timeIntegral (q L A B : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..q, Real.exp (-L * (q - α)) *
    ∫ v : ℝ × ℝ in Icc (0 : ℝ) α ×ˢ Icc (0 : ℝ) α,
      Real.exp (-A * (q + α - 2 * v.1) - B * (q + α - 2 * v.2))

def kernel (ψ : Lattice → Lattice → ℝ) (q : ℝ) (n m₁ m₂ : Lattice) : ℝ :=
  frequency (n - m₁) ^ 2 * ψ (n - m₁) m₁ *
    timeIntegral q (frequency (n - m₁) ^ 4)
      (frequency (m₁ - m₂) ^ 4) (frequency m₂ ^ 4)

def cutoffWeight {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ε : ℝ) (m₁ m₂ : Lattice) : ℝ :=
  ‖ζ (ε • embed (m₁ - m₂))‖ ^ 2 * ‖ζ (ε • embed m₂)‖ ^ 2

/-- Summation over all ordered pairs, with no removed zero modes. -/
def phi {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ψ : Lattice → Lattice → ℝ) (ε q : ℝ) (n : Lattice) : ℝ :=
  ∑' m : Lattice × Lattice, kernel ψ q n m.1 m.2 * cutoffWeight ζ ε m.1 m.2

def delta {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ψ : Lattice → Lattice → ℝ) (ε r : ℝ) (u : Lattice) : ℝ :=
  phi ζ ψ ε r u - phi ζ ψ ε r 0

def SmoothCutoff {F : Type*} [RCLike F] (ζ : Space → F) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ ζ 0 = 1

def UniformEstimate {F : Type*} [RCLike F] (ζ : Space → F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ ψ : Lattice → Lattice → ℝ, LegalMask ψ →
    ∀ r : ℝ, 0 ≤ r → ∀ u : Lattice, ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ →
      |delta ζ ψ ε₂ r u - delta ζ ψ ε₁ r u| ≤ C * |ε₂ - ε₁| ^ δ

/-- Both conventional scalar readings, with constants chosen after the fixed cutoff. -/
def claim : Prop :=
  (∀ ζ : Space → ℝ, SmoothCutoff ζ → UniformEstimate ζ) ∧
  (∀ ζ : Space → ℂ, SmoothCutoff ζ → UniformEstimate ζ)

def firstUnit : Lattice := fun i => if i = 0 then 1 else 0

/-- One mask, independent of the scales and the cutoff. -/
def selectedMask (k l : Lattice) : ℝ :=
  if k + l = firstUnit ∧ (9 / 64 : ℝ) * length k ≤ length l ∧
      length l ≤ (64 / 9 : ℝ) * length k then 1 else 0

/-- The exact change from difference variables to the original ordered indices. -/
def indexEquiv : (Lattice × Lattice) ≃ (Lattice × Lattice) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp

private lemma square_integral_eq_iterated (q A B α : ℝ) (hα : 0 ≤ α) :
    (∫ v : ℝ × ℝ in Icc (0 : ℝ) α ×ˢ Icc (0 : ℝ) α,
      Real.exp (-A * (q + α - 2 * v.1) - B * (q + α - 2 * v.2))) =
    ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂)) := by
  have hc : Continuous (fun v : ℝ × ℝ =>
      Real.exp (-A * (q + α - 2 * v.1) - B * (q + α - 2 * v.2))) := by fun_prop
  have hi : IntegrableOn (fun v : ℝ × ℝ =>
      Real.exp (-A * (q + α - 2 * v.1) - B * (q + α - 2 * v.2)))
      (Icc (0 : ℝ) α ×ˢ Icc (0 : ℝ) α) ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hi]
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hα]

private lemma timeIntegral_eq_iterated (q L A B : ℝ) (hq : 0 ≤ q) :
    timeIntegral q L A B =
    ∫ α in (0 : ℝ)..q, Real.exp (-L * (q - α)) *
      ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
        Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂)) := by
  apply intervalIntegral.integral_congr
  intro α hα
  rw [uIcc_of_le hq] at hα
  dsimp only
  rw [square_integral_eq_iterated q A B α hα.1]

private lemma inner_factor (q A B α : ℝ) :
    (∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))) =
    Real.exp (-(A + B) * (q + α)) *
      (∫ v in (0 : ℝ)..α, Real.exp (2 * A * v)) *
      (∫ v in (0 : ℝ)..α, Real.exp (2 * B * v)) := by
  have he (v w : ℝ) :
      Real.exp (-A * (q + α - 2 * v) - B * (q + α - 2 * w)) =
      Real.exp (-(A + B) * (q + α)) * Real.exp (2 * A * v) *
        Real.exp (2 * B * w) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

private lemma inner_continuous (q A B : ℝ) : Continuous (fun α : ℝ =>
    ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))) := by
  simp_rw [inner_factor]
  have hc (D : ℝ) : Continuous (fun v : ℝ => Real.exp (2 * D * v)) := by fun_prop
  exact ((by fun_prop : Continuous (fun α : ℝ => Real.exp (-(A + B) * (q + α)))).mul
    (intervalIntegral.continuous_primitive (fun a b => (hc A).intervalIntegrable a b) 0)).mul
      (intervalIntegral.continuous_primitive (fun a b => (hc B).intervalIntegrable a b) 0)

private lemma outer_continuous (q L A B : ℝ) : Continuous (fun α : ℝ =>
    Real.exp (-L * (q - α)) *
      ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
        Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))) :=
  (by fun_prop : Continuous (fun α : ℝ => Real.exp (-L * (q - α)))).mul
    (inner_continuous q A B)

private lemma inner_nonneg (q A B α : ℝ) (hα : 0 ≤ α) :
    0 ≤ ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂)) := by
  apply intervalIntegral.integral_nonneg hα
  intro v hv
  exact intervalIntegral.integral_nonneg_of_forall hα (fun w => (Real.exp_pos _).le)

private lemma timeIntegral_nonneg (q L A B : ℝ) (hq : 0 ≤ q) :
    0 ≤ timeIntegral q L A B := by
  rw [timeIntegral_eq_iterated q L A B hq]
  apply intervalIntegral.integral_nonneg hq
  intro α hα
  exact mul_nonneg (Real.exp_pos _).le (inner_nonneg q A B α hα.1)

private lemma integral_lower_subinterval (f : ℝ → ℝ) (hf : Continuous f)
    (a b c d M : ℝ) (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
    (hn : ∀ x ∈ Icc c d, 0 ≤ f x) (hl : ∀ x ∈ Icc a b, M ≤ f x) :
    (b - a) * M ≤ ∫ x in c..d, f x := by
  calc
    (b - a) * M = ∫ _x in a..b, M := by simp
    _ ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_on hab (intervalIntegrable_const)
        (hf.intervalIntegrable a b) hl
    _ ≤ ∫ x in c..d, f x :=
      intervalIntegral.integral_mono_interval hca hab hbd
        (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hn x ⟨hx.1.le, hx.2⟩))
        (hf.intervalIntegrable c d)

private lemma timeIntegral_lower (L A B h : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hh : 0 < h) (hhsmall : h ≤ 1 / 2) :
    Real.exp (-(L + 3 * A + 3 * B) * h) * h ^ 3 ≤ timeIntegral 1 L A B := by
  rw [timeIntegral_eq_iterated 1 L A B (by norm_num)]
  let E := Real.exp (-(3 * A + 3 * B) * h)
  have hinner (α : ℝ) (hα : α ∈ Icc (1 - h) 1) :
      h ^ 2 * E ≤ ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
        Real.exp (-A * (1 + α - 2 * v₁) - B * (1 + α - 2 * v₂)) := by
    have ha : 0 ≤ α - h := by linarith [hα.1]
    have hb : α - h ≤ α := by linarith
    have hrow (v : ℝ) (hv : v ∈ Icc (α - h) α) :
        h * E ≤ ∫ w in (0 : ℝ)..α,
          Real.exp (-A * (1 + α - 2 * v) - B * (1 + α - 2 * w)) := by
      have ht := integral_lower_subinterval
        (fun w : ℝ => Real.exp (-A * (1 + α - 2 * v) - B * (1 + α - 2 * w)))
        (by fun_prop) (α - h) α 0 α E ha hb le_rfl
        (fun _ _ => (Real.exp_pos _).le) ?_
      · simpa only [sub_sub_cancel] using ht
      · intro w hw
        apply Real.exp_le_exp.mpr
        have hv' : 1 + α - 2 * v ≤ 3 * h := by linarith [hv.1, hα.1]
        have hw' : 1 + α - 2 * w ≤ 3 * h := by linarith [hw.1, hα.1]
        nlinarith [mul_le_mul_of_nonneg_left hv' hA,
          mul_le_mul_of_nonneg_left hw' hB]
    have ht := integral_lower_subinterval
      (fun v : ℝ => ∫ w in (0 : ℝ)..α,
        Real.exp (-A * (1 + α - 2 * v) - B * (1 + α - 2 * w)))
      (by fun_prop) (α - h) α 0 α (h * E) ha hb le_rfl
      (fun _ _ => intervalIntegral.integral_nonneg_of_forall (by linarith)
        (fun _ => (Real.exp_pos _).le)) hrow
    convert ht using 1 <;> ring
  have ht := integral_lower_subinterval
    (fun α : ℝ => Real.exp (-L * (1 - α)) *
      ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
        Real.exp (-A * (1 + α - 2 * v₁) - B * (1 + α - 2 * v₂)))
    (outer_continuous 1 L A B) (1 - h) 1 0 1
    (Real.exp (-L * h) * (h ^ 2 * E)) (by linarith) (by linarith) le_rfl
    (fun α hα => mul_nonneg (Real.exp_pos _).le (inner_nonneg 1 A B α hα.1)) ?_
  · convert ht using 1
    · rw [show -(L + 3 * A + 3 * B) * h = -L * h + -(3 * A + 3 * B) * h by ring,
        Real.exp_add]
      dsimp [E]
      ring
  · intro α hα
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hL (show 0 ≤ α - (1 - h) by linarith [hα.1])]
    · exact hinner α hα
    · exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    · exact (Real.exp_pos _).le

/-- A lower estimate for the actual time integral, using a subregion of its full square. -/
theorem time_integral_ge (L A B h : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : 0 < h) (hhsmall : h ≤ 1 / 2) (hbudget : (L + 3 * A + 3 * B) * h ≤ 1) :
    Real.exp (-1) * h ^ 3 ≤ timeIntegral 1 L A B := by
  calc
    Real.exp (-1) * h ^ 3 ≤ Real.exp (-(L + 3 * A + 3 * B) * h) * h ^ 3 := by
      gcongr
      linarith
    _ ≤ timeIntegral 1 L A B := timeIntegral_lower L A B h hL hA hB hh hhsmall

private lemma embed_sub (a b : Lattice) : embed (a - b) = embed a - embed b := by
  ext i
  simp [embed]

private lemma frequency_eq (k : Lattice) : frequency k = (2 * Real.pi) * length k := by
  simp [frequency, length, norm_smul, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

private def coordinateBox (R : ℝ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 5 => Finset.Icc (-⌈R⌉) ⌈R⌉)

private lemma mem_coordinateBox (k : Lattice) (R : ℝ) (hk : length k ≤ R) :
    k ∈ coordinateBox R := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi : |(k i : ℝ)| ≤ length k := PiLp.norm_apply_le (embed k) i
  have hc : |(k i : ℝ)| ≤ (⌈R⌉ : ℝ) := hi.trans (hk.trans (Int.le_ceil R))
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (abs_le.mp hc).1
  · exact_mod_cast (abs_le.mp hc).2

/-- Compact support makes every positive-scale source sum a genuine finite sum. -/
theorem cutoff_finite_support {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (hζ : HasCompactSupport ζ) (ε : ℝ) (hε : 0 < ε) :
    (Function.support (fun m : Lattice × Lattice => cutoffWeight ζ ε m.1 m.2)).Finite := by
  classical
  obtain ⟨R, hR, hz⟩ := hζ.exists_pos_le_norm
  let S := coordinateBox (R / ε)
  have hmem (k : Lattice) (hk : ζ (ε • embed k) ≠ 0) : k ∈ S := by
    apply mem_coordinateBox
    have hn : ‖ε • embed k‖ < R := lt_of_not_ge (fun h => hk (hz _ h))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε] at hn
    exact (lt_div_iff₀ hε).mpr (by simpa [length, mul_comm] using hn) |>.le
  apply (((S ×ˢ S).image indexEquiv).finite_toSet).subset
  intro m hm
  have hw : cutoffWeight ζ ε m.1 m.2 ≠ 0 := hm
  have ha : ζ (ε • embed (m.1 - m.2)) ≠ 0 := by
    intro h
    exact hw (by simp [cutoffWeight, h])
  have hb : ζ (ε • embed m.2) ≠ 0 := by
    intro h
    exact hw (by simp [cutoffWeight, h])
  apply Finset.mem_image.mpr
  refine ⟨(m.1 - m.2, m.2), Finset.mem_product.mpr ⟨hmem _ ha, hmem _ hb⟩, ?_⟩
  exact indexEquiv.apply_symm_apply m

private lemma source_summable {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (hζ : HasCompactSupport ζ) (ψ : Lattice → Lattice → ℝ) (ε q : ℝ) (hε : 0 < ε)
    (n : Lattice) : Summable (fun m : Lattice × Lattice =>
      kernel ψ q n m.1 m.2 * cutoffWeight ζ ε m.1 m.2) := by
  apply summable_of_ne_finset_zero (s := (cutoff_finite_support ζ hζ ε hε).toFinset)
  intro m hm
  have hz : cutoffWeight ζ ε m.1 m.2 = 0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hm
  simp [hz]

private lemma selectedMask_legal : LegalMask selectedMask := by
  constructor
  · intro k l
    unfold selectedMask
    split_ifs <;> norm_num
  · intro k l h
    unfold selectedMask at h
    split_ifs at h with hc
    · exact hc.2
    · exact (h rfl).elim

private lemma selectedMask_vanish (n m : Lattice) (hn : n ≠ firstUnit) :
    selectedMask (n - m) m = 0 := by
  apply if_neg
  intro h
  apply hn
  simpa using h.1

private lemma phi_vanish {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ε q : ℝ) (n : Lattice) (hn : n ≠ firstUnit) : phi ζ selectedMask ε q n = 0 := by
  unfold phi
  calc
    _ = ∑' _m : Lattice × Lattice, (0 : ℝ) := tsum_congr (fun m => by
      simp [kernel, selectedMask_vanish n m.1 hn])
    _ = 0 := tsum_zero

private lemma delta_selected {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ε r : ℝ) : delta ζ selectedMask ε r firstUnit = phi ζ selectedMask ε r firstUnit := by
  have h : (0 : Lattice) ≠ firstUnit := by
    intro he
    have := congrFun he 0
    simp [firstUnit] at this
  simp [delta, phi_vanish ζ ε r 0 h]

private lemma source_term_nonneg {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ψ : Lattice → Lattice → ℝ) (hψ : LegalMask ψ) (ε q : ℝ) (hq : 0 ≤ q)
    (n : Lattice) (m : Lattice × Lattice) :
    0 ≤ kernel ψ q n m.1 m.2 * cutoffWeight ζ ε m.1 m.2 := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (hψ.1 _ _).1)
      (timeIntegral_nonneg _ _ _ _ hq))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

private lemma phi_reindex {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ψ : Lattice → Lattice → ℝ) (ε q : ℝ) (n : Lattice) :
    phi ζ ψ ε q n = ∑' p : Lattice × Lattice,
      kernel ψ q n (p.1 + p.2) p.2 *
        (‖ζ (ε • embed p.1)‖ ^ 2 * ‖ζ (ε • embed p.2)‖ ^ 2) := by
  have h := indexEquiv.tsum_eq (fun m : Lattice × Lattice =>
    kernel ψ q n m.1 m.2 * cutoffWeight ζ ε m.1 m.2)
  simpa [phi, cutoffWeight, indexEquiv] using h.symm

def blockBox (N : ℕ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 5 => Finset.Ico (N : ℤ) (2 * (N : ℤ)))

private lemma blockBox_card (N : ℕ) : (blockBox N).card = N ^ 5 := by
  simp [blockBox, Fintype.card_piFinset, Int.card_Ico,
    show 2 * (N : ℤ) - N = N by ring]

private lemma blockBox_coordinates (N : ℕ) (a : Lattice) (ha : a ∈ blockBox N) :
    ∀ i, (N : ℝ) ≤ a i ∧ (a i : ℝ) ≤ 2 * (N : ℝ) := by
  intro i
  have hi := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp ha i)
  constructor
  · exact_mod_cast hi.1
  · exact_mod_cast hi.2.le

private lemma length_sq (k : Lattice) : length k ^ 2 = ∑ i, (k i : ℝ) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq (embed k)

private lemma box_norm_bounds (N : ℕ) (hN : 1 ≤ N) (a b : Lattice)
    (ha : a ∈ blockBox N) (hb : b ∈ blockBox N) :
    length a ≤ 5 * N ∧ length b ≤ 5 * N ∧
      4 * N ≤ length (a + b) ∧ length (a + b) ≤ 9 * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcoord := blockBox_coordinates N a ha
  have hcoord' := blockBox_coordinates N b hb
  have hs (v : Lattice) (hv : ∀ i, (N : ℝ) ≤ v i ∧ (v i : ℝ) ≤ 2 * N) :
      length v ^ 2 ≤ 20 * (N : ℝ) ^ 2 := by
    rw [length_sq]
    calc
      _ ≤ ∑ _i : Fin 5, 4 * (N : ℝ) ^ 2 := Finset.sum_le_sum (fun i _ => by
        nlinarith [(hv i).1, (hv i).2])
      _ = _ := by norm_num; ring
  have hamax := hs a hcoord
  have hbmax := hs b hcoord'
  have hmmin : 20 * (N : ℝ) ^ 2 ≤ length (a + b) ^ 2 := by
    rw [length_sq]
    calc
      _ = ∑ _i : Fin 5, 4 * (N : ℝ) ^ 2 := by norm_num; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by
        simp only [Pi.add_apply, Int.cast_add]
        nlinarith [(hcoord i).1, (hcoord' i).1])
  have hmmax : length (a + b) ^ 2 ≤ 80 * (N : ℝ) ^ 2 := by
    rw [length_sq]
    calc
      _ ≤ ∑ _i : Fin 5, 16 * (N : ℝ) ^ 2 := Finset.sum_le_sum (fun i _ => by
        simp only [Pi.add_apply, Int.cast_add]
        nlinarith [(hcoord i).1, (hcoord i).2, (hcoord' i).1, (hcoord' i).2])
      _ = _ := by norm_num; ring
  have hn (v : Lattice) : 0 ≤ length v := norm_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hn a]
  · nlinarith [hn b]
  · nlinarith [hn (a + b)]
  · nlinarith [hn (a + b)]

private lemma firstUnit_length : length firstUnit = 1 := by
  have hs : length firstUnit ^ 2 = 1 := by
    rw [length_sq]
    norm_num [firstUnit, Fin.sum_univ_succ]
  have hn : 0 ≤ length firstUnit := norm_nonneg _
  nlinarith

private lemma block_frequencies (N : ℕ) (hN : 1 ≤ N) (a b : Lattice)
    (ha : a ∈ blockBox N) (hb : b ∈ blockBox N) :
    selectedMask (firstUnit - (a + b)) (a + b) = 1 ∧
      (N : ℝ) ≤ length (firstUnit - (a + b)) ∧
      length (firstUnit - (a + b)) ≤ 10 * N ∧
      length a ≤ 5 * N ∧ length b ≤ 5 * N := by
  obtain ⟨ha', hb', hmmin, hmmax⟩ := box_norm_bounds N hN a b ha hb
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hkmax : length (firstUnit - (a + b)) ≤ 1 + length (a + b) := by
    simpa only [length, embed_sub, show ‖embed firstUnit‖ = 1 from firstUnit_length]
      using norm_sub_le (embed firstUnit) (embed (a + b))
  have hm : length (a + b) ≤ 1 + length (firstUnit - (a + b)) := by
    have hh := norm_sub_le (embed firstUnit) (embed (firstUnit - (a + b)))
    rw [← embed_sub, sub_sub_cancel, ← length, ← length, firstUnit_length] at hh
    exact hh
  refine ⟨?_, by linarith, by linarith, ha', hb'⟩
  unfold selectedMask
  apply if_pos
  refine ⟨by simp, ?_, ?_⟩ <;> linarith

def eta : ℝ := 1 / (20000 * (2 * Real.pi) ^ 4)

def kernelConstant : ℝ := (2 * Real.pi) ^ 2 * Real.exp (-1) * eta ^ 3

private lemma eta_pos : 0 < eta := by unfold eta; positivity

private lemma kernelConstant_pos : 0 < kernelConstant := by
  unfold kernelConstant
  exact mul_pos (mul_pos (pow_pos (by positivity) _) (Real.exp_pos _)) (pow_pos eta_pos _)

/-- A source-kernel estimate on actual ten-dimensional lattice blocks. -/
theorem kernel_block_lower (N : ℕ) (hN : 1 ≤ N) (a b : Lattice)
    (ha : a ∈ blockBox N) (hb : b ∈ blockBox N) :
    kernelConstant / (N : ℝ) ^ 10 ≤ kernel selectedMask 1 firstUnit (a + b) b := by
  obtain ⟨hmask, hkmin, hkmax, hamax, hbmax⟩ := block_frequencies N hN a b ha hb
  let D : ℝ := 2 * Real.pi
  let h : ℝ := eta / (N : ℝ) ^ 4
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hD : 1 < D := by dsimp [D]; linarith [Real.pi_gt_three]
  have hh : 0 < h := div_pos eta_pos (pow_pos hNp _)
  have hhalf : h ≤ 1 / 2 := by
    have hp : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hNr
    have hDp : (1 : ℝ) ≤ D ^ 4 := one_le_pow₀ hD.le
    dsimp [h, eta, D] at *
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 4)).mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 20000 * (2 * Real.pi) ^ 4)).mpr
    nlinarith
  have hrate (k : Lattice) (c : ℝ) (hc : 0 ≤ c) (hk : length k ≤ c * N) :
      frequency k ^ 4 ≤ D ^ 4 * c ^ 4 * (N : ℝ) ^ 4 := by
    have hlen : 0 ≤ length k := norm_nonneg _
    rw [frequency_eq]
    calc
      _ ≤ (D * (c * (N : ℝ))) ^ 4 := by dsimp [D]; gcongr
      _ = _ := by ring
  have hk := hrate (firstUnit - (a + b)) 10 (by norm_num) hkmax
  have ha' := hrate a 5 (by norm_num) hamax
  have hb' := hrate b 5 (by norm_num) hbmax
  have hbudget : (frequency (firstUnit - (a + b)) ^ 4 +
      3 * frequency a ^ 4 + 3 * frequency b ^ 4) * h ≤ 1 := by
    calc
      _ ≤ (D ^ 4 * 10 ^ 4 * (N : ℝ) ^ 4 +
          3 * (D ^ 4 * 5 ^ 4 * (N : ℝ) ^ 4) +
          3 * (D ^ 4 * 5 ^ 4 * (N : ℝ) ^ 4)) * h := by gcongr
      _ = 11 / 16 := by dsimp [h, eta, D]; field_simp; ring
      _ ≤ 1 := by norm_num
  have ht := time_integral_ge (frequency (firstUnit - (a + b)) ^ 4)
    (frequency a ^ 4) (frequency b ^ 4) h (by positivity) (by positivity) (by positivity)
    hh hhalf hbudget
  have hpref : D ^ 2 * (N : ℝ) ^ 2 ≤ frequency (firstUnit - (a + b)) ^ 2 := by
    rw [frequency_eq]
    calc
      _ = (D * (N : ℝ)) ^ 2 := by ring
      _ ≤ _ := by dsimp [D]; gcongr
  unfold kernel
  rw [hmask, mul_one, add_sub_cancel_right]
  calc
    kernelConstant / (N : ℝ) ^ 10 = (D ^ 2 * (N : ℝ) ^ 2) *
        (Real.exp (-1) * h ^ 3) := by dsimp [kernelConstant, h, D]; field_simp <;> ring
    _ ≤ _ := mul_le_mul hpref ht (by positivity) (sq_nonneg _)

private lemma cutoff_near_zero {F : Type*} [RCLike F] (ζ : Space → F)
    (hc : ContinuousAt ζ 0) (hz : ζ 0 = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x : Space, ‖x‖ ≤ ρ → (1 / 2 : ℝ) ≤ ‖ζ x‖ := by
  obtain ⟨s, hs, hζ⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  refine ⟨min 1 (s / 2), lt_min zero_lt_one (by linarith), min_le_left _ _, ?_⟩
  intro x hx
  have hd : dist x 0 < s := by
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hx.trans (min_le_right _ _)) (by linarith)
  have he := hζ hd
  rw [hz] at he
  have ht := norm_sub_norm_le (1 : F) (ζ x)
  rw [norm_one, ← dist_eq_norm, dist_comm] at ht
  linarith

private lemma dyadic_boxes_disjoint (i j : ℕ) (hij : i ≠ j) :
    Disjoint (blockBox (2 ^ i)) (blockBox (2 ^ j)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hai := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp ha (0 : Fin 5))
  have haj := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hb (0 : Fin 5))
  rcases lt_or_gt_of_ne hij with h | h
  · have hp : 2 * 2 ^ i ≤ (2 : ℕ) ^ j := by
      calc
        _ = 2 ^ (i + 1) := by rw [pow_succ]; omega
        _ ≤ _ := Nat.pow_le_pow_right (by decide) h
    have hp' : 2 * ((2 ^ i : ℕ) : ℤ) ≤ ((2 ^ j : ℕ) : ℤ) := by exact_mod_cast hp
    omega
  · have hp : 2 * 2 ^ j ≤ (2 : ℕ) ^ i := by
      calc
        _ = 2 ^ (j + 1) := by rw [pow_succ]; omega
        _ ≤ _ := Nat.pow_le_pow_right (by decide) h
    have hp' : 2 * ((2 ^ j : ℕ) : ℤ) ≤ ((2 ^ i : ℕ) : ℤ) := by exact_mod_cast hp
    omega

private def pairBlock (j : ℕ) : Finset (Lattice × Lattice) :=
  blockBox (2 ^ j) ×ˢ blockBox (2 ^ j)

private lemma pairBlock_disjoint (i j : ℕ) (hij : i ≠ j) :
    Disjoint (pairBlock i) (pairBlock j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (dyadic_boxes_disjoint i j hij)
    (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1

def blockConstant : ℝ := kernelConstant / 16

private lemma blockConstant_pos : 0 < blockConstant := div_pos kernelConstant_pos (by norm_num)

private def reindexedTerm {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ε : ℝ) (p : Lattice × Lattice) : ℝ :=
  kernel selectedMask 1 firstUnit (p.1 + p.2) p.2 *
    (‖ζ (ε • embed p.1)‖ ^ 2 * ‖ζ (ε • embed p.2)‖ ^ 2)

private lemma block_mass_lower {F : Type*} [RCLike F] (ζ : Space → F) (ρ : ℝ)
    (hρ : 0 < ρ) (hζ : ∀ x : Space, ‖x‖ ≤ ρ → (1 / 2 : ℝ) ≤ ‖ζ x‖)
    (J j : ℕ) (hj : j ≤ J) :
    blockConstant ≤ ∑ p ∈ pairBlock j, reindexedTerm ζ (ρ / (5 * (2 : ℝ) ^ J)) p := by
  let N := 2 ^ j
  have hN : 1 ≤ N := Nat.one_le_pow _ _ (by decide)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hpow : (N : ℝ) ≤ (2 : ℝ) ^ J := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hj
  have hε : 0 < ρ / (5 * (2 : ℝ) ^ J) := by positivity
  have hweight (a : Lattice) (ha : a ∈ blockBox N) :
      (1 / 2 : ℝ) ≤ ‖ζ ((ρ / (5 * (2 : ℝ) ^ J)) • embed a)‖ := by
    apply hζ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hbound := (box_norm_bounds N hN a a ha ha).1
    calc
      ρ / (5 * (2 : ℝ) ^ J) * ‖embed a‖ ≤
          ρ / (5 * (2 : ℝ) ^ J) * (5 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hε.le
      _ ≤ ρ / (5 * (2 : ℝ) ^ J) * (5 * (2 : ℝ) ^ J) := by gcongr
      _ = ρ := div_mul_cancel₀ _ (by positivity)
  have hterm (p : Lattice × Lattice) (hp : p ∈ pairBlock j) :
      blockConstant / (N : ℝ) ^ 10 ≤ reindexedTerm ζ (ρ / (5 * (2 : ℝ) ^ J)) p := by
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have hk := kernel_block_lower N hN p.1 p.2 ha hb
    have hwa := hweight p.1 ha
    have hwb := hweight p.2 hb
    have hw : (1 / 16 : ℝ) ≤ ‖ζ ((ρ / (5 * (2 : ℝ) ^ J)) • embed p.1)‖ ^ 2 *
        ‖ζ ((ρ / (5 * (2 : ℝ) ^ J)) • embed p.2)‖ ^ 2 := by
      have ha' : (1 / 4 : ℝ) ≤ ‖ζ ((ρ / (5 * (2 : ℝ) ^ J)) • embed p.1)‖ ^ 2 := by nlinarith
      have hb' : (1 / 4 : ℝ) ≤ ‖ζ ((ρ / (5 * (2 : ℝ) ^ J)) • embed p.2)‖ ^ 2 := by nlinarith
      nlinarith [mul_le_mul ha' hb' (by norm_num) (sq_nonneg _)]
    calc
      blockConstant / (N : ℝ) ^ 10 = (kernelConstant / (N : ℝ) ^ 10) * (1 / 16) := by
        dsimp [blockConstant]; ring
      _ ≤ _ := mul_le_mul hk hw (by norm_num)
        (le_trans (div_nonneg kernelConstant_pos.le (by positivity)) hk)
  calc
    blockConstant = (pairBlock j).card * (blockConstant / (N : ℝ) ^ 10) := by
      rw [show (pairBlock j).card = N ^ 10 by
        simp [pairBlock, Finset.card_product, blockBox_card, N, ← pow_add]]
      push_cast
      field_simp
    _ = ∑ _p ∈ pairBlock j, blockConstant / (N : ℝ) ^ 10 := by simp
    _ ≤ _ := Finset.sum_le_sum hterm

/-- Joint cutoff control and disjoint actual blocks force linear growth in the number of scales. -/
theorem phi_dyadic_growth {F : Type} [RCLike F] (ζ : Space → F)
    (hc : ContinuousAt ζ 0) (hz : ζ 0 = 1) (hs : HasCompactSupport ζ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ J : ℕ,
      blockConstant * (J + 1) ≤ phi ζ selectedMask (ρ / (5 * (2 : ℝ) ^ J)) 1 firstUnit := by
  classical
  obtain ⟨ρ, hρ, hρ1, hζ⟩ := cutoff_near_zero ζ hc hz
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro J
  let S := (Finset.range (J + 1)).biUnion pairBlock
  have hsum : Summable (reindexedTerm ζ (ρ / (5 * (2 : ℝ) ^ J))) := by
    unfold reindexedTerm
    have ht := (indexEquiv.summable_iff).mpr
      (source_summable ζ hs selectedMask (ρ / (5 * (2 : ℝ) ^ J)) 1 (by positivity) firstUnit)
    simpa [cutoffWeight, indexEquiv, Function.comp_def] using ht
  have hn (p : Lattice × Lattice) : 0 ≤ reindexedTerm ζ (ρ / (5 * (2 : ℝ) ^ J)) p := by
    simpa [reindexedTerm, cutoffWeight, indexEquiv] using
      source_term_nonneg ζ selectedMask selectedMask_legal (ρ / (5 * (2 : ℝ) ^ J)) 1
        (by norm_num) firstUnit (indexEquiv p)
  rw [phi_reindex]
  change blockConstant * (J + 1) ≤ ∑' p, reindexedTerm ζ (ρ / (5 * (2 : ℝ) ^ J)) p
  calc
    blockConstant * (J + 1) = ∑ _j ∈ Finset.range (J + 1), blockConstant := by simp; ring
    _ ≤ ∑ j ∈ Finset.range (J + 1), ∑ p ∈ pairBlock j,
        reindexedTerm ζ (ρ / (5 * (2 : ℝ) ^ J)) p :=
      Finset.sum_le_sum (fun j hj => block_mass_lower ζ ρ hρ hζ J j
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ = ∑ p ∈ S, reindexedTerm ζ (ρ / (5 * (2 : ℝ) ^ J)) p :=
      (Finset.sum_biUnion (fun i _ j _ hij => pairBlock_disjoint i j hij)).symm
    _ ≤ _ := hsum.sum_le_tsum S (fun p _ => hn p)

private lemma uniform_estimate_fails {F : Type} [RCLike F] (ζ : Space → F)
    (hc : ContinuousAt ζ 0) (hz : ζ 0 = 1) (hs : HasCompactSupport ζ) :
    ¬ UniformEstimate ζ := by
  obtain ⟨ρ, hρ, hρ1, hgrowth⟩ := phi_dyadic_growth ζ hc hz hs
  rintro ⟨C, hC, δ, hδ, hbound⟩
  let M := phi ζ selectedMask (ρ / 5) 1 firstUnit
  obtain ⟨J, hJ⟩ := exists_nat_gt ((M + C) / blockConstant)
  have hJ' : M + C < blockConstant * (J + 1) := by
    have ht := (div_lt_iff₀ blockConstant_pos).mp hJ
    nlinarith [blockConstant_pos]
  let ε := ρ / (5 * (2 : ℝ) ^ J)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεref : 0 < ρ / 5 := by positivity
  have heps : ε ≤ ρ / 5 := by
    dsimp [ε]
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 5)).mpr
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
    nlinarith
  have hgap : |ρ / 5 - ε| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr heps)]
    linarith
  have hb := hbound selectedMask selectedMask_legal 1 (by norm_num) firstUnit
    ε (ρ / 5) hε hεref
  rw [delta_selected, delta_selected] at hb
  have hrpow : |ρ / 5 - ε| ^ δ ≤ (1 : ℝ) :=
    Real.rpow_le_one (abs_nonneg _) hgap hδ.le
  have hupper : phi ζ selectedMask ε 1 firstUnit ≤ M + C := by
    have hrhs : C * |ρ / 5 - ε| ^ δ ≤ C := by nlinarith
    have ha := neg_le_abs (M - phi ζ selectedMask ε 1 firstUnit)
    dsimp [M] at *
    linarith
  have hlower := hgrowth J
  change blockConstant * (J + 1) ≤ phi ζ selectedMask ε 1 firstUnit at hlower
  linarith

/-- The literal complete source estimate, including both scalar readings, is false. -/
theorem result : ¬ claim := by
  intro h
  let f : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩
  have hz : f (0 : Space) = 1 := f.one_of_mem_closedBall (by simp [f])
  have hs : SmoothCutoff (f : Space → ℝ) := ⟨f.contDiff, f.hasCompactSupport, hz⟩
  exact uniform_estimate_fails f hs.1.continuous.continuousAt hz f.hasCompactSupport
    (h.1 f hs)

end
end D5.S3.Fourier.MO511715Source
