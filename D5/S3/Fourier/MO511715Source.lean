/- GID: D5/S3/Fourier/MO511715Source
   generality: I
   mirror-B: D5/B/S3/Fourier/MO511715Source
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Euclidean five-dimensional cutoff series and its original nested time integral. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

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

/-- The original full square is written as two independent interval integrals. -/
def timeIntegral (q L A B : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..q, Real.exp (-L * (q - α)) *
    ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))

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
    · rfl
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

private lemma embed_add (a b : Lattice) : embed (a + b) = embed a + embed b := by
  ext i
  simp [embed]

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
  apply tsum_eq_zero
  intro m
  simp [kernel, selectedMask_vanish n m.1 hn]

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

end
end D5.S3.Fourier.MO511715Source
