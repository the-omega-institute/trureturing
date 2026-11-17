/- GID: D5/S3/Quantum/Foundation/EffectDensityRepair
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/EffectDensityRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform spectral repair turns trace and effect lower bounds into one density matrix. -/

/-
For a Hermitian matrix, an almost normalized trace and a uniform lower bound
on every effect control the negative spectral mass. Normalizing the positive
part yields one density matrix when its trace is positive. When that trace is
zero, a coordinate density gives the same uniform estimate.
-/

import D5.S3.Quantum.Foundation.EffectAdditivityStability
import D5.S3.Weil.ZetaLinear.HermitianPosPart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.EffectAdditivityStability
open Matrix Unitary RHLinalg
namespace D5.S3.Quantum.Foundation.EffectDensityRepair

def negativeProjector {d : ℕ} {A : Mat d} (hA : A.IsHermitian) : Mat d :=
  specMap hA (fun x => if x < 0 then 1 else 0)

theorem negativeProjector_effect {d : ℕ} {A : Mat d} (hA : A.IsHermitian) :
    IsEffect (negativeProjector hA) := by
  have hone : specMap hA (fun _ => 1) = (1 : Mat d) := by
    simp [specMap]
  constructor
  · apply specMap_posSemidef
    intro i
    split <;> norm_num
  · rw [← hone, negativeProjector, ← specMap_sub]
    apply specMap_posSemidef
    intro i
    change (0 : ℝ) ≤ 1 - (if hA.eigenvalues i < 0 then 1 else 0)
    split <;> norm_num

theorem mul_negativeProjector {d : ℕ} {A : Mat d} (hA : A.IsHermitian) :
    A * negativeProjector hA = -hermNegPart hA := by
  have hf : (id * (fun x : ℝ => if x < 0 then 1 else 0)) =
      (0 - (fun x : ℝ => x⁻)) := by
    funext x
    by_cases hx : x < 0
    · simp [hx, negPart_def, max_eq_left (le_of_lt (neg_pos.mpr hx))]
    · simp [hx, negPart_eq_zero.mpr (le_of_not_gt hx)]
  calc
    A * negativeProjector hA = specMap hA id * negativeProjector hA :=
      congrArg (fun X : Mat d => X * negativeProjector hA) (specMap_id hA).symm
    _ = specMap hA (id * (fun x : ℝ => if x < 0 then 1 else 0)) :=
      (specMap_mul hA _ _).symm
    _ = -hermNegPart hA := by
      rw [hf, specMap_sub, specMap_zero, zero_sub]
      rfl

theorem psd_effect_pairing_bounds {d : ℕ} {B E : Mat d}
    (hB : B.PosSemidef) (hE : IsEffect E) :
    0 ≤ (trace (B*E)).re ∧ (trace (B*E)).re ≤ (trace B).re := by
  have h0 := (Complex.nonneg_iff.mp (hB.trace_mul_nonneg hE.1)).1
  have h1 := (Complex.nonneg_iff.mp (hB.trace_mul_nonneg hE.2)).1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at h1
  exact ⟨h0, by linarith⟩

theorem psd_trace_real {d : ℕ} {B : Mat d} (hB : B.PosSemidef) :
    trace B = ((trace B).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm

theorem uniform_density_repair
    (d : ℕ) (hd : 1 ≤ d) (η : ℝ) (hη : 0 ≤ η)
    (A : Mat d) (hA : A.IsHermitian)
    (htrace : |(trace A).re - 1| ≤ η)
    (hlower : ∀ E : Mat d, E.PosSemidef → (1-E).PosSemidef →
      -η ≤ (trace (A*E)).re) :
    ∃ ρ : Mat d, ρ.PosSemidef ∧ trace ρ = 1 ∧
      ∀ E : Mat d, E.PosSemidef → (1-E).PosSemidef →
        |(trace (ρ*E)).re - (trace (A*E)).re| ≤ 3*η := by
  let B : Mat d := hermPosPart hA
  let M : Mat d := hermNegPart hA
  let t : ℝ := (trace B).re
  let n : ℝ := (trace M).re
  have hB : B.PosSemidef := hermPosPart_posSemidef hA
  have hM : M.PosSemidef := hermNegPart_posSemidef hA
  have ht0 : 0 ≤ t := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have hn0 : 0 ≤ n := (Complex.nonneg_iff.mp hM.trace_nonneg).1
  have hdecomp : B - M = A := hermPosPart_sub_hermNegPart hA
  have htn : (trace A).re = t-n := rtrace_sub_decomp hA
  have hnη : n ≤ η := by
    have hP := negativeProjector_effect hA
    have hh := hlower (negativeProjector hA) hP.1 hP.2
    rw [mul_negativeProjector, Matrix.trace_neg, Complex.neg_re] at hh
    change -η ≤ -n at hh
    linarith
  have htnorm : |t-n-1| ≤ η := by rwa [htn] at htrace
  have htbound : |t-1| ≤ η+n := by
    have hh := abs_le.mp htnorm
    apply abs_le.mpr
    constructor <;> linarith
  have hpair (E : Mat d) :
      (trace (A*E)).re = (trace (B*E)).re - (trace (M*E)).re := by
    calc
      (trace (A*E)).re = (trace ((B-M)*E)).re :=
        congrArg (fun X : Mat d => (trace (X*E)).re) hdecomp.symm
      _ = _ := by rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  by_cases ht : 0 < t
  · let ρ : Mat d := t⁻¹ • B
    have hρ : ρ.PosSemidef := hB.smul (inv_nonneg.mpr ht.le)
    have hρtrace : trace ρ = 1 := by
      change trace (t⁻¹ • B) = 1
      rw [Matrix.trace_smul, psd_trace_real hB, Complex.real_smul]
      change ((t⁻¹ : ℝ) : ℂ) * (t : ℂ) = 1
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt ht), Complex.ofReal_one]
    refine ⟨ρ, hρ, hρtrace, ?_⟩
    intro E hE0 hE1
    have hE : IsEffect E := ⟨hE0, hE1⟩
    let b : ℝ := (trace (B*E)).re
    let m : ℝ := (trace (M*E)).re
    let q : ℝ := t⁻¹*b
    have hb : 0 ≤ b ∧ b ≤ t := psd_effect_pairing_bounds hB hE
    have hm : 0 ≤ m ∧ m ≤ n := psd_effect_pairing_bounds hM hE
    have hq0 : 0 ≤ q := mul_nonneg (inv_nonneg.mpr ht.le) hb.1
    have hq1 : q ≤ 1 := by
      calc
        t⁻¹*b ≤ t⁻¹*t := mul_le_mul_of_nonneg_left hb.2 (inv_nonneg.mpr ht.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt ht)
    have hbq : b = t*q := by
      dsimp [q]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht), one_mul]
    have hρE : (trace (ρ*E)).re = q := by
      simp only [ρ, q, b, Matrix.smul_mul, Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul]
    have hprod : |(1-t)*q| ≤ |t-1| := by
      rw [abs_mul, abs_of_nonneg hq0]
      calc
        |1-t| * q ≤ |1-t| := mul_le_of_le_one_right (abs_nonneg _) hq1
        _ = |t-1| := abs_sub_comm _ _
    calc
      |(trace (ρ*E)).re - (trace (A*E)).re| = |q-(b-m)| := by
        rw [hρE, hpair E]
      _ = |(1-t)*q+m| := by congr 1; nlinarith [hbq]
      _ ≤ |(1-t)*q| + |m| := abs_add_le _ _
      _ ≤ |t-1| + n := add_le_add hprod (by simpa only [abs_of_nonneg hm.1] using hm.2)
      _ ≤ (η+n)+n := add_le_add htbound (le_refl n)
      _ ≤ 3*η := by linarith only [hnη]
  · have htzero : t = 0 := le_antisymm (le_of_not_gt ht) ht0
    have hηlarge : 1+n ≤ η := by
      have hh := abs_le.mp htnorm
      rw [htzero] at hh
      linarith
    let i₀ : Fin d := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩
    let ρ : Mat d := diagonal (fun i => if i = i₀ then (1 : ℂ) else 0)
    have hρ : ρ.PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      split <;> norm_num
    have hρtrace : trace ρ = 1 := by
      simp [ρ, Matrix.trace_diagonal]
    refine ⟨ρ, hρ, hρtrace, ?_⟩
    intro E hE0 hE1
    have hE : IsEffect E := ⟨hE0, hE1⟩
    have hb := psd_effect_pairing_bounds hB hE
    have hm := psd_effect_pairing_bounds hM hE
    have hq := psd_effect_pairing_bounds hρ hE
    have hbzero : (trace (B*E)).re = 0 := by
      have hb1 : (trace (B*E)).re ≤ t := hb.2
      rw [htzero] at hb1
      linarith [hb.1]
    have hq1 : (trace (ρ*E)).re ≤ 1 := by simpa [hρtrace] using hq.2
    rw [hpair E, hbzero, zero_sub, sub_neg_eq_add,
      abs_of_nonneg (add_nonneg hq.1 hm.1)]
    change (trace (ρ*E)).re + (trace (M*E)).re ≤ 3*η
    have hm1 : (trace (M*E)).re ≤ n := hm.2
    calc
      (trace (ρ*E)).re + (trace (M*E)).re ≤ 1+n := add_le_add hq1 hm1
      _ ≤ η := hηlarge
      _ ≤ 3*η := by linarith only [hη]

end D5.S3.Quantum.Foundation.EffectDensityRepair
