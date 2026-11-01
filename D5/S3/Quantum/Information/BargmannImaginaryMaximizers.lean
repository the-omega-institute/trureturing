/- GID: D5/S3/Quantum/Information/BargmannImaginaryMaximizers
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/BargmannImaginaryMaximizers
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Maximal imaginary qubit Bargmann tuples form one latitude-polygon orbit. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#19224; Proved).
Direct frozen dependencies: GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
(statement_id: sha256:accd04d85421c0847456ddb52626f272e79ea98e568dcf9dfeddc5035a1f2013).
All auxiliary theorems are consumed bind-only steps; consumers are in the delivery inventory.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19337.
The wave-function condition and rank-one projector are inlined in their source expressions.
-/
import D5.S3.Quantum.Algebra.GramUnitaryExtension
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Binding conventions for L. Zhang and B. Xie, "A Survey of Bargmann Invariants: Geometric Foundations and
Applications", arXiv:2601.01858v2: Section 2 (wave functions and pure states), Definition 3.1 (the Bargmann invariant
`Δ_n(Ψ) = tr(ρ_1 ⋯ ρ_n)`), Corollary 5.5 (`τ_n = cos^n(π/n) sec^{n−1}(π/[2(n−1)])`) and the open question on the tuples in
`ℂ²` attaining `Im tr(ψ_1 ⋯ ψ_n) = τ_n`. Indices are `0`-based. -/

namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers

open Matrix

/-- Definition 3.1: the `n`th-order Bargmann invariant `Δ_n(Ψ) = tr(ψ_1 ⋯ ψ_n)`. -/
noncomputable def bargmann {n : ℕ} (Ψ : Fin n → Fin 2 → ℂ) : ℂ :=
  ((List.ofFn fun j => (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) (Ψ j)).prod).trace

/-- Corollary 5.5: `τ_n = cos^n(π/n) sec^{n−1}(π/[2(n−1)])`. -/
noncomputable def tau (n : ℕ) : ℝ :=
  Real.cos (Real.pi / n) ^ n / Real.cos (Real.pi / (2 * (n - 1 : ℝ))) ^ (n - 1)

/-- The proposed maximising tuple `v_j = (√(1 − t_n), √t_n · e^{2πij/n})`, with
`t_n = (1 − tan(π/(2(n−1))) / tan(π/n)) / 2`. -/
noncomputable def maximizer (n : ℕ) (j : Fin n) : Fin 2 → ℂ :=
  let t : ℝ := (1 - Real.tan (Real.pi / (2 * (n - 1 : ℝ))) / Real.tan (Real.pi / n)) / 2
  ![(Real.sqrt (1 - t) : ℂ), (Real.sqrt t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * j / n)]

/-- The open question "what is the complete set of n-tuples Ψ = (|ψ_1⟩, …, |ψ_n⟩) in ℂ² that achieve
Im tr(ψ_1 … ψ_n) = τ_n?", answered: for every `n ≥ 3`, exactly the tuples `ψ_j = η_j U v_j` with one common unitary `U`
and unimodular phases `η_j`. -/
def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ Ψ : Fin n → Fin 2 → ℂ, (∀ j, (star (Ψ j) ⬝ᵥ Ψ j = 1)) →
    ((bargmann Ψ).im = tau n ↔
      ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ η : Fin n → ℂ, (∀ j, ‖η j‖ = 1) ∧
        ∀ j, Ψ j = η j • (U *ᵥ maximizer n j))

end D5.S3.Quantum.Information.BargmannImaginaryMaximizers

open Matrix
open scoped BigOperators ComplexOrder
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Scalar
open Set
private noncomputable def profile (n : ℕ) (x : ℝ) : ℝ := Real.sin (n*x) / Real.cos x ^ n
private theorem profile_derivative {n : ℕ} (hn : 1 ≤ n) (x : ℝ) (hc : Real.cos x ≠ 0) : HasDerivAt (profile n) ((n : ℝ) * Real.cos (((n : ℝ)-1)*x) / Real.cos x ^ (n+1)) x := by
  have hs := (Real.hasDerivAt_sin ((n : ℝ)*x)).comp x ((hasDerivAt_id x).const_mul (n : ℝ))
  have hd := (Real.hasDerivAt_cos x).pow n
  have hh := hs.div hd (pow_ne_zero n hc)
  convert hh using 1
  · ext y
    rfl
  · dsimp
    have hp : Real.cos x ^ n = Real.cos x ^ (n-1) * Real.cos x := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    have hangle : ((n : ℝ)-1)*x = (n : ℝ)*x-x := by exact sub_one_mul (↑n) x
    rw [hangle, Real.cos_sub]; rw [pow_succ, hp]
    field_simp
    ring
private theorem scalar_angles {n : ℕ} (hn : 3 ≤ n) : 0 < Real.pi / (2*((n : ℝ)-1)) ∧ Real.pi / (2*((n : ℝ)-1)) < Real.pi/(n : ℝ) ∧ Real.pi/(n : ℝ) < Real.pi/2 := by
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hden : 0 < 2*((n : ℝ)-1) := by linarith
  refine ⟨div_pos Real.pi_pos hden, ?_, ?_⟩
  · rw [div_lt_div_iff₀ hden hnpos]
    nlinarith [Real.pi_pos]
  · rw [div_lt_iff₀ hnpos]
    nlinarith [Real.pi_pos]
private theorem profile_rising {n : ℕ} (hn : 3 ≤ n) : StrictMonoOn (profile n) (Icc 0 (Real.pi/(2*((n : ℝ)-1)))) := by
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hn1 : 1 ≤ n := by exact Nat.one_le_of_lt hn
  have hden : (n : ℝ)-1 ≠ 0 := by linarith
  have hb := scalar_angles hn
  have hcrit : ((n : ℝ)-1)*(Real.pi/(2*((n : ℝ)-1))) = Real.pi/2 := by
    field_simp [hden]
    <;> ring
  have hcosx : ∀ x ∈ Icc 0 (Real.pi/(2*((n : ℝ)-1))), 0 < Real.cos x := by
    intro x hx
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [Real.pi_pos,hx.1], lt_of_le_of_lt hx.2 (lt_trans hb.2.1 hb.2.2)⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 _)
  · intro x hx
    exact (profile_derivative hn1 x (hcosx x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(profile_derivative hn1 x (hcosx x ⟨hx.1.le,hx.2.le⟩).ne').deriv]
    have hangle : ((n : ℝ)-1)*x < Real.pi/2 := by
      nlinarith [mul_lt_mul_of_pos_left hx.2 (show 0 < (n : ℝ)-1 by linarith)]
    have hangle0 : 0 ≤ ((n : ℝ)-1)*x := mul_nonneg (by linarith) hx.1.le
    have hcosarg := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hangle⟩
    exact div_pos (mul_pos (by linarith) hcosarg) (pow_pos (hcosx x ⟨hx.1.le,hx.2.le⟩) _)
private theorem profile_falling {n : ℕ} (hn : 3 ≤ n) : StrictAntiOn (profile n) (Icc (Real.pi/(2*((n : ℝ)-1))) (Real.pi/n)) := by
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hn1 : 1 ≤ n := by exact Nat.one_le_of_lt hn
  have hnpos : (0 : ℝ) < n := by exact Nat.cast_pos'.mpr hn1
  have hden : (n : ℝ)-1 ≠ 0 := by linarith
  have hb := scalar_angles hn
  have hcrit : ((n : ℝ)-1)*(Real.pi/(2*((n : ℝ)-1))) = Real.pi/2 := by
    field_simp [hden]
    <;> ring
  have hna : (n : ℝ)*(Real.pi/n) = Real.pi := by field_simp
  have hcosx : ∀ x ∈ Icc (Real.pi/(2*((n : ℝ)-1))) (Real.pi/n), 0 < Real.cos x := by
    intro x hx
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [Real.pi_pos,hx.1], lt_of_le_of_lt hx.2 hb.2.2⟩
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro x hx
    exact (profile_derivative hn1 x (hcosx x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(profile_derivative hn1 x (hcosx x ⟨hx.1.le,hx.2.le⟩).ne').deriv]
    have hangle : Real.pi/2 < ((n : ℝ)-1)*x := by
      nlinarith [mul_lt_mul_of_pos_left hx.1 (show 0 < (n : ℝ)-1 by linarith)]
    have hanglehi : ((n : ℝ)-1)*x < Real.pi+Real.pi/2 := by
      nlinarith [mul_lt_mul_of_pos_left hx.2 (show 0 < (n : ℝ)-1 by linarith), Real.pi_pos]
    have hcosarg := Real.cos_neg_of_pi_div_two_lt_of_lt hangle hanglehi
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hcosarg)
      (pow_pos (hcosx x ⟨hx.1.le,hx.2.le⟩) _)
private theorem profile_unique_max {n : ℕ} (hn : 3 ≤ n) {x : ℝ} (hx : x ∈ Icc 0 (Real.pi/n)) : profile n x ≤ profile n (Real.pi/(2*((n : ℝ)-1))) ∧ (profile n x = profile n (Real.pi/(2*((n : ℝ)-1))) ↔ x = Real.pi/(2*((n : ℝ)-1))) := by
  have hb := scalar_angles hn
  rcases lt_trichotomy x (Real.pi/(2*((n : ℝ)-1))) with hlt | heq | hgt
  · have h := profile_rising hn ⟨hx.1,hlt.le⟩ ⟨hb.1.le,le_rfl⟩ hlt
    exact ⟨h.le, by simp [ne_of_lt h, ne_of_lt hlt]⟩
  · subst x
    exact ⟨le_rfl, by simp⟩
  · have h := profile_falling hn ⟨le_rfl,hb.2.1.le⟩ ⟨hgt.le,hx.2⟩ hgt
    exact ⟨h.le, by simp [ne_of_lt h, ne_of_gt hgt]⟩
private theorem profile_at_critical {n : ℕ} (hn : 3 ≤ n) : profile n (Real.pi/(2*((n : ℝ)-1))) = 1 / Real.cos (Real.pi/(2*((n : ℝ)-1))) ^ (n-1) := by
  let b := Real.pi/(2*((n : ℝ)-1))
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hden : (n : ℝ)-1 ≠ 0 := by linarith
  have hangle : (n : ℝ)*b = Real.pi/2+b := by
    dsimp [b]
    field_simp [hden]
    <;> ring
  have hcos : Real.cos b ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    have hb := scalar_angles hn
    exact ⟨by dsimp [b]; linarith [Real.pi_pos],lt_trans hb.2.1 hb.2.2⟩
  change Real.sin ((n : ℝ)*b)/Real.cos b ^ n = 1/Real.cos b ^ (n-1)
  rw [hangle,Real.sin_add,Real.sin_pi_div_two,Real.cos_pi_div_two]; simp only [one_mul,zero_mul,add_zero]
  have hpow : Real.cos b ^ n = Real.cos b ^ (n-1)*Real.cos b := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hpow]; field_simp
private theorem phase_profile_max {n : ℕ} (hn : 3 ≤ n) {φ : ℝ} (hφ : φ ∈ Icc 0 (Real.pi/n)) : Real.cos (Real.pi/n)^n * Real.sin ((n : ℝ)*φ) / Real.cos (Real.pi/n-φ)^n ≤ Real.cos (Real.pi/n)^n / Real.cos (Real.pi/(2*((n : ℝ)-1)))^(n-1) ∧ (Real.cos (Real.pi/n)^n * Real.sin ((n : ℝ)*φ) / Real.cos (Real.pi/n-φ)^n = Real.cos (Real.pi/n)^n / Real.cos (Real.pi/(2*((n : ℝ)-1)))^(n-1) ↔ φ = Real.pi/n-Real.pi/(2*((n : ℝ)-1))) := by
  have hx : Real.pi/n-φ ∈ Icc 0 (Real.pi/n) := ⟨by linarith [hφ.2],by linarith [hφ.1]⟩
  have h := profile_unique_max hn hx
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hnpos : (0 : ℝ) < n := by linarith
  have ha := (scalar_angles hn).2.2
  have hca : 0 < Real.cos (Real.pi/n)^n := by
    apply pow_pos
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [div_pos Real.pi_pos hnpos],ha⟩
  have hangle : (n : ℝ)*(Real.pi/n-φ) = Real.pi-(n : ℝ)*φ := by
    field_simp
    <;> ring
  have hsin : Real.sin ((n : ℝ)*(Real.pi/n-φ)) = Real.sin ((n : ℝ)*φ) := by
    rw [hangle,Real.sin_pi_sub]
  have hleft : Real.cos (Real.pi/n)^n * profile n (Real.pi/n-φ) =
      Real.cos (Real.pi/n)^n * Real.sin ((n : ℝ)*φ)/Real.cos (Real.pi/n-φ)^n := by
    simp only [profile,hsin,mul_div_assoc]
  have hright : Real.cos (Real.pi/n)^n * profile n (Real.pi/(2*((n : ℝ)-1))) =
      Real.cos (Real.pi/n)^n / Real.cos (Real.pi/(2*((n : ℝ)-1)))^(n-1) := by
    rw [profile_at_critical hn,mul_one_div]
  rw [← hleft,← hright]
  refine ⟨mul_le_mul_of_nonneg_left h.1 hca.le,?_⟩
  rw [mul_right_inj' hca.ne',h.2]
  constructor <;> intro hh <;> linarith
private theorem scalar_saturation {n : ℕ} (hn : 3 ≤ n) (φ P R : ℝ) (hφ : φ ∈ Ioo 0 (Real.pi/n)) (hR : 0 ≤ R) (hprod : P ≤ R^n) (hedge : R*Real.cos (Real.pi/n-φ) ≤ Real.cos (Real.pi/n)) (hmax : P*Real.sin ((n : ℝ)*φ) = Real.cos (Real.pi/n)^n / Real.cos (Real.pi/(2*((n : ℝ)-1)))^(n-1)) : φ = Real.pi/n-Real.pi/(2*((n : ℝ)-1)) ∧ R = Real.cos (Real.pi/n)/Real.cos (Real.pi/(2*((n : ℝ)-1))) := by
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  have ha := scalar_angles hn
  have hcos : 0 < Real.cos (Real.pi/n-φ) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith [Real.pi_pos,hφ.2],by linarith [hφ.1,ha.2.2]⟩
  have hca : 0 < Real.cos (Real.pi/n) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [div_pos Real.pi_pos hnpos],ha.2.2⟩
  have hsin : 0 < Real.sin ((n : ℝ)*φ) := by
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hnpos hφ.1)
    have hm := mul_lt_mul_of_pos_left hφ.2 hnpos
    have hna : (n : ℝ)*(Real.pi/n) = Real.pi := by field_simp
    rwa [hna] at hm
  have hRq : R ≤ Real.cos (Real.pi/n)/Real.cos (Real.pi/n-φ) :=
    (le_div_iff₀ hcos).mpr hedge
  have hpow := pow_le_pow_left₀ hR hRq n
  have h1 := mul_le_mul_of_nonneg_right hprod hsin.le
  have h2 := mul_le_mul_of_nonneg_right hpow hsin.le
  have hprofile := phase_profile_max hn ⟨hφ.1.le,hφ.2.le⟩
  have halg : (Real.cos (Real.pi/n)/Real.cos (Real.pi/n-φ))^n*
      Real.sin ((n : ℝ)*φ) =
      Real.cos (Real.pi/n)^n*Real.sin ((n : ℝ)*φ)/Real.cos (Real.pi/n-φ)^n := by
    rw [div_pow]; ring
  have hprofileeq : Real.cos (Real.pi/n)^n*Real.sin ((n : ℝ)*φ)/
      Real.cos (Real.pi/n-φ)^n =
      Real.cos (Real.pi/n)^n / Real.cos (Real.pi/(2*((n : ℝ)-1)))^(n-1) := by
    rw [← halg]; rw [halg] at h2
    linarith
  have hφeq := hprofile.2.mp hprofileeq
  refine ⟨hφeq,?_⟩
  have hpowequal : R^n = (Real.cos (Real.pi/n)/Real.cos (Real.pi/n-φ))^n := by
    apply (mul_left_inj' hsin.ne').mp
    rw [halg,hprofileeq]
    linarith
  have hReq := (pow_left_inj₀ hR (div_pos hca hcos).le hn0).mp hpowequal
  rw [hφeq] at hReq
  have hangle : Real.pi/n-(Real.pi/n-Real.pi/(2*((n : ℝ)-1))) =
      Real.pi/(2*((n : ℝ)-1)) := by exact sub_sub_self (Real.pi / ↑n) (Real.pi / (2 * (↑n - 1)))
  rwa [hangle] at hReq
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Scalar
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Family
private theorem latitude_overlap_polar (a b : ℝ)
    (hsa : Real.sin a ≠ 0) (hcb : Real.cos b ≠ 0) :
    let t := (1 - Real.tan b / Real.tan a)/2
    (1-(t : ℂ)) + (t : ℂ) * Complex.exp ((2*a : ℝ) * Complex.I) =
      ((Real.cos a / Real.cos b : ℝ) : ℂ) * Complex.exp ((a-b : ℝ)*Complex.I) := by
  dsimp
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
    rw [Real.cos_two_mul, Real.cos_sub, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]; field_simp [hsa,hcb]
    linear_combination -2*Real.sin b*Real.cos a*(Real.sin_sq_add_cos_sq a)
  · simp only [Complex.add_im, Complex.sub_im, Complex.one_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, add_zero,
      sub_zero, zero_add, Complex.exp_ofReal_mul_I_im]
    rw [Real.sin_two_mul, Real.sin_sub, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]; field_simp [hsa,hcb]
    <;> ring
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Family
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude
noncomputable def latitude (t : ℝ) (z : ℂ) : Fin 2 → ℂ :=
  ![(Real.sqrt (1-t) : ℂ), (Real.sqrt t : ℂ)*z]
private theorem two_mode_unitary {ι : Type*} [Fintype ι] (p q : Fin 2 → ℂ) (z : ι → ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hp : star p ⬝ᵥ p = ((1-t : ℝ) : ℂ)) (hq : star q ⬝ᵥ q = (t : ℂ)) (hpq : star p ⬝ᵥ q = 0) : ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∀ j, p + z j • q = U *ᵥ latitude t (z j) := by
  classical
  have hqp : star q ⬝ᵥ p = 0 := by rw [star_dotProduct, hpq, star_zero]
  let B : Matrix (Fin 2) ι ℂ := fun a j => (p+z j • q) a
  let A : Matrix (Fin 2) ι ℂ := fun a j => latitude t (z j) a
  have hs0 : (Real.sqrt (1-t) : ℂ) * Real.sqrt (1-t) = ((1-t : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by linarith : 0 ≤ 1-t)
  have hs1 : (Real.sqrt t : ℂ) * Real.sqrt t = (t : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt ht0
  have hGram : Bᴴ * B = Aᴴ * A := by
    ext j k
    change star (p+z j • q) ⬝ᵥ (p+z k • q) =
      star (latitude t (z j)) ⬝ᵥ latitude t (z k)
    simp only [star_add, star_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hp, hq, hpq, hqp,
      mul_zero, zero_add, add_zero]
    simp only [latitude, dotProduct, Fin.sum_univ_two, Pi.star_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_mul, Complex.star_def,
      Complex.conj_ofReal, map_mul]
    rw [hs0]; rw [← hs1]
    ring
  obtain ⟨U,hU⟩ :=
    D5.S3.Quantum.Algebra.GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq B A hGram
  refine ⟨U, U.property, ?_⟩
  intro j
  ext a
  exact congrFun (congrFun hU a) j
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Character
private theorem phase_exp {n : ℕ} [NeZero n] (j : Fin n) : (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j = Complex.exp (2*Real.pi*Complex.I*(j.val : ℂ)/(n : ℂ)) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    simp only [ZMod.finEquiv,RingEquiv.refl_apply,ZMod.stdAddChar_apply,
      ZMod.toCircle_apply,ZMod.val]
    rfl
private theorem phase_norm {n : ℕ} [NeZero n] (j : Fin n) : ‖(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j‖ = 1 :=
  AddChar.norm_apply ZMod.stdAddChar ((ZMod.finEquiv n) j)
private theorem phase_next {n : ℕ} [NeZero n] (j : Fin n) : star ((fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j)*(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (j+1) = (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n) := by
  have hh : (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (j+1) = (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j*(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n) := by
    dsimp only
    rw [map_add,AddChar.map_add_eq_mul]
  rw [hh,← mul_assoc]
  have hn : star ((fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j)*(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j = 1 := by
    simpa only [Complex.star_def,phase_norm,one_pow,Complex.ofReal_one] using
      Complex.conj_mul' ((fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j)
  rw [hn,one_mul]
private theorem phase_one {n : ℕ} [NeZero n] (hn : 3 ≤ n) : (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n) = Complex.exp (((2*(Real.pi/n) : ℝ) : ℂ)*Complex.I) := by
  rw [phase_exp]
  have hv : (1 : Fin n).val = 1 := by
    rw [Fin.val_one',Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [hv]
  push_cast
  congr 1
  ring
private theorem phase_one_im_pos {n : ℕ} [NeZero n] (hn : 3 ≤ n) : 0 < ((fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n)).im := by
  rw [phase_one hn,Complex.exp_ofReal_mul_I_im]
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlo : 0 < 2*(Real.pi/(n : ℝ)) := mul_pos (by norm_num) (div_pos Real.pi_pos hnpos)
  have hhi : 2*(Real.pi/(n : ℝ)) < Real.pi := by
    rw [← mul_div_assoc,div_lt_iff₀ hnpos]
    nlinarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi hlo hhi
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Character
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude
theorem latitude_dot (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z w : ℂ) : star (latitude t z) ⬝ᵥ latitude t w = ((1-t : ℝ) : ℂ) + (t : ℂ)*star z*w := by
  have hs0 : (Real.sqrt (1-t) : ℂ) * Real.sqrt (1-t) = ((1-t : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by linarith : 0 ≤ 1-t)
  have hs1 : (Real.sqrt t : ℂ) * Real.sqrt t = (t : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt ht0
  simp only [latitude, dotProduct, Fin.sum_univ_two, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_mul, Complex.star_def, Complex.conj_ofReal, map_mul]
  rw [hs0]
  calc _ = ((1-t : ℝ) : ℂ) + ((Real.sqrt t : ℂ)*Real.sqrt t)*(starRingEnd ℂ z)*w := by ring
       _ = _ := by rw [hs1]
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Argument
open Set
private theorem positive_argument {n : ℕ} (hn : 0 < n) (z : ℂ) (hz : 0 < z.im) : z.arg/(n : ℝ) ∈ Ioo 0 (Real.pi/n) ∧ ‖z‖*Real.sin ((n : ℝ)*(z.arg/n)) = z.im := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have harg0 : z.arg ≠ 0 := by
    intro hh; exact hz.ne' (Complex.arg_eq_zero_iff.mp hh).2
  have hargpos : 0 < z.arg :=
    lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hz.le) harg0.symm
  have harglt : z.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')
  refine ⟨⟨div_pos hargpos hnR,(div_lt_div_iff_of_pos_right hnR).mpr harglt⟩,?_⟩
  rw [mul_div_cancel₀ z.arg hnR.ne']; exact Complex.norm_mul_sin_arg z
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Argument
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Ray
private theorem phase_preserves_unit (v : Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) (ξ : ℂ) (hξ : ‖ξ‖ = 1) : star (ξ • v) ⬝ᵥ (ξ • v) = 1 := by
  have hh : star ξ*ξ = 1 := by
    simpa only [Complex.star_def,hξ,one_pow,Complex.ofReal_one] using Complex.conj_mul' ξ
  simp only [star_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,hv,mul_one]
  simpa only [mul_comm] using hh
private theorem mean_ray {n : ℕ} (r : Fin n → ℝ) (e : ℂ) : (n : ℂ)⁻¹*(∑ j, e*(r j : ℂ)) = (((∑ j,r j)/(n : ℝ) : ℝ) : ℂ)*e := by
  rw [← Finset.mul_sum,← Complex.ofReal_sum]
  push_cast
  ring
private theorem rotated_ray_real (a φ R : ℝ) : (Complex.exp (((-a : ℝ) : ℂ)*Complex.I)* ((R : ℂ)*Complex.exp ((φ : ℂ)*Complex.I))).re = R*Real.cos (a-φ) := by
  have he : (((-a : ℝ) : ℂ)*Complex.I)+((φ : ℂ)*Complex.I) =
      (((-(a-φ) : ℝ) : ℂ)*Complex.I) := by push_cast;ring
  calc
    _ = ((R : ℂ)*(Complex.exp (((-a : ℝ) : ℂ)*Complex.I)*
        Complex.exp ((φ : ℂ)*Complex.I))).re := by congr 1;ring
    _ = _ := by
      rw [← Complex.exp_add,he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero,Complex.exp_ofReal_mul_I_re,Real.cos_neg]
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Ray
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Polygon
open Set
private theorem polygon_cosine_edge {n : ℕ} (hn : 3 ≤ n) (k : Fin n) : Real.cos ((2*(k.val : ℝ)-1)*(Real.pi/n)) ≤ Real.cos (Real.pi/n) ∧ (Real.cos ((2*(k.val : ℝ)-1)*(Real.pi/n)) = Real.cos (Real.pi/n) ↔ k.val = 0 ∨ k.val = 1) := by
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have ha : 0 < Real.pi/(n : ℝ) := div_pos Real.pi_pos hnpos
  have hna : (n : ℝ)*(Real.pi/n) = Real.pi := by field_simp
  by_cases hk0 : k.val = 0
  · simp [hk0, Real.cos_neg]
  by_cases hk1 : k.val = 1
  · norm_num [hk1]
  have hk2 : 2 ≤ k.val := by omega
  have hk2R : (2 : ℝ) ≤ k.val := by exact Nat.ofNat_le_cast.mpr hk2
  have hkltR : (k.val : ℝ)+1 ≤ n := by exact_mod_cast (Nat.add_one_le_iff.mpr k.isLt)
  have hlo : Real.pi/n < (2*(k.val : ℝ)-1)*(Real.pi/n) := by
    nlinarith [mul_le_mul_of_nonneg_right hk2R ha.le]
  have hhi : (2*(k.val : ℝ)-1)*(Real.pi/n) < 2*Real.pi-Real.pi/n := by
    nlinarith [mul_le_mul_of_nonneg_right hkltR ha.le]
  have hstrict : Real.cos ((2*(k.val : ℝ)-1)*(Real.pi/n)) < Real.cos (Real.pi/n) := by
    by_cases hmid : (2*(k.val : ℝ)-1)*(Real.pi/n) ≤ Real.pi
    · exact Real.cos_lt_cos_of_nonneg_of_le_pi ha.le hmid hlo
    · have hreflect : Real.pi/n < 2*Real.pi-(2*(k.val : ℝ)-1)*(Real.pi/n) := by linarith
      have hreflectpi : 2*Real.pi-(2*(k.val : ℝ)-1)*(Real.pi/n) ≤ Real.pi := by linarith
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi ha.le hreflectpi hreflect
      simpa only [Real.cos_two_pi_sub] using h
  exact ⟨hstrict.le, by simp [hk0, hk1, ne_of_lt hstrict]⟩
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Polygon
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Rigidity
private theorem cross_zero_of_two_unit_samples {m : Type*} [Fintype m] (p q : m → ℂ) (z : ℂ) (hz : ‖z‖ = 1) (hzi : z.im ≠ 0) (henergy : star p ⬝ᵥ p + star q ⬝ᵥ q = 1) (hzero : star (p+q) ⬝ᵥ (p+q) = 1) (hone : star (p+z • q) ⬝ᵥ (p+z • q) = 1) : star p ⬝ᵥ q = 0 := by
  have hnorm : star z * z = 1 := by
    simpa only [Complex.star_def, hz, one_pow, Complex.ofReal_one] using Complex.conj_mul' z
  have hconj : star q ⬝ᵥ p = star (star p ⬝ᵥ q) := star_dotProduct q p
  simp only [star_add, add_dotProduct, dotProduct_add] at hzero
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at hone
  rw [hconj] at hzero hone
  have hre : (star p ⬝ᵥ q).re = 0 := by
    have hs := congrArg Complex.re henergy
    have hh := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.one_re, Complex.star_def, Complex.conj_re] at hh hs
    linarith
  have hlast : z * (star z * (star q ⬝ᵥ q)) = star q ⬝ᵥ q := by
    rw [← mul_assoc, mul_comm z (star z), hnorm, one_mul]
  simp only [mul_add] at hone
  rw [hlast] at hone
  have him : (star p ⬝ᵥ q).im = 0 := by
    have hs := congrArg Complex.re henergy
    have hh := congrArg Complex.re hone
    simp only [Complex.add_re, Complex.one_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_re] at hh hs
    rw [hre] at hh
    have hm : z.im * (star p ⬝ᵥ q).im = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_left hzi
  exact Complex.ext hre him
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Rigidity
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Gauge
private noncomputable def chainPhase (g : ℕ → ℂ) (e : ℂ) : ℕ → ℂ
  | 0 => 1
  | j+1 => chainPhase g e j * e * (‖g j‖ : ℂ) / g j
private theorem chain_phase_norm (g : ℕ → ℂ) (e : ℂ) (he : ‖e‖ = 1) (n : ℕ) (hg : ∀ j < n, g j ≠ 0) : ‖chainPhase g e n‖ = 1 := by
  induction n with
  | zero => simp [chainPhase]
  | succ n ih =>
    have hn := hg n (Nat.lt_succ_self n)
    have hp : ‖chainPhase g e n‖ = 1 := ih (fun j hj => hg j (Nat.lt_succ_of_lt hj))
    simp only [chainPhase,norm_div,norm_mul,hp,he,one_mul,Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hn)
private theorem chain_phase_product (g : ℕ → ℂ) (e : ℂ) (n : ℕ) : chainPhase g e n = e^n * (∏ j ∈ Finset.range n, (‖g j‖ : ℂ)) / (∏ j ∈ Finset.range n, g j) := by
  induction n with
  | zero => simp [chainPhase]
  | succ n ih =>
    simp only [chainPhase,ih,pow_succ,Finset.prod_range_succ]
    ring
private theorem chain_phase_edge (g : ℕ → ℂ) (e : ℂ) (he : ‖e‖ = 1) (n : ℕ) (hg : ∀ j ≤ n, g j ≠ 0) : star (chainPhase g e n) * chainPhase g e (n+1) * g n = e * (‖g n‖ : ℂ) := by
  have hp := chain_phase_norm g e he n (fun j hj => hg j hj.le)
  have hpn : star (chainPhase g e n) * chainPhase g e n = 1 := by
    simpa only [Complex.star_def,hp,one_pow,Complex.ofReal_one] using
      Complex.conj_mul' (chainPhase g e n)
  rw [chainPhase]
  calc
    _ = (star (chainPhase g e n) * chainPhase g e n) * e * (‖g n‖ : ℂ) := by
      field_simp [hg n le_rfl]
    _ = _ := by rw [hpn,one_mul]
private theorem chain_phase_closes (g : ℕ → ℂ) (e : ℂ) (n : ℕ) (hg : ∀ j < n, g j ≠ 0) (he : e^n * (∏ j ∈ Finset.range n, (‖g j‖ : ℂ)) = ∏ j ∈ Finset.range n, g j) : chainPhase g e n = 1 := by
  rw [chain_phase_product,he]
  apply div_self
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => hg j (Finset.mem_range.mp hj))
private theorem cycle_phase_norm {n : ℕ} [NeZero n] (g : Fin n → ℂ) (e : ℂ) (he : ‖e‖ = 1) (hg : ∀ j, g j ≠ 0) (j : Fin n) : ‖chainPhase (fun k => g (Fin.ofNat n k)) e j.val‖ = 1 :=
  chain_phase_norm _ _ he _ (fun k _ => hg (Fin.ofNat n k))
private theorem cycle_phase_edge {n : ℕ} [NeZero n] (g : Fin n → ℂ) (e : ℂ) (he : ‖e‖ = 1) (hg : ∀ j, g j ≠ 0) (hroot : e^n * (∏ j, (‖g j‖ : ℂ)) = ∏ j, g j) (j : Fin n) : star (chainPhase (fun k => g (Fin.ofNat n k)) e j.val) * chainPhase (fun k => g (Fin.ofNat n k)) e (j+1).val * g j = e*(‖g j‖ : ℂ) := by
  let gnat : ℕ → ℂ := fun k => g (Fin.ofNat n k)
  have hprod : (∏ k ∈ Finset.range n, gnat k) = ∏ k, g k := by
    rw [Finset.prod_range]; simp only [gnat,Fin.ofNat_val_eq_self]
  have hnormprod : (∏ k ∈ Finset.range n, (‖gnat k‖ : ℂ)) = ∏ k, (‖g k‖ : ℂ) := by
    rw [Finset.prod_range]; simp only [gnat,Fin.ofNat_val_eq_self]
  have hclose : chainPhase gnat e n = 1 :=
    chain_phase_closes gnat e n (fun k _ => hg (Fin.ofNat n k))
      (by rwa [hnormprod,hprod])
  have hnext : Fin.ofNat n (j.val+1) = j+1 := by
    exact (Fin.add_ofNat j 1).symm
  have hval : (j+1).val = (j.val+1)%n := by exact Fin.mk.inj_iff.mp (id (Eq.symm hnext))
  have hstep : chainPhase gnat e (j+1).val = chainPhase gnat e (j.val+1) := by
    rw [hval]
    by_cases hlt : j.val+1 < n
    · rw [Nat.mod_eq_of_lt hlt]
    · have hboundary : j.val+1=n := by omega
      rw [hboundary,Nat.mod_self,hclose,chainPhase]
  change star (chainPhase gnat e j.val) * chainPhase gnat e (j+1).val * g j = _
  rw [hstep]
  have hh := chain_phase_edge gnat e he j.val (fun k _ => hg (Fin.ofNat n k))
  simpa only [gnat,Fin.ofNat_val_eq_self] using hh
private theorem argument_root (n : ℕ) (hn : n ≠ 0) (z : ℂ) : (Complex.exp (((z.arg/n : ℝ) : ℂ)*Complex.I))^n * (‖z‖ : ℂ) = z := by
  rw [← Complex.exp_nat_mul]
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have he : (n : ℂ) * (((z.arg/n : ℝ) : ℂ)*Complex.I) = (z.arg : ℂ)*Complex.I := by
    push_cast
    field_simp
  rw [he,mul_comm]; exact Complex.norm_mul_exp_arg_mul_I z
private theorem cyclic_phase_equalization {n : ℕ} [NeZero n] (g : Fin n → ℂ) (hg : ∀ j, g j ≠ 0) : ∃ ξ : Fin n → ℂ, (∀ j, ‖ξ j‖ = 1) ∧ ∀ j, star (ξ j) * ξ (j+1) * g j = Complex.exp (((((∏ k, g k).arg)/n : ℝ) : ℂ)*Complex.I) * (‖g j‖ : ℂ) := by
  let e := Complex.exp (((((∏ k, g k).arg)/n : ℝ) : ℂ)*Complex.I)
  have he : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hnormprod : (∏ j, (‖g j‖ : ℂ)) = (‖∏ j, g j‖ : ℂ) := by
    rw [← Complex.ofReal_prod, norm_prod]
  have hroot : e^n * (∏ j, (‖g j‖ : ℂ)) = ∏ j, g j := by
    rw [hnormprod]; exact argument_root n (NeZero.ne n) _
  refine ⟨(fun j => chainPhase (fun k => g (Fin.ofNat n k)) e j.val), fun j => cycle_phase_norm g e he hg j, ?_⟩
  exact fun j => cycle_phase_edge g e he hg hroot j
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Gauge
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.AMGM
private theorem product_le_mean_pow {n : ℕ} (hn : n ≠ 0) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) : (∏ j, r j) ≤ ((∑ j, r j)/(n : ℝ)) ^ n := by
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin n => (1 : ℝ)) r
    (fun _ _ => zero_le_one) (by simpa using (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn) : (0 : ℝ) < n))
    (fun j _ => hr j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Real.rpow_one, one_mul] at h
  have hp : 0 ≤ ∏ j, r j := Finset.prod_nonneg fun j _ => hr j
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hp _) h n
  rw [Real.rpow_inv_natCast_pow hp hn] at hh
  exact hh
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.AMGM
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Fourier
open D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Character
private theorem reconstruct {n : ℕ} [NeZero n] (u : ZMod n → Fin 2 → ℂ) (j : ZMod n) : ZMod.dft ((fun k => (n : ℂ)⁻¹ • ZMod.dft u k)) (-j) = u j := by
  change ZMod.dft ((n : ℂ)⁻¹ • ZMod.dft u) (-j) = u j
  rw [map_smul, Pi.smul_apply]
  have h := congrFun ((ZMod.dft (N := n) (E := Fin 2 → ℂ)).symm_apply_apply u) j
  simpa only [ZMod.invDFT_apply'] using h
private theorem character_orthogonality {n : ℕ} [NeZero n] (k l : ZMod n) : (∑ j : ZMod n, star (ZMod.stdAddChar (j*k)) * ZMod.stdAddChar (j*l)) = if k = l then (n : ℂ) else 0 := by
  have ht (j : ZMod n) :
      star (ZMod.stdAddChar (j*k)) * ZMod.stdAddChar (j*l) =
        ZMod.stdAddChar (j * (l-k)) := by
    rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [ht]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]; simp only [sub_eq_zero, eq_comm, ZMod.card, Nat.cast_ite, Nat.cast_zero]
private theorem parseval_synthesis {n : ℕ} [NeZero n] (f g : ZMod n → Fin 2 → ℂ) : (∑ j, star (ZMod.dft f (-j)) ⬝ᵥ ZMod.dft g (-j)) = (n : ℂ) * ∑ k, star (f k) ⬝ᵥ g k := by
  classical
  simp only [ZMod.dft_apply, mul_neg, neg_neg, mul_comm, star_sum, star_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k, ∑ l, (∑ j : ZMod n,
        star (ZMod.stdAddChar (j*l)) * ZMod.stdAddChar (j*k)) *
          (star (f l) ⬝ᵥ g k) := by
      apply Finset.sum_congr rfl
      intro k _; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _; ring
    _ = _ := by
      simp_rw [character_orthogonality]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
private theorem energy_nonneg (v : Fin 2 → ℂ) : 0 ≤ (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) v :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).1
private theorem self_dot_eq_energy (v : Fin 2 → ℂ) : star v ⬝ᵥ v = ((fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) v : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg v)).2.symm
private theorem energy_zero_iff (v : Fin 2 → ℂ) : (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply dotProduct_star_self_eq_zero.mp
    rw [self_dot_eq_energy, h, Complex.ofReal_zero]
  · rintro rfl
    simp
private theorem synthesis_shift {n : ℕ} [NeZero n] (f : ZMod n → Fin 2 → ℂ) (j : ZMod n) : ZMod.dft f (-(j+1)) = ZMod.dft (fun k => ZMod.stdAddChar k • f k) (-j) := by
  simp only [ZMod.dft_apply, mul_neg, neg_neg, mul_comm, mul_add, add_mul, one_mul, mul_one, AddChar.map_add_eq_mul, smul_smul]
private theorem neighbor_sum_synthesis {n : ℕ} [NeZero n] (f : ZMod n → Fin 2 → ℂ) : (∑ j, star (ZMod.dft f (-j)) ⬝ᵥ ZMod.dft f (-(j+1))) = (n : ℂ) * ∑ k, ZMod.stdAddChar k * ((fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) : ℂ) := by
  simp_rw [synthesis_shift]
  rw [parseval_synthesis]
  simp only [dotProduct_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [self_dot_eq_energy]
  simp only [Complex.ofReal_re]
private theorem root_rotated_real {n : ℕ} [NeZero n] (k : ZMod n) : (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ZMod.stdAddChar k).re = Real.cos ((2*(k.val : ℝ)-1)*(Real.pi/n)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have he : 2*Real.pi*Complex.I*(k.val : ℂ)/(n : ℂ) =
      (((2*(k.val : ℝ)*(Real.pi/n) : ℝ) : ℂ)*Complex.I) := by
    push_cast
    ring
  rw [he]
  have hangle : Real.pi/n - 2*(k.val : ℝ)*(Real.pi/n) =
      -((2*(k.val : ℝ)-1)*(Real.pi/n)) := by ring
  simpa only [Complex.ofReal_one, one_mul, hangle, Real.cos_neg] using
    (Ray.rotated_ray_real (Real.pi/n) (2*(k.val : ℝ)*(Real.pi/n)) 1)
private theorem weighted_edge_bound {ι : Type*} [Fintype ι] (w c : ι → ℝ) (M : ℝ) (hw : ∀ k, 0 ≤ w k) (hwsum : ∑ k, w k = 1) (hc : ∀ k, c k ≤ M) : (∑ k, c k*w k) ≤ M ∧ ((∑ k, c k*w k) = M ↔ ∀ k, c k < M → w k = 0) := by
  classical
  have hgap : ∀ k, 0 ≤ (M-c k)*w k := fun k => mul_nonneg (sub_nonneg.mpr (hc k)) (hw k)
  have hsum : (∑ k, (M-c k)*w k) = M-(∑ k,c k*w k) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hwsum, mul_one]
  have hge : 0 ≤ ∑ k, (M-c k)*w k := Finset.sum_nonneg fun k _ => hgap k
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq k hlt
    have hz : (∑ k, (M-c k)*w k) = 0 := by rw [hsum,heq,sub_self]
    have hzk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hgap k)).mp hz k (Finset.mem_univ k)
    exact (mul_eq_zero.mp hzk).resolve_left (sub_pos.mpr hlt).ne'
  · intro h
    have hz : (∑ k, (M-c k)*w k) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rcases (hc k).eq_or_lt with heq | hlt
      · rw [heq,sub_self,zero_mul]
      · rw [h k hlt,mul_zero]
    linarith
private theorem rotated_mean_real {n : ℕ} [NeZero n] (f : ZMod n → Fin 2 → ℂ) (E : ℂ) : (E * ∑ k, ZMod.stdAddChar k * ((fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) : ℂ)).re = ∑ k, (E * ZMod.stdAddChar k).re * (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) := by
  simp only [Finset.mul_sum, Complex.re_sum, ← mul_assoc, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
private theorem fourier_exposed_edge {n : ℕ} [NeZero n] (hn : 3 ≤ n) (f : ZMod n → Fin 2 → ℂ) (hsum : ∑ k, (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) = 1) : (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ∑ k, ZMod.stdAddChar k * ((fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) : ℂ)).re ≤ Real.cos (Real.pi/n) ∧ ((Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ∑ k, ZMod.stdAddChar k * ((fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) : ℂ)).re = Real.cos (Real.pi/n) → ∀ k, k ≠ 0 → k ≠ 1 → f k = 0) := by
  have hc (k : ZMod n) :
      (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ZMod.stdAddChar k).re ≤
        Real.cos (Real.pi/n) := by
    rw [root_rotated_real]; exact (Polygon.polygon_cosine_edge hn ⟨k.val,k.val_lt⟩).1
  have h := weighted_edge_bound (fun k => (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k))
    (fun k => (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ZMod.stdAddChar k).re)
    (Real.cos (Real.pi/n)) (fun k => energy_nonneg (f k)) hsum hc
  simp only [rotated_mean_real] at ⊢
  refine ⟨h.1, ?_⟩
  intro heq k hk0 hk1
  apply (energy_zero_iff (f k)).mp
  apply h.2.mp heq k
  have hneq :
      (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ZMod.stdAddChar k).re ≠
        Real.cos (Real.pi/n) := by
    intro he; rw [root_rotated_real] at he
    rcases (Polygon.polygon_cosine_edge hn ⟨k.val,k.val_lt⟩).2.mp he with he0 | he1
    · apply hk0
      have hh := ZMod.natCast_zmod_val k
      change k.val = 0 at he0
      rw [he0,Nat.cast_zero] at hh
      exact hh.symm
    · apply hk1
      have hh := ZMod.natCast_zmod_val k
      change k.val = 1 at he1
      rw [he1,Nat.cast_one] at hh
      exact hh.symm
  exact lt_of_le_of_ne (hc k) hneq
private theorem synthesis_two_modes {n : ℕ} [NeZero n] (hn : 3 ≤ n) (f : ZMod n → Fin 2 → ℂ) (hf : ∀ k, k ≠ 0 → k ≠ 1 → f k = 0) (j : ZMod n) : ZMod.dft f (-j) = f 0 + ZMod.stdAddChar j • f 1 := by
  classical
  have hn1 : n ≠ 1 := by omega
  have hne : (0 : ZMod n) ≠ 1 := by
    intro hh
    have he := congrArg ZMod.val hh
    simpa [ZMod.val_zero,ZMod.val_one'' hn1] using he
  simp only [ZMod.dft_apply, mul_neg, neg_neg, mul_comm]
  calc
    (∑ k, ZMod.stdAddChar (j*k) • f k) =
        ∑ k ∈ ({0,1} : Finset (ZMod n)), ZMod.stdAddChar (j*k) • f k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk; simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
      rw [hf k hk.1 hk.2,smul_zero]
    _ = _ := by simp [hne]
private theorem coefficient_energy_sum {n : ℕ} [NeZero n] (u : ZMod n → Fin 2 → ℂ) (hu : ∀ j, star (u j) ⬝ᵥ u j = 1) : ∑ k, (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (((n : ℂ)⁻¹ • ZMod.dft u k)) = 1 := by
  have h := parseval_synthesis ((fun k => (n : ℂ)⁻¹ • ZMod.dft u k)) ((fun k => (n : ℂ)⁻¹ • ZMod.dft u k))
  simp_rw [reconstruct,hu] at h
  have hreal := congrArg Complex.re h
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one,
    Complex.natCast_re, Complex.mul_re, Complex.natCast_im, zero_mul,
    Complex.re_sum, sub_zero] at hreal
  change (n : ℝ) = (n : ℝ) * (∑ k, (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (((n : ℂ)⁻¹ • ZMod.dft u k))) at hreal
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  nlinarith
private theorem coefficient_neighbor_mean {n : ℕ} [NeZero n] (u : ZMod n → Fin 2 → ℂ) : (n : ℂ)⁻¹ * (∑ j, star (u j) ⬝ᵥ u (j+1)) = ∑ k, ZMod.stdAddChar k * ((fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (((n : ℂ)⁻¹ • ZMod.dft u k)) : ℂ) := by
  have h := neighbor_sum_synthesis ((fun k => (n : ℂ)⁻¹ • ZMod.dft u k))
  simp_rw [reconstruct] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (NeZero.ne (n : ℂ)), one_mul]
private theorem exposed_edge_two_mode_orthogonal {n : ℕ} [NeZero n] (hn : 3 ≤ n) (u : ZMod n → Fin 2 → ℂ) (hu : ∀ j, star (u j) ⬝ᵥ u j = 1) (heq : (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ((n : ℂ)⁻¹ * ∑ j, star (u j) ⬝ᵥ u (j+1))).re = Real.cos (Real.pi/n)) : ∃ p q : Fin 2 → ℂ, (∀ j, u j = p + ZMod.stdAddChar j • q) ∧ star p ⬝ᵥ p + star q ⬝ᵥ q = 1 ∧ star p ⬝ᵥ q = 0 := by
  classical
  let f := (fun k => (n : ℂ)⁻¹ • ZMod.dft u k)
  have hsum : ∑ k, (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) = 1 := coefficient_energy_sum u hu
  rw [coefficient_neighbor_mean] at heq
  have hf : ∀ k, k ≠ 0 → k ≠ 1 → f k = 0 :=
    (fourier_exposed_edge hn f hsum).2 heq
  have hrep (j : ZMod n) : u j = f 0 + ZMod.stdAddChar j • f 1 := by
    rw [← reconstruct u j]; exact synthesis_two_modes hn f hf j
  have hn1 : n ≠ 1 := by omega
  have hne : (0 : ZMod n) ≠ 1 := by
    intro hh
    have he := congrArg ZMod.val hh
    simpa [ZMod.val_zero,ZMod.val_one'' hn1] using he
  have hsum2 : (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f 0) + (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f 1) = 1 := by
    have hreduce : (∑ k, (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k)) = (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f 0)+(fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f 1) := by
      calc
        _ = ∑ k ∈ ({0,1} : Finset (ZMod n)), (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) (f k) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro k _ hk; simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
          rw [hf k hk.1 hk.2]; simp
        _ = _ := by simp [hne]
    rw [← hreduce]; exact hsum
  have hcomplex : star (f 0) ⬝ᵥ f 0 + star (f 1) ⬝ᵥ f 1 = 1 := by
    rw [self_dot_eq_energy,self_dot_eq_energy,← Complex.ofReal_add,hsum2,Complex.ofReal_one]
  have hnorm : ‖ZMod.stdAddChar (1 : ZMod n)‖ = 1 := by
    simpa only [map_one] using (phase_norm (n := n) (1 : Fin n))
  have hzi : (ZMod.stdAddChar (1 : ZMod n)).im ≠ 0 := by
    simpa only [map_one] using (phase_one_im_pos (n := n) hn).ne'
  have hzero : star (f 0+f 1) ⬝ᵥ (f 0+f 1) = 1 := by
    have hh := hu 0
    simpa only [hrep,AddChar.map_zero_eq_one,one_smul] using hh
  have hone : star (f 0+ZMod.stdAddChar (1 : ZMod n) • f 1) ⬝ᵥ
      (f 0+ZMod.stdAddChar (1 : ZMod n) • f 1) = 1 := by simpa only [hrep] using hu 1
  exact ⟨f 0,f 1,hrep,hcomplex,
    Rigidity.cross_zero_of_two_unit_samples (f 0) (f 1)
      (ZMod.stdAddChar (1 : ZMod n)) hnorm hzi hcomplex hzero hone⟩
private theorem lift_neighbor_sum {n : ℕ} [NeZero n] (u : Fin n → Fin 2 → ℂ) : (∑ j : ZMod n, star ((u ∘ (ZMod.finEquiv n).symm) j) ⬝ᵥ (u ∘ (ZMod.finEquiv n).symm) (j+1)) = ∑ j : Fin n, star (u j) ⬝ᵥ u (j+1) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl
private theorem finite_exposed_edge {n : ℕ} [NeZero n] (hn : 3 ≤ n) (u : Fin n → Fin 2 → ℂ) (hu : ∀ j, star (u j) ⬝ᵥ u j = 1) : (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ((n : ℂ)⁻¹ * ∑ j, star (u j) ⬝ᵥ u (j+1))).re ≤ Real.cos (Real.pi/n) := by
  have h := (fourier_exposed_edge hn ((fun u k => (n : ℂ)⁻¹ • ZMod.dft u k) ((u ∘ (ZMod.finEquiv n).symm)))
    (coefficient_energy_sum ((u ∘ (ZMod.finEquiv n).symm)) (fun j => hu _))).1
  rw [← coefficient_neighbor_mean,lift_neighbor_sum] at h
  exact h
private theorem finite_two_mode_orthogonal {n : ℕ} [NeZero n] (hn : 3 ≤ n) (u : Fin n → Fin 2 → ℂ) (hu : ∀ j, star (u j) ⬝ᵥ u j = 1) (heq : (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) * ((n : ℂ)⁻¹ * ∑ j, star (u j) ⬝ᵥ u (j+1))).re = Real.cos (Real.pi/n)) : ∃ p q : Fin 2 → ℂ, (∀ j, u j = p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j • q) ∧ star p ⬝ᵥ p + star q ⬝ᵥ q = 1 ∧ star p ⬝ᵥ q = 0 := by
  have hZ : (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I) *
      ((n : ℂ)⁻¹ * ∑ j, star ((u ∘ (ZMod.finEquiv n).symm) j) ⬝ᵥ (u ∘ (ZMod.finEquiv n).symm) (j+1))).re = Real.cos (Real.pi/n) := by
    rwa [lift_neighbor_sum]
  obtain ⟨p,q,hrep,hsum,horth⟩ := exposed_edge_two_mode_orthogonal hn ((u ∘ (ZMod.finEquiv n).symm))
    (fun j => hu _) hZ
  refine ⟨p,q,?_,hsum,horth⟩
  intro j; simpa only [Function.comp_apply,RingEquiv.symm_apply_apply] using
    hrep (ZMod.finEquiv n j)
private theorem two_mode_overlap {n : ℕ} [NeZero n] (p q : Fin 2 → ℂ) (hpq : star p ⬝ᵥ q = 0) (j : Fin n) : star (p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j • q) ⬝ᵥ (p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (j+1) • q) = star p ⬝ᵥ p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n)*(star q ⬝ᵥ q) := by
  have hqp : star q ⬝ᵥ p = 0 := by rw [star_dotProduct,hpq,star_zero]
  simp only [star_add,star_smul,add_dotProduct,dotProduct_add,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,hpq,hqp,mul_zero,zero_add,add_zero]
  calc
    _ = star p ⬝ᵥ p + (star ((fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j)*(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (j+1))*(star q ⬝ᵥ q) := by ring
    _ = _ := by rw [phase_next]
private theorem two_mode_mean {n : ℕ} [NeZero n] (p q : Fin 2 → ℂ) (hpq : star p ⬝ᵥ q = 0) : (n : ℂ)⁻¹*(∑ j : Fin n, star (p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j • q) ⬝ᵥ (p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (j+1) • q)) = star p ⬝ᵥ p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n)*(star q ⬝ᵥ q) := by
  simp only [two_mode_overlap p q hpq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (NeZero.ne (n : ℂ)),one_mul]
private theorem weight_identifiable (s t : ℝ) (ω : ℂ) (hω : ω ≠ 1) (h : (1-(s : ℂ))+(s : ℂ)*ω = (1-(t : ℂ))+(t : ℂ)*ω) : s = t := by
  have hh : ((s : ℂ)-(t : ℂ))*(ω-1) = 0 := by linear_combination h
  have hst : (s : ℂ)-(t : ℂ) = 0 :=
    (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hω)
  exact_mod_cast sub_eq_zero.mp hst
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Fourier
namespace D5.S3.Quantum.Information.BargmannImaginaryMaximizers
open Character _root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Fourier
private noncomputable def cycleWeight (v u : Fin 2 → ℂ) : List (Fin 2 → ℂ) → ℂ
  | [] => star u ⬝ᵥ v
  | w :: L => (star u ⬝ᵥ w) * cycleWeight v w L
private theorem trace_rank_one_chain (v u : Fin 2 → ℂ) (L : List (Fin 2 → ℂ)) : (Matrix.vecMulVec v (star u) * (L.map (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ))).prod).trace = cycleWeight v u L := by
  induction L generalizing u with
  | nil => simp [cycleWeight, Matrix.trace_vecMulVec, dotProduct_comm]
  | cons w L ih =>
    simp only [List.map_cons, List.prod_cons, cycleWeight]
    rw [← mul_assoc]; simp only [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
    rw [smul_mul_assoc, Matrix.trace_smul]; exact congrArg ((star u ⬝ᵥ w) * ·) (ih w)
private theorem trace_pure_chain (v : Fin 2 → ℂ) (L : List (Fin 2 → ℂ)) : (((v :: L).map (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ))).prod).trace = cycleWeight v v L := by
  exact trace_rank_one_chain v v L
private theorem cycle_weight_ofFn (n : ℕ) (v : Fin 2 → ℂ) (Ψ : Fin (n+1) → Fin 2 → ℂ) : cycleWeight v (Ψ 0) (List.ofFn fun j : Fin n => Ψ j.succ) = (∏ j : Fin n, star (Ψ j.castSucc) ⬝ᵥ Ψ j.succ) * (star (Ψ (Fin.last n)) ⬝ᵥ v) := by
  induction n with
  | zero => simp [cycleWeight]
  | succ n ih =>
    rw [List.ofFn_succ, cycleWeight, Fin.prod_univ_succ]
    have hh := ih (fun j => Ψ j.succ)
    simpa only [Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last, mul_assoc] using
      congrArg ((star (Ψ 0) ⬝ᵥ Ψ 1) * ·) hh
private theorem bargmann_path_product (n : ℕ) (Ψ : Fin (n+1) → Fin 2 → ℂ) : bargmann Ψ = (∏ j : Fin n, star (Ψ j.castSucc) ⬝ᵥ Ψ j.succ) * (star (Ψ (Fin.last n)) ⬝ᵥ Ψ 0) := by
  unfold bargmann
  rw [List.ofFn_succ]; rw [show ((fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) (Ψ 0) :: List.ofFn fun j : Fin n => (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) (Ψ j.succ)) =
      (Ψ 0 :: List.ofFn fun j : Fin n => Ψ j.succ).map (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) by
        simp only [List.map_cons,List.map_ofFn,Function.comp_def]]
  rw [trace_pure_chain, cycle_weight_ofFn]
private theorem bargmann_eq_overlap_product {n : ℕ} [NeZero n] (Ψ : Fin n → Fin 2 → ℂ) : bargmann Ψ = ∏ j : Fin n, star (Ψ j) ⬝ᵥ Ψ (j+1) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    rw [bargmann_path_product,Fin.prod_univ_castSucc]; simp only [Fin.coeSucc_eq_succ,Fin.last_add_one]
private theorem bargmann_constant_overlap {n : ℕ} [NeZero n] (Ψ : Fin n → Fin 2 → ℂ) (c : ℂ) (hc : ∀ j : Fin n, star (Ψ j) ⬝ᵥ Ψ (j+1) = c) : bargmann Ψ = c^n := by
  rw [bargmann_eq_overlap_product]; simp only [hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
private theorem pure_state_phase (v : Fin 2 → ℂ) (η : ℂ) (hη : ‖η‖ = 1) : (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) (η • v) = (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) v := by
  have hh : η * star η = 1 := by
    simpa only [Complex.star_def, hη, one_pow, Complex.ofReal_one] using Complex.mul_conj' η
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul]
  calc η * v i * (star (v j) * star η) = (η * star η) * (v i * star (v j)) := by ring
       _ = v i * star (v j) := by rw [hh, one_mul]
private theorem bargmann_phase {n : ℕ} (v : Fin n → Fin 2 → ℂ) (η : Fin n → ℂ) (hη : ∀ j, ‖η j‖ = 1) : bargmann (fun j => η j • v j) = bargmann v := by
  simp only [bargmann, pure_state_phase _ _ (hη _)]
private theorem pure_state_unitary (U : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) (U *ᵥ v) = U * (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) v * Uᴴ := by
  simp only [mul_vecMulVec, vecMulVec_mul, star_mulVec]
private theorem list_prod_unitary (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (L : List (Matrix (Fin 2) (Fin 2) ℂ)) : (L.map (fun M => U * M * Uᴴ)).prod = U * L.prod * Uᴴ := by
  let f := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) ⟨U, hU⟩
  have hf : (fun M : Matrix (Fin 2) (Fin 2) ℂ => U * M * Uᴴ) =
      (f : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) := by
    funext M
    simp only [f, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rw [hf, List.prod_hom]
  simp only [f, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
private theorem bargmann_unitary {n : ℕ} (v : Fin n → Fin 2 → ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) : bargmann (fun j => U *ᵥ v j) = bargmann v := by
  have hright : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  simp only [bargmann, pure_state_unitary]
  rw [show (List.ofFn fun j => U * (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) (v j) * Uᴴ) =
      (List.ofFn fun j => (fun ψ : Fin 2 → ℂ => Matrix.vecMulVec ψ (star ψ)) (v j)).map (fun M => U * M * Uᴴ) by
      simp only [List.map_ofFn]; rfl]
  rw [list_prod_unitary U hU, Matrix.trace_mul_cycle, hright, one_mul]
private noncomputable def weight (n : ℕ) : ℝ :=
  (1 - Real.tan (Real.pi / (2 * (n - 1 : ℝ))) / Real.tan (Real.pi / n)) / 2
private theorem weight_bounds {n : ℕ} (hn : 3 ≤ n) : 0 < weight n ∧ weight n < 1/2 := by
  have h := Scalar.scalar_angles hn
  have ha : 0 < Real.pi/(n : ℝ) := lt_trans h.1 h.2.1
  have hbhalf : Real.pi/(2*((n : ℝ)-1)) < Real.pi/2 := lt_trans h.2.1 h.2.2
  have htana := Real.tan_pos_of_pos_of_lt_pi_div_two ha h.2.2
  have htanb := Real.tan_pos_of_pos_of_lt_pi_div_two h.1 hbhalf
  have htanlt := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two h.1.le h.2.2 h.2.1
  have hratio : 0 < Real.tan (Real.pi/(2*((n : ℝ)-1))) / Real.tan (Real.pi/n) :=
    div_pos htanb htana
  have hratiolt : Real.tan (Real.pi/(2*((n : ℝ)-1))) / Real.tan (Real.pi/n) < 1 :=
    (div_lt_one htana).mpr htanlt
  unfold weight
  constructor <;> linarith
private theorem tau_pos {n : ℕ} (hn : 3 ≤ n) : 0 < tau n := by
  have h := Scalar.scalar_angles hn
  have hcosa := Real.cos_pos_of_mem_Ioo ⟨by linarith, h.2.2⟩
  have hcosb := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], lt_trans h.2.1 h.2.2⟩
  exact div_pos (pow_pos hcosa _) (pow_pos hcosb _)
private theorem maximizer_eq_latitude {n : ℕ} [NeZero n] (j : Fin n) : maximizer n j = Latitude.latitude (weight n) ((fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j) := by
  rw [phase_exp]; rfl
private theorem maximizer_overlap {n : ℕ} [NeZero n] (hn : 3 ≤ n) (j : Fin n) : star (maximizer n j) ⬝ᵥ maximizer n (j+1) = (↑(Real.cos (Real.pi/n)/Real.cos (Real.pi/(2*((n : ℝ)-1)))) : ℂ) * Complex.exp ((((Real.pi/n-Real.pi/(2*((n : ℝ)-1))) : ℝ) : ℂ)*Complex.I) := by
  have ht := weight_bounds hn
  have ha := Scalar.scalar_angles hn
  have hsa : Real.sin (Real.pi/n) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hcb : Real.cos (Real.pi/(2*((n : ℝ)-1))) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],lt_trans ha.2.1 ha.2.2⟩).ne'
  rw [maximizer_eq_latitude,maximizer_eq_latitude,
    Latitude.latitude_dot (weight n) ht.1.le (by linarith)]
  rw [mul_assoc,phase_next,phase_one hn]; simpa only [weight,Complex.ofReal_sub,Complex.ofReal_one] using
    (Family.latitude_overlap_polar (Real.pi/n)
      (Real.pi/(2*((n : ℝ)-1))) hsa hcb)
private theorem maximizer_attains {n : ℕ} [NeZero n] (hn : 3 ≤ n) : (bargmann (maximizer n)).im = tau n := by
  let a := Real.pi/(n : ℝ)
  let b := Real.pi/(2*((n : ℝ)-1))
  have hnR : (3 : ℝ) ≤ n := by exact Nat.ofNat_le_cast.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hd : (n : ℝ)-1 ≠ 0 := by linarith
  have ha := Scalar.scalar_angles hn
  have hc : Real.cos b ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by change -(Real.pi/2) < Real.pi/(2*((n : ℝ)-1)); linarith [Real.pi_pos],lt_trans ha.2.1 ha.2.2⟩).ne'
  have hangle : (n : ℝ)*(a-b) = Real.pi/2-b := by
    dsimp [a,b]
    field_simp [hn0,hd]
    <;> ring
  rw [bargmann_constant_overlap _ _ (maximizer_overlap hn)]; rw [mul_pow,← Complex.exp_nat_mul]
  have he : (n : ℂ)*(((a-b : ℝ) : ℂ)*Complex.I) =
      (((Real.pi/2-b : ℝ) : ℂ)*Complex.I) := by
    rw [← mul_assoc,← Complex.ofReal_natCast,← Complex.ofReal_mul, hangle]
  change (((((Real.cos a/Real.cos b : ℝ) : ℂ))^n)*
    Complex.exp ((n : ℂ)*(((a-b : ℝ) : ℂ)*Complex.I))).im = tau n
  rw [he,← Complex.ofReal_pow]; simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,
    add_zero,Complex.exp_ofReal_mul_I_im,Real.sin_pi_div_two_sub]
  unfold tau
  change (Real.cos a/Real.cos b)^n*Real.cos b = Real.cos a^n/Real.cos b^(n-1)
  have hpow : Real.cos b^n = Real.cos b^(n-1)*Real.cos b := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [div_pow,hpow]; field_simp
private theorem orbit_implies_maximum {n : ℕ} [NeZero n] (hn : 3 ≤ n) (Ψ : Fin n → Fin 2 → ℂ) (horbit : ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ η : Fin n → ℂ, (∀ j, ‖η j‖ = 1) ∧ ∀ j, Ψ j = η j • (U *ᵥ maximizer n j)) : (bargmann Ψ).im = tau n := by
  obtain ⟨U,hU,η,hη,hΨ⟩ := horbit
  have hΨfun : Ψ = fun j => η j • (U *ᵥ maximizer n j) := funext hΨ
  rw [hΨfun,bargmann_phase _ η hη,bargmann_unitary _ U hU]; exact maximizer_attains hn
private theorem maximum_implies_orbit {n : ℕ} [NeZero n] (hn : 3 ≤ n) (Ψ : Fin n → Fin 2 → ℂ) (hΨ : ∀ j, (star (Ψ j) ⬝ᵥ Ψ j = 1)) (hmax : (bargmann Ψ).im = tau n) : ∃ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∃ η : Fin n → ℂ, (∀ j, ‖η j‖ = 1) ∧ ∀ j, Ψ j = η j • (U *ᵥ maximizer n j) := by
  classical
  let g : Fin n → ℂ := fun j => star (Ψ j) ⬝ᵥ Ψ (j+1)
  let φ := (bargmann Ψ).arg/(n : ℝ)
  let R : ℝ := (∑ j, ‖g j‖)/(n : ℝ)
  have hn0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hprodδ : (∏ j,g j) = bargmann Ψ := (bargmann_eq_overlap_product Ψ).symm
  have himpos : 0 < (bargmann Ψ).im := by rw [hmax];exact tau_pos hn
  have hδne : bargmann Ψ ≠ 0 := by intro hh;simpa [hh] using himpos
  have hg (j : Fin n) : g j ≠ 0 := by
    intro hh
    have hp : (∏ j,g j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hh
    exact hδne (hprodδ.symm.trans hp)
  have harg := Argument.positive_argument (Nat.pos_of_ne_zero hn0) (bargmann Ψ) himpos
  have hφ : φ ∈ Set.Ioo 0 (Real.pi/n) := harg.1
  have hprod : ‖bargmann Ψ‖ ≤ R^n := by
    have hh := AMGM.product_le_mean_pow hn0 (fun j => ‖g j‖) (fun j => norm_nonneg _)
    have hnorm : ‖bargmann Ψ‖ = ∏ j, ‖g j‖ := by rw [← hprodδ,norm_prod]
    rwa [← hnorm] at hh
  obtain ⟨ξ,hξ,hξedge⟩ := Gauge.cyclic_phase_equalization g hg
  rw [hprodδ] at hξedge
  let u : Fin n → Fin 2 → ℂ := fun j => ξ j • Ψ j
  have hu (j : Fin n) : star (u j) ⬝ᵥ u j = 1 :=
    Ray.phase_preserves_unit (Ψ j) (hΨ j) (ξ j) (hξ j)
  have huedge (j : Fin n) : star (u j) ⬝ᵥ u (j+1) =
      Complex.exp ((φ : ℂ)*Complex.I)*(‖g j‖ : ℂ) := by
    simp only [u,star_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    calc
      _ = (star (ξ j)*ξ (j+1))*g j := by dsimp [g];ring
      _ = _ := hξedge j
  have hmean : (n : ℂ)⁻¹*(∑ j,star (u j) ⬝ᵥ u (j+1)) =
      (R : ℂ)*Complex.exp ((φ : ℂ)*Complex.I) := by
    simp_rw [huedge]
    exact Ray.mean_ray _ _
  have hR0 : 0 ≤ R := div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnR.le
  have hedge := Fourier.finite_exposed_edge hn u hu
  rw [hmean,Ray.rotated_ray_real] at hedge
  have hmaxP : ‖bargmann Ψ‖*Real.sin ((n : ℝ)*φ) =
      Real.cos (Real.pi/n)^n/Real.cos (Real.pi/(2*((n : ℝ)-1)))^(n-1) := by
    change _ = tau n
    rw [harg.2,hmax]
  obtain ⟨hφeq,hReq⟩ := Scalar.scalar_saturation hn φ ‖bargmann Ψ‖ R
    hφ hR0 hprod hedge hmaxP
  have ha := Scalar.scalar_angles hn
  have hcb : Real.cos (Real.pi/(2*((n : ℝ)-1))) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],lt_trans ha.2.1 ha.2.2⟩).ne'
  have heq : (Complex.exp (((-(Real.pi/n) : ℝ) : ℂ)*Complex.I)*
      ((n : ℂ)⁻¹*∑ j,star (u j) ⬝ᵥ u (j+1))).re = Real.cos (Real.pi/n) := by
    rw [hmean,Ray.rotated_ray_real,hφeq,hReq,sub_sub_cancel]; exact div_mul_cancel₀ _ hcb
  obtain ⟨p,q,hrep,hsum,horth⟩ := Fourier.finite_two_mode_orthogonal hn u hu heq
  let s := (fun v : Fin 2 → ℂ => (star v ⬝ᵥ v).re) q
  have hqc : star q ⬝ᵥ q = (s : ℂ) := self_dot_eq_energy q
  have hpc : star p ⬝ᵥ p = ((1-s : ℝ) : ℂ) := by
    have hh : star p ⬝ᵥ p = 1-star q ⬝ᵥ q := eq_sub_of_add_eq hsum
    rw [hh,hqc]
    push_cast
    rfl
  have hmean2 : (n : ℂ)⁻¹*(∑ j,star (u j) ⬝ᵥ u (j+1)) =
      star p ⬝ᵥ p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n)*(star q ⬝ᵥ q) := by
    simp_rw [hrep]
    exact Fourier.two_mode_mean p q horth
  have hsa : Real.sin (Real.pi/n) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hpolar : (1-(weight n : ℂ))+(weight n : ℂ)*(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n) =
      (↑(Real.cos (Real.pi/n)/Real.cos (Real.pi/(2*((n : ℝ)-1)))) : ℂ)*
        Complex.exp (((Real.pi/n-Real.pi/(2*((n : ℝ)-1)) : ℝ) : ℂ)*Complex.I) := by
    rw [phase_one hn]; exact Family.latitude_overlap_polar (Real.pi/n)
      (Real.pi/(2*((n : ℝ)-1))) hsa hcb
  have hweights : (1-(s : ℂ))+(s : ℂ)*(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n) =
      (1-(weight n : ℂ))+(weight n : ℂ)*(fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n) := by
    calc
      _ = star p ⬝ᵥ p + (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n)*(star q ⬝ᵥ q) := by
        rw [hpc,hqc];push_cast;ring
      _ = (n : ℂ)⁻¹*(∑ j,star (u j) ⬝ᵥ u (j+1)) := hmean2.symm
      _ = _ := by rw [hmean,hReq,hφeq];exact hpolar.symm
  have hω : (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) (1 : Fin n) ≠ 1 := by
    intro hh
    have hi := phase_one_im_pos hn
    rw [hh,Complex.one_im] at hi
    linarith
  have hst : s = weight n := Fourier.weight_identifiable s (weight n) _ hω hweights
  rw [hst] at hpc hqc
  have ht := weight_bounds hn
  obtain ⟨U,hU,hUrep⟩ := Latitude.two_mode_unitary p q (fun j : Fin n => (fun j => ZMod.stdAddChar (ZMod.finEquiv _ j)) j) (weight n)
    ht.1.le (by linarith) hpc hqc horth
  have huU (j : Fin n) : u j = U *ᵥ maximizer n j := by
    rw [hrep j,hUrep j,maximizer_eq_latitude]
  refine ⟨U,hU,fun j => star (ξ j),?_,?_⟩
  · intro j
    simpa only [norm_star] using hξ j
  · intro j
    have hunit : star (ξ j)*ξ j = 1 := by
      simpa only [Complex.star_def,hξ j,one_pow,Complex.ofReal_one] using Complex.conj_mul' (ξ j)
    calc
      Ψ j = (star (ξ j)*ξ j) • Ψ j := by rw [hunit,one_smul]
      _ = star (ξ j) • u j := by rw [smul_smul]
      _ = star (ξ j) • (U *ᵥ maximizer n j) := by rw [huU j]
theorem result : claim := by
  intro n hn Ψ hΨ
  letI : NeZero n := ⟨by omega⟩
  exact ⟨maximum_implies_orbit hn Ψ hΨ,orbit_implies_maximum hn Ψ⟩
end D5.S3.Quantum.Information.BargmannImaginaryMaximizers
