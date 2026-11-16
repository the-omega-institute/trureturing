/- GID: D5/S3/Quantum/Matrix/AsynchronousTwoBlockRadius
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/AsynchronousTwoBlockRadius
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact two-block delay radius with arbitrary independent history length. -/

import D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The radius follows from the actual history spectrum, including the zero-delay specialization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs (Vtx)
open D5.S3.Quantum.Matrix.AsynchronousIterationSpectralRadiusRefutation
open D5.S3.Quantum.Matrix.AsynchronousTwoBlockSpectrum
open scoped ENNReal NNReal Matrix.Norms.Operator

namespace D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius

private theorem synchronous_spectrum_iff {m n : ℕ}
    (U : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (z : ℂ) (hz : z ≠ 0) :
    z ∈ spectrum ℂ ((zeroDiagonal U V).map (algebraMap ℝ ℂ)) ↔
      z^2 ∈ spectrum ℂ ((U*V).map (algebraMap ℝ ℂ)) := by
  classical
  let e : Vtx (![m,n] : Fin 2 → ℕ) ≃ Fin 1 × Vtx (![m,n] : Fin 2 → ℕ) := {
    toFun := fun p => (0,p)
    invFun := Prod.snd
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨r,p⟩; have h : r=0 := Subsingleton.elim _ _; subst r; rfl }
  have hmatrix : (asyncMatrix (zeroDiagonal U V) !![0,0; 0,0] 0).map (algebraMap ℝ ℂ) =
      Matrix.reindexAlgEquiv ℂ ℂ e ((zeroDiagonal U V).map (algebraMap ℝ ℂ)) := by
    ext ⟨r,p⟩ ⟨s,q⟩
    have hr : r=0 := by apply Fin.ext; have := r.isLt; simp only [Nat.zero_add] at this; omega
    have hs : s=0 := by apply Fin.ext; have := s.isLt; simp only [Nat.zero_add] at this; omega
    subst r; subst s
    have hd (i j : Fin 2) : (!![0,0; 0,0] : Matrix (Fin 2) (Fin 2) ℕ) i j = 0 := by
      fin_cases i <;> fin_cases j <;> rfl
    simp [asyncMatrix, Matrix.map_apply, Matrix.reindex_apply, e,hd]
  have h := nonzero_spectrum_iff (a:=0) (b:=0) (K:=0) U V (by omega) (by omega) z hz
  rw [hmatrix, AlgEquiv.spectrum_eq] at h
  simpa using h

/-- The exact radius, original power bound, and strict stability for every admissible history. -/
theorem two_block_radius {m n a b k K : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (U : Matrix (Fin m) (Fin n) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hak : a ≤ k) (hbk : b ≤ k)
    (haK : a ≤ K) (hbK : b ≤ K)
    (lambda : ℝ) (hl0 : 0 < lambda) (hl1 : lambda < 1)
    (hradius : radius (zeroDiagonal U V) = ENNReal.ofReal lambda) :
    radius (asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K) =
        ENNReal.ofReal (lambda ^ ((2:ℝ) / (a+b+2:ℕ))) ∧
      ENNReal.ofReal (lambda ^ ((2:ℝ) / (a+b+2:ℕ))) ≤
        ENNReal.ofReal (lambda ^ ((1:ℝ) / ((k:ℝ)+1))) ∧
      ENNReal.ofReal (lambda ^ ((1:ℝ) / ((k:ℝ)+1))) < 1 := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : Nonempty (Vtx (![m,n] : Fin 2 → ℕ)) := ⟨⟨0,(⟨0,hm⟩ : Fin m)⟩⟩
  let M := (zeroDiagonal U V).map (algebraMap ℝ ℂ)
  let B := (asyncMatrix (zeroDiagonal U V) !![0,b; a,0] K).map (algebraMap ℝ ℂ)
  let L : ℕ := a+b+2
  let R : ℝ := lambda ^ ((2:ℝ)/(L:ℝ))
  have hL : 0 < L := by dsimp [L]; omega
  have hLc : (0:ℝ) < L := by exact_mod_cast hL
  have hR : 0 ≤ R := Real.rpow_nonneg hl0.le _
  have hRpow : R^L = lambda^2 := by
    dsimp [R]
    rw [←Real.rpow_natCast _ L, ←Real.rpow_mul hl0.le,
      div_mul_cancel₀ _ (ne_of_gt hLc), Real.rpow_two]
  have norm_le (w : ℂ) (hw : w ∈ spectrum ℂ M) : ‖w‖ ≤ lambda := by
    have h : (‖w‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal lambda := by
      rw [←hradius, radius, spectralRadius_eq_of_unital]
      exact le_iSup₂ (f:=fun w (_ : w ∈ spectrum ℂ M) => (‖w‖₊ : ℝ≥0∞)) w hw
    rw [←ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff hl0.le).mp h
  have hupper : spectralRadius ℂ B ≤ ENNReal.ofReal R := by
    rw [spectralRadius_eq_of_unital]
    apply iSup₂_le
    intro z hzspec
    by_cases hz : z=0
    · subst z; simp
    have hproduct := (nonzero_spectrum_iff U V haK hbK z hz).mp hzspec
    obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (z^L) (by norm_num : 0<2)
    have hwne : w ≠ 0 := by
      intro hwz; rw [hwz,zero_pow (by norm_num)] at hw
      exact (pow_ne_zero L hz) hw.symm
    have hwmem : w ∈ spectrum ℂ M :=
      (synchronous_spectrum_iff U V w hwne).mpr (by simpa [L,hw] using hproduct)
    have hwpow : ‖w‖^2 = ‖z‖^L := by
      rw [←norm_pow,hw,norm_pow]
    have hzle : ‖z‖ ≤ R := by
      apply le_of_pow_le_pow_left₀ (ne_of_gt hL) hR
      rw [hRpow,←hwpow]
      exact pow_le_pow_left₀ (norm_nonneg w) (norm_le w hwmem) 2
    rw [←ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hzle
  obtain ⟨w,hw,hwmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ M)
  have hwlambda : ‖w‖ = lambda := by
    have h : (‖w‖₊ : ℝ≥0∞) = ENNReal.ofReal lambda := hwmax.trans hradius
    rw [←ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg w) hl0.le).mp h
  have hwne : w ≠ 0 := by intro h; rw [h,norm_zero] at hwlambda; linarith
  have hproduct := (synchronous_spectrum_iff U V w hwne).mp hw
  obtain ⟨z,hzpow⟩ := IsAlgClosed.exists_pow_nat_eq (w^2) hL
  have hzne : z ≠ 0 := by
    intro h; rw [h,zero_pow (ne_of_gt hL)] at hzpow
    exact (pow_ne_zero 2 hwne) hzpow.symm
  have hzmem : z ∈ spectrum ℂ B :=
    (nonzero_spectrum_iff U V haK hbK z hzne).mpr (by simpa [L,hzpow] using hproduct)
  have hzR : ‖z‖ = R := by
    apply (pow_left_inj₀ (norm_nonneg z) hR (ne_of_gt hL)).mp
    rw [hRpow,←norm_pow,hzpow,norm_pow,hwlambda]
  have hlower : ENNReal.ofReal R ≤ spectralRadius ℂ B := by
    rw [spectralRadius_eq_of_unital]
    have h := le_iSup₂ (f:=fun z (_ : z ∈ spectrum ℂ B) => (‖z‖₊ : ℝ≥0∞)) z hzmem
    rw [←ENNReal.ofReal_coe_nnreal] at h
    simpa [hzR] using h
  refine ⟨hupper.antisymm hlower, ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_ge hl0 hl1.le
    have hk : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hsum : (L:ℝ) ≤ 2*((k:ℝ)+1) := by dsimp [L]; push_cast; exact_mod_cast (show a+b+2≤2*(k+1) by omega)
    apply (div_le_div_iff₀ hk hLc).mpr
    nlinarith
  · rw [ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one hl0.le hl1 (one_div_pos.mpr (by positivity))

end D5.S3.Quantum.Matrix.AsynchronousTwoBlockRadius
