/- GID: D5/S3/Quantum/Algebra/GenericCommonCoefficientPlane
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/GenericCommonCoefficientPlane
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An injective independent rectangular triple above the three-halves threshold has a common neutral complex coefficient plane. -/

import D5.S3.Quantum.Algebra.CommonCoefficientPlane
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! A simultaneous neutral plane above the strict three-halves dimension threshold. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Module
open scoped BigOperators ComplexOrder ComplexConjugate InnerProductSpace

namespace D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane
open D5.S3.Quantum.Algebra.CommonCoefficientPlane
open D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

private theorem coefficient_rank_le_two {a b : ℕ}
    (hab : 3 * a < 2 * b)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : compression X T = 0) : T.rank ≤ 2 := by
  let S := stack X
  let Q := Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ)
  have hS : S.rank = b := by
    change finrank ℂ (LinearMap.range S.mulVecLin) = b
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  have hleft := Matrix.rank_mul_ge Sᴴ Q
  have hright := Matrix.rank_mul_ge (Sᴴ * Q) S
  have hQ : Q.rank = a * T.rank := rank_kronecker_one T a
  have hz : (Sᴴ * Q * S).rank = 0 := by rw [show Sᴴ * Q * S = 0 from hT]; simp
  simp only [Matrix.rank_conjTranspose, hS, Fintype.card_prod,
    Fintype.card_fin] at hleft hright
  rw [hQ] at hleft
  by_contra hn
  have ht : 3 ≤ T.rank := by omega
  have hm := Nat.mul_le_mul_left a ht
  omega

private theorem spectral_signs {a b : ℕ} (hab : 3 * a < 2 * b)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stack X).mulVecLin)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian)
    (hPhi : compression X T = 0) (hne : T ≠ 0) :
    ∃ e : Fin 3 ≃ Fin 3,
      0 < hT.eigenvalues (e 0) ∧ hT.eigenvalues (e 1) < 0 ∧
      hT.eigenvalues (e 2) = 0 := by
  classical
  have hnotP : ¬ T.PosSemidef := fun h => hne (semidefinite_eq_zero X hX T h hPhi)
  have hnotN : ¬ (-T).PosSemidef := by
    intro h
    have hPhiN : compression X (-T) = 0 := by
      rw [compression_eq_sum]
      change (∑ r, ∑ s, -(T r s) • ((X r)ᴴ * X s)) = 0
      simp only [neg_smul, Finset.sum_neg_distrib]
      rw [← compression_eq_sum, hPhi, neg_zero]
    have he := semidefinite_eq_zero X hX (-T) h hPhiN
    exact hne (neg_eq_zero.mp he)
  obtain ⟨j, hj⟩ : ∃ j, hT.eigenvalues j < 0 := by
    by_contra h
    apply hnotP
    apply hT.posSemidef_iff_eigenvalues_nonneg.mpr
    intro j
    exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
  obtain ⟨i, hi⟩ : ∃ i, 0 < hT.eigenvalues i := by
    by_contra h
    have hnonpos : ∀ i, hT.eigenvalues i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hd : (Matrix.diagonal (fun i => (-(hT.eigenvalues i) : ℂ))).PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      exact_mod_cast neg_nonneg.mpr (hnonpos i)
    have hp := hd.mul_mul_conjTranspose_same (hT.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ)
    apply hnotN
    have hs := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [hs]
    convert hp using 1
    rw [Matrix.star_eq_conjTranspose]
    simp only [Function.comp_def]
    rw [show (Matrix.diagonal fun i => -(hT.eigenvalues i : ℂ)) =
        -(Matrix.diagonal fun i => (hT.eigenvalues i : ℂ)) by
      ext r s; by_cases hrs : r = s <;> simp [hrs]]
    rw [Matrix.mul_neg, Matrix.neg_mul]
    rfl
  have hij : i ≠ j := by intro he; subst j; linarith
  have hc : ({i, j} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card := by
    simp [hij]
  obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hki : k ≠ i := by exact fun he => hkn (by simp [he])
  have hkj : k ≠ j := by
    exact fun he => hkn (by simp [he])
  let f : Fin 3 → Fin 3 := ![i, j, k]
  have hf : Function.Injective f := by
    intro r s he
    fin_cases r <;> fin_cases s <;> simp_all [f]
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  have hknz : hT.eigenvalues k = 0 := by
    by_contra hknz
    have hall : ∀ r, hT.eigenvalues r ≠ 0 := by
      intro r
      obtain ⟨s, rfl⟩ := e.surjective r
      fin_cases s
      · exact ne_of_gt hi
      · exact ne_of_lt hj
      · exact hknz
    have hcard : Fintype.card {r // hT.eigenvalues r ≠ 0} = 3 := by
      simp [hall]
    have hr := coefficient_rank_le_two hab X hinj T hPhi
    rw [hT.rank_eq_card_non_zero_eigs, hcard] at hr
    omega
  exact ⟨e, hi, hj, hknz⟩

private theorem last_coefficient_eq_zero {a b : ℕ} (hab : a < b)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (U : Matrix (Fin a) (Fin a) ℂ) (hU : X 1 = U * X 0)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) : T 2 2 = 0 := by
  classical
  let K := LinearMap.ker (X 0).mulVecLin
  have hdim : 0 < finrank ℂ K := by
    have hs := (X 0).mulVecLin.finrank_range_add_finrank_ker
    have hu := (X 0).rank_le_card_height
    change (X 0).rank + finrank ℂ K = _ at hs
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hs hu
    omega
  obtain ⟨x, hxne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  have hx0 : X 0 *ᵥ x.val = 0 := x.property
  have hx1 : X 1 *ᵥ x.val = 0 := by
    rw [hU, ← Matrix.mulVec_mulVec, hx0, Matrix.mulVec_zero]
  have hx2 : X 2 *ᵥ x.val ≠ 0 := by
    intro he
    apply hxne
    apply Subtype.ext
    apply stack_injective_on_common_kernel X hinj
    intro r
    fin_cases r <;> assumption
  have he := compression_pairing X T x.val x.val
  rw [hPhi] at he
  simp only [Matrix.zero_mulVec, dotProduct_zero, Fin.sum_univ_three, hx0, hx1,
    star_zero, zero_dotProduct, dotProduct_zero, mul_zero, zero_add, add_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (fun hz => hx2 (dotProduct_star_self_eq_zero.mp hz))

private theorem cross_coefficient_pairing {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (U : Matrix (Fin a) (Fin a) ℂ) (hU : X 1 = U * X 0)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) (h22 : T 2 2 = 0)
    (x y : Fin b → ℂ) (hx : X 0 *ᵥ x = 0) :
    star (X 2 *ᵥ x) ⬝ᵥ (T 2 0 • (X 0 *ᵥ y) + T 2 1 • (X 1 *ᵥ y)) = 0 := by
  have hx1 : X 1 *ᵥ x = 0 := by
    rw [hU, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have he := compression_pairing X T x y
  rw [hPhi] at he
  simp only [Matrix.zero_mulVec, dotProduct_zero, Fin.sum_univ_three, hx, hx1,
    h22, star_zero, zero_dotProduct, zero_mul, mul_zero, zero_add, add_zero] at he
  simpa only [dotProduct_add, dotProduct_smul, smul_eq_mul] using he.symm

private def coefficientOperator {a : ℕ} (U : Matrix (Fin a) (Fin a) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin a) (Fin a) ℂ :=
  (T 0 0 + T 1 1) • 1 + T 0 1 • U + T 1 0 • Uᴴ

private theorem coefficientOperator_isHermitian {a : ℕ}
    (U : Matrix (Fin a) (Fin a) ℂ) (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian) :
    (coefficientOperator U T).IsHermitian := by
  have h00 : star (T 0 0) = T 0 0 := congrFun (congrFun hT 0) 0
  have h11 : star (T 1 1) = T 1 1 := congrFun (congrFun hT 1) 1
  have h01 : star (T 1 0) = T 0 1 := congrFun (congrFun hT 0) 1
  have h10 : star (T 0 1) = T 1 0 := congrFun (congrFun hT 1) 0
  change (coefficientOperator U T)ᴴ = coefficientOperator U T
  simp only [coefficientOperator, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_conjTranspose, star_add,
    h00, h11, h01, h10]
  abel

private theorem coefficientOperator_compression {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a) ℂ) (hU : X 1 = (U : Matrix (Fin a) (Fin a) ℂ) * X 0)
    (T : Matrix (Fin 3) (Fin 3) ℂ)
    (h02 : T 0 2 = 0) (h12 : T 1 2 = 0) (h20 : T 2 0 = 0)
    (h21 : T 2 1 = 0) (h22 : T 2 2 = 0) :
    (X 0)ᴴ * coefficientOperator U T * X 0 = compression X T := by
  have hleft : (U : Matrix (Fin a) (Fin a) ℂ)ᴴ * (U : Matrix (Fin a) (Fin a) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  rw [compression_eq_sum]
  simp only [Fin.sum_univ_three, h02, h12, h20, h21, h22, zero_smul,
    add_zero, coefficientOperator, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (U : Matrix (Fin a) (Fin a) ℂ)ᴴ
    (U : Matrix (Fin a) (Fin a) ℂ), hleft, Matrix.one_mul]
  module

private def hermitianKernel {a b : ℕ} (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) :
    Submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) where
  carrier := {T | T.IsHermitian ∧ compression X T = 0}
  zero_mem' := ⟨by simp, by simp [compression]⟩
  add_mem' := by
    intro T Q hT hQ
    refine ⟨hT.1.add hQ.1, ?_⟩
    simp only [compression_eq_sum, Matrix.add_apply, add_smul, Finset.sum_add_distrib] at *
    rw [hT.2, hQ.2, add_zero]
  smul_mem' := by
    intro c T hT
    refine ⟨hT.1.smul (IsSelfAdjoint.all c), ?_⟩
    have he : compression X (c • T) = c • compression X T := by
      rw [compression_eq_sum, compression_eq_sum]
      simp only [Matrix.smul_apply, Finset.smul_sum, smul_assoc]
    rw [he, hT.2, smul_zero]

private theorem eigenvector_phase {a : ℕ}
    (U : Matrix.unitaryGroup (Fin a) ℂ) (w : ℂ) (v : Fin a → ℂ) (hv : v ≠ 0)
    (heig : (U : Matrix (Fin a) (Fin a) ℂ) *ᵥ v = w • v) : star w * w = 1 := by
  have hunit : (U : Matrix (Fin a) (Fin a) ℂ)ᴴ * (U : Matrix (Fin a) (Fin a) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hnorm : star ((U : Matrix (Fin a) (Fin a) ℂ) *ᵥ v) ⬝ᵥ
      ((U : Matrix (Fin a) (Fin a) ℂ) *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hunit,
      Matrix.one_mulVec]
  rw [heig, star_smul, smul_dotProduct, dotProduct_smul] at hnorm
  change star w * (w * (star v ⬝ᵥ v)) = star v ⬝ᵥ v at hnorm
  apply mul_right_cancel₀ (show star v ⬝ᵥ v ≠ 0 from
    fun he => hv (dotProduct_star_self_eq_zero.mp he))
  simpa only [mul_assoc, one_mul] using hnorm

private theorem simultaneous_phase {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (U : Matrix.unitaryGroup (Fin a) ℂ)
    (hU : X 1 = (U : Matrix (Fin a) (Fin a) ℂ) * X 0)
    (hlarge : a < 2 * (X 0).rank)
    (hlast : ∀ T ∈ hermitianKernel X, T 2 2 = 0)
    (hcross : ∀ T ∈ hermitianKernel X, T 2 0 = 0 ∧ T 2 1 = 0) :
    ∃ w : ℂ, star w * w = 1 ∧ ∀ T ∈ hermitianKernel X,
      star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w) = 0 := by
  classical
  obtain ⟨V, hV, d, hdiag⟩ :=
    Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (U : Matrix (Fin a) (Fin a) ℂ)
  let W : Matrix.unitaryGroup (Fin a) ℂ := ⟨V, hV⟩
  have hWV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self W
  have hVW : V * Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using W.2.2
  have hUV : (U : Matrix (Fin a) (Fin a) ℂ) * V = V * Matrix.diagonal d := by
    rw [← hdiag, Matrix.star_eq_conjTranspose]
    simp only [← Matrix.mul_assoc, hVW, Matrix.one_mul]
  have hUd : Vᴴ * (U : Matrix (Fin a) (Fin a) ℂ)ᴴ * V = Matrix.diagonal (star d) := by
    have hh := congrArg Matrix.conjTranspose hdiag
    simpa only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc] using hh
  let z (T : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin a) : ℂ :=
    T 0 0 + T 1 1 + T 0 1 * d j + T 1 0 * star (d j)
  have hQdiag (T : Matrix (Fin 3) (Fin 3) ℂ) :
      Vᴴ * coefficientOperator U T * V = Matrix.diagonal (z T) := by
    simp only [coefficientOperator, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hWV, hUd]
    rw [show Vᴴ * (U : Matrix (Fin a) (Fin a) ℂ) * V = Matrix.diagonal d from hdiag]
    ext i j
    by_cases hij : i = j
    · subst j; simp [z]
    · simp [hij]
  have hreal (T : hermitianKernel X) (j : Fin a) : star (z T.val j) = z T.val j := by
    have hh := Matrix.isHermitian_conjTranspose_mul_mul V
      (coefficientOperator_isHermitian U T.val T.property.1)
    rw [hQdiag] at hh
    simpa only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] using
      congrFun (congrFun hh j) j
  let f (j : Fin a) : Module.Dual ℝ (hermitianKernel X) := {
    toFun := fun T => (z T.val j).re
    map_add' := by intro T Q; simp [z, add_mul]; ring
    map_smul' := by intro c T; simp [z, Complex.real_smul, smul_eq_mul, mul_add]; ring }
  have hsing (T : hermitianKernel X) : ¬ ∀ j, z T.val j ≠ 0 := by
    intro hz
    have hdunit : IsUnit (Matrix.diagonal (z T.val)) :=
      Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun j => isUnit_iff_ne_zero.mpr (hz j)))
    have hQunit : IsUnit (coefficientOperator (U : Matrix (Fin a) (Fin a) ℂ) T.val) := by
      have he : V * (Vᴴ * coefficientOperator (U : Matrix (Fin a) (Fin a) ℂ) T.val * V) *
          Vᴴ = coefficientOperator (U : Matrix (Fin a) (Fin a) ℂ) T.val := by
        simp only [← Matrix.mul_assoc, hVW, Matrix.one_mul]
        rw [Matrix.mul_assoc, hVW, Matrix.mul_one]
      rw [← he, hQdiag]
      exact (show IsUnit V from Unitary.isUnit_coe (U := W)).mul hdunit |>.mul
        (show IsUnit Vᴴ from by
          simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
            (Unitary.isUnit_coe (U := star W)))
    have hr := Matrix.rank_of_isUnit _ hQunit
    have h20 := (hcross T.val T.property).1
    have h21 := (hcross T.val T.property).2
    have h02 : T.val 0 2 = 0 := by
      have he := congrFun (congrFun T.property.1 0) 2
      simpa only [Matrix.conjTranspose_apply, h20, star_zero] using he.symm
    have h12 : T.val 1 2 = 0 := by
      have he := congrFun (congrFun T.property.1 1) 2
      simpa only [Matrix.conjTranspose_apply, h21, star_zero] using he.symm
    have hc := coefficientOperator_compression X U hU T.val h02 h12 h20 h21
    have h22 := hlast T.val T.property
    have hzero := (hc h22).trans T.property.2
    have h1 := Matrix.rank_mul_ge (X 0)ᴴ (coefficientOperator (U : Matrix (Fin a) (Fin a) ℂ) T.val)
    have h2 := Matrix.rank_mul_ge
      ((X 0)ᴴ * coefficientOperator (U : Matrix (Fin a) (Fin a) ℂ) T.val) (X 0)
    rw [hzero, Matrix.rank_zero] at h2
    simp only [Matrix.rank_conjTranspose, Fintype.card_fin] at h1 h2 hr
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin a, ∀ T : hermitianKernel X, f j T = 0 := by
    by_contra hh
    have hf : ∀ j, ∃ T, f j T ≠ 0 := by simpa only [not_exists, not_forall] using hh
    obtain ⟨T, hT⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
    exact hsing T (fun j hz => hT j (by simp [f, hz]))
  let v := V *ᵥ Pi.single j 1
  have hv : v ≠ 0 := by
    intro he
    have hi := Matrix.mulVec_injective_iff_isUnit.mpr
      (show IsUnit V from Unitary.isUnit_coe (U := W))
    have he' : V *ᵥ Pi.single j 1 = V *ᵥ 0 := by simpa [v] using he
    have heq := hi he'
    have hejj := congrFun heq j
    simp at hejj
  have heig : (U : Matrix (Fin a) (Fin a) ℂ) *ᵥ v = d j • v := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, hUV, ← Matrix.mulVec_mulVec]
    simp
  have hw := eigenvector_phase U (d j) v hv heig
  refine ⟨d j, hw, ?_⟩
  intro T hT
  have hzre : (z T j).re = 0 := hj ⟨T,hT⟩
  have hzim : (z T j).im = 0 := by
    have hh := congrArg Complex.im (hreal ⟨T,hT⟩ j)
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith
  have hz : z T j = 0 := Complex.ext hzre hzim
  rw [phaseVector_quad]
  change T 0 0 + T 1 1 + T 0 1 * d j + T 1 0 * star (d j) = 0 at hz
  linear_combination hz + T 1 1 * hw

private theorem intersection_kernel_vector {a : ℕ}
    (D R : Submodule ℂ (Fin a → ℂ)) (B : Matrix (Fin a) (Fin a) ℂ)
    (hlarge : 3 * a < 2 * (finrank ℂ D + finrank ℂ R))
    (hpair : ∀ r ∈ R, ∀ v ∈ D, star r ⬝ᵥ (B *ᵥ v) = 0) :
    ∃ v : Fin a → ℂ, v ∈ D ∧ v ∈ R ∧ v ≠ 0 ∧ B *ᵥ v = 0 := by
  classical
  let e : (Fin a → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin a) :=
    (WithLp.linearEquiv 2 ℂ (Fin a → ℂ)).symm
  let P := R.map e.toLinearMap
  have hmem (v : D) : e (B *ᵥ v.val) ∈ Pᗮ := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := hz
    simpa [e, PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]
      using hpair r hr v.val v.property
  let f : D →ₗ[ℂ] Pᗮ :=
    ((e.toLinearMap.comp B.mulVecLin).domRestrict D).codRestrict Pᗮ hmem
  let E := (LinearMap.ker f).map D.subtype
  have hdE : finrank ℂ E = finrank ℂ (LinearMap.ker f) :=
    Submodule.finrank_map_subtype_eq D (LinearMap.ker f)
  have hP : finrank ℂ P = finrank ℂ R := e.finrank_map_eq R
  have horth := P.finrank_add_finrank_orthogonal
  have hf := f.finrank_range_add_finrank_ker
  have hfupper := (LinearMap.range f).finrank_le
  have hsup := (E ⊔ R).finrank_le
  have hinter := E.finrank_sup_add_finrank_inf_eq R
  have hD := D.finrank_le
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    finrank_euclideanSpace] at horth hsup hD
  have hpos : 0 < finrank ℂ (E ⊓ R : Submodule ℂ (Fin a → ℂ)) := by omega
  obtain ⟨v, hvne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv : v.val ≠ 0 := by intro he; exact hvne (Subtype.ext he)
  obtain ⟨u, hu, huval⟩ := v.property.1
  have hB : B *ᵥ v.val = 0 := by
    have he : f u = 0 := hu
    have he' := congrArg Subtype.val he
    change e (B *ᵥ u.val) = 0 at he'
    have he0 : B *ᵥ u.val = 0 := e.injective (by simpa using he')
    simpa only [show u.val = v.val from huval] using he0
  exact ⟨v.val, (show u.val ∈ D from u.property) |> (huval ▸ ·),
    v.property.2, hv, hB⟩

private def residualSpace {a b : ℕ} (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) :
    Submodule ℂ (Fin a → ℂ) :=
  LinearMap.range ((X 2).mulVecLin.domRestrict (LinearMap.ker (X 0).mulVecLin))

private theorem residualSpace_finrank {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (U : Matrix (Fin a) (Fin a) ℂ) (hU : X 1 = U * X 0) :
    finrank ℂ (residualSpace X) + (X 0).rank = b := by
  have he := LinearMap.finrank_range_of_inj (kernel_restriction_injective X hinj U hU)
  have hs := (X 0).mulVecLin.finrank_range_add_finrank_ker
  change finrank ℂ (residualSpace X) = _ at he
  change (X 0).rank + finrank ℂ (LinearMap.ker (X 0).mulVecLin) = _ at hs
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hs
  omega

private theorem residual_pairing {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (U : Matrix (Fin a) (Fin a) ℂ) (hU : X 1 = U * X 0)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hPhi : compression X T = 0) (h22 : T 2 2 = 0)
    (r : Fin a → ℂ) (hr : r ∈ residualSpace X)
    (v : Fin a → ℂ) (hv : v ∈ LinearMap.range (X 0).mulVecLin) :
    star r ⬝ᵥ (T 2 0 • v + T 2 1 • (U *ᵥ v)) = 0 := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := hv
  change X 0 *ᵥ y = v at hy
  change X 2 *ᵥ x.val = r at hx
  have he := cross_coefficient_pairing X U hU T hPhi h22 x.val y x.property
  rw [hx, hU, ← Matrix.mulVec_mulVec, hy] at he
  exact he

private theorem phase_quad_of_image {a b : ℕ}
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T.IsHermitian)
    (hPhi : compression X T = 0) (h22 : T 2 2 = 0)
    (w : ℂ) (hcross : T 2 0 + w * T 2 1 = 0)
    (x : Fin b → ℂ) (v : Fin a → ℂ) (hv : v ≠ 0)
    (hx0 : X 0 *ᵥ x = v) (hx1 : X 1 *ᵥ x = w • v) :
    star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w) = 0 := by
  have hreverse : T 0 2 + star w * T 1 2 = 0 := by
    have he := congrArg star hcross
    have h02 : star (T 2 0) = T 0 2 := congrFun (congrFun hT 0) 2
    have h12 : star (T 2 1) = T 1 2 := congrFun (congrFun hT 1) 2
    simpa only [star_add, star_mul, h02, h12, star_zero, mul_comm] using he
  have he := compression_pairing X T x x
  rw [hPhi] at he
  simp only [Matrix.zero_mulVec, dotProduct_zero, Fin.sum_univ_three,
    hx0, hx1, h22, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    zero_mul, add_zero] at he
  apply (mul_eq_zero.mp (show (star (phaseVector w) ⬝ᵥ (T *ᵥ phaseVector w)) *
      (star v ⬝ᵥ v) = 0 by
    rw [phaseVector_quad]
    linear_combination -he - (star v ⬝ᵥ (X 2 *ᵥ x)) * hreverse -
      (star (X 2 *ᵥ x) ⬝ᵥ v) * hcross)).resolve_right
  exact fun hn => hv (dotProduct_star_self_eq_zero.mp hn)

private theorem normalized_common_plane {a b : ℕ} (hab : 3 * a < 2 * b)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin) (hSig : compression X signature = 0) :
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 →
        ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
  classical
  obtain ⟨U, hU⟩ := GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (X 1) (X 0) (gram_eq_of_signature X hSig)
  have hab' : a < b := by omega
  have h22 (T : Matrix (Fin 3) (Fin 3) ℂ) (hT : T ∈ hermitianKernel X) : T 2 2 = 0 :=
    last_coefficient_eq_zero hab' X hinj U hU T hT.2
  have hRdim := residualSpace_finrank X hinj U hU
  have hRupper := (residualSpace X).finrank_le
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hRupper
  have hAr : a < 2 * (X 0).rank := by omega
  suffices hplane : ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T ∈ hermitianKernel X, ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 by
    obtain ⟨L, hd, hL⟩ := hplane
    exact ⟨L, hd, fun T hT hPhi => hL T ⟨hT, hPhi⟩⟩
  by_cases hcross : ∀ T ∈ hermitianKernel X, T 2 0 = 0 ∧ T 2 1 = 0
  · obtain ⟨w, hw, hquad⟩ := simultaneous_phase X U hU hAr h22 hcross
    apply phase_plane (hermitianKernel X) w
    intro T hT
    refine ⟨hT.1, h22 T hT, ?_, hquad T hT⟩
    rw [(hcross T hT).1, (hcross T hT).2]; simp
  · obtain ⟨T, hTK, hbad⟩ : ∃ T ∈ hermitianKernel X, ¬ (T 2 0 = 0 ∧ T 2 1 = 0) := by
      simpa only [not_forall, exists_prop] using hcross
    let D := LinearMap.range (X 0).mulVecLin
    let R := residualSpace X
    let B : Matrix (Fin a) (Fin a) ℂ := T 2 0 • 1 + T 2 1 • (U : Matrix (Fin a) (Fin a) ℂ)
    have hDR : 3 * a < 2 * (finrank ℂ D + finrank ℂ R) := by
      change 3 * a < 2 * ((X 0).rank + finrank ℂ (residualSpace X))
      omega
    have hpB : ∀ r ∈ R, ∀ v ∈ D, star r ⬝ᵥ (B *ᵥ v) = 0 := by
      intro r hr v hv
      simpa only [B, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using
        residual_pairing X U hU T hTK.2 (h22 T hTK) r hr v hv
    obtain ⟨v, hvD, hvR, hv, hB⟩ := intersection_kernel_vector D R B hDR hpB
    have h21 : T 2 1 ≠ 0 := by
      intro hq
      have he : T 2 0 • v = 0 := by
        simpa only [B, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          hq, zero_smul, add_zero] using hB
      exact hbad ⟨(smul_eq_zero.mp he).resolve_right hv, hq⟩
    let w := -(T 2 0) / T 2 1
    have heig : (U : Matrix (Fin a) (Fin a) ℂ) *ᵥ v = w • v := by
      have he : T 2 1 • ((U : Matrix (Fin a) (Fin a) ℂ) *ᵥ v) = -(T 2 0 • v) := by
        apply eq_neg_of_add_eq_zero_left
        simpa only [B, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, add_comm] using hB
      calc
        _ = (T 2 1)⁻¹ • (T 2 1 • ((U : Matrix (Fin a) (Fin a) ℂ) *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ h21, one_smul]
        _ = w • v := by rw [he]; simp [w, div_eq_mul_inv, smul_smul, mul_comm]
    have hcrossW (Q : Matrix (Fin 3) (Fin 3) ℂ) (hQ : Q ∈ hermitianKernel X) :
        Q 2 0 + w * Q 2 1 = 0 := by
      have he := residual_pairing X U hU Q hQ.2 (h22 Q hQ) v hvR v hvD
      rw [heig] at he
      simp only [smul_smul, dotProduct_add, dotProduct_smul, smul_eq_mul] at he
      apply (mul_eq_zero.mp (show (Q 2 0 + w * Q 2 1) * (star v ⬝ᵥ v) = 0 by
        linear_combination he)).resolve_right
      exact fun hn => hv (dotProduct_star_self_eq_zero.mp hn)
    obtain ⟨x, hx⟩ := hvD
    have hx1 : X 1 *ᵥ x = w • v := by
      rw [hU, ← Matrix.mulVec_mulVec, show X 0 *ᵥ x = v from hx, heig]
    apply phase_plane (hermitianKernel X) w
    intro Q hQ
    exact ⟨hQ.1, h22 Q hQ, hcrossW Q hQ,
      phase_quad_of_image X Q hQ.1 hQ.2 (h22 Q hQ) w (hcrossW Q hQ) x v hv hx hx1⟩

/-- One complex two-plane is neutral for the entire Hermitian coefficient kernel. -/
theorem common_plane {a b : ℕ} (hab : 3 * a < 2 * b)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ) (hX : LinearIndependent ℂ X)
    (hinj : Function.Injective (stack X).mulVecLin) :
    ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
      ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian →
        (stack X)ᴴ * Matrix.kronecker T (1 : Matrix (Fin a) (Fin a) ℂ) * stack X = 0 →
        ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0 := by
  classical
  change ∃ L : Submodule ℂ (Fin 3 → ℂ), finrank ℂ L = 2 ∧
    ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 →
      ∀ u ∈ L, ∀ v ∈ L, star u ⬝ᵥ (T *ᵥ v) = 0
  by_cases hzero : ∀ T : Matrix (Fin 3) (Fin 3) ℂ,
      T.IsHermitian → compression X T = 0 → T = 0
  · obtain ⟨L, hd, hL⟩ := phase_plane (hermitianKernel X) 1 (by
      intro T hT
      rw [hzero T hT.1 hT.2]
      simp)
    exact ⟨L, hd, fun T hT hPhi => hL T ⟨hT,hPhi⟩⟩
  · obtain ⟨T, hT, hPhi, hne⟩ : ∃ T : Matrix (Fin 3) (Fin 3) ℂ,
        T.IsHermitian ∧ compression X T = 0 ∧ T ≠ 0 := by
      simpa only [not_forall, exists_prop] using hzero
    obtain ⟨e, hp, hn, hz⟩ := spectral_signs hab X hX hinj T hT hPhi hne
    obtain ⟨B, hB, hD⟩ := signature_congruence T hT e hp hn hz
    let A := B⁻¹
    have hA : IsUnit A := Matrix.isUnit_nonsing_inv_iff.mpr hB
    have hBA : B * A = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
    have hrecover (Q : Matrix (Fin 3) (Fin 3) ℂ) : Aᴴ * (Bᴴ * Q * B) * A = Q := by
      calc
        _ = (B * A)ᴴ * Q * (B * A) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Q := by rw [hBA]; simp
    let Y := mix A X
    have hYinj : Function.Injective (stack Y).mulVecLin := injective_stack_mix A hA X hinj
    have hYSig : compression Y signature = 0 := by
      rw [show Y = mix A X from rfl, compression_mix, ← hD, hrecover, hPhi]
    obtain ⟨L, hdim, hL⟩ := normalized_common_plane hab Y hYinj hYSig
    let K : Set (Matrix (Fin 3) (Fin 3) ℂ) := {Q | Q.IsHermitian ∧ compression X Q = 0}
    have hneutral : ∀ Q ∈ K, ∀ u ∈ L, ∀ v ∈ L,
        star u ⬝ᵥ ((Bᴴ * Q * B) *ᵥ v) = 0 := by
      intro Q hQ
      apply hL (Bᴴ * Q * B) (Matrix.isHermitian_conjTranspose_mul_mul B hQ.1)
      rw [show Y = mix A X from rfl, compression_mix, hrecover]
      exact hQ.2
    obtain ⟨L', hdim', hL'⟩ := common_plane_transport K B hB L hdim hneutral
    exact ⟨L', hdim', fun Q hQ hPhi => hL' Q ⟨hQ, hPhi⟩⟩

end D5.S3.Quantum.Algebra.GenericCommonCoefficientPlane
