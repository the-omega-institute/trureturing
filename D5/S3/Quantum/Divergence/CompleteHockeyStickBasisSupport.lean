/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Trivial common basis output support implies unit complete hockey-stick coefficient. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
import D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace
import D5.S3.Quantum.Recovery.BKMFlagRefinement
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Trivial common support among the outputs of computational basis states
forces complete hockey-stick coefficient one for a fixed parameter above one.
The construction uses simplex vectors on a reference of input dimension. -/

set_option autoImplicit false

noncomputable section

namespace HockeyStickSupportLinearCore

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Compare each prepared support coordinate with the coordinate for the distinguished outcome. -/
private def differences (S : Option I → Submodule K V) :
    ((i : Option I) → S i) →ₗ[K] (I → V) :=
  LinearMap.pi fun i =>
    ((S (some i)).subtype.comp (LinearMap.proj (some i))) -
      ((S none).subtype.comp (LinearMap.proj none))

/-- The comparison determines each support vector when their common intersection is zero.
The linear reconstruction maps extend to every vector in the comparison space. -/
private theorem recover_coordinates (S : Option I → Submodule K V) (hS : (⨅ i, S i) = ⊥) :
    ∃ recover : Option I → ((I → V) →ₗ[K] V),
      ∀ (x : (i : Option I) → S i) i, recover i (differences S x) = (x i : V) := by
  have hker : (differences S).ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have heq (i : I) : (x (some i) : V) = (x none : V) := by
      apply sub_eq_zero.mp
      exact congrFun hx i
    have hm : (x none : V) ∈ ⨅ i, S i := by
      apply (Submodule.mem_iInf S).mpr
      intro i
      cases i with
      | none => exact (x none).property
      | some i => exact heq i ▸ (x (some i)).property
    have hz : (x none : V) = 0 := by
      rwa [hS, Submodule.mem_bot] at hm
    funext i
    apply Subtype.ext
    cases i with
    | none => exact hz
    | some i => exact (heq i).trans hz
  obtain ⟨g, hg⟩ := (differences S).exists_leftInverse_of_injective hker
  refine ⟨fun i => (S i).subtype.comp ((LinearMap.proj i).comp g), fun x i => ?_⟩
  have h : g (differences S x) = x := DFunLike.congr_fun hg x
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply, h]

end HockeyStickSupportLinearCore

namespace HockeyStickSupportLinearCore

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

/-- An effect whose compression to the first summand is a scalar identity and
whose kernel contains the graph of the specified linear map. -/
private theorem graph_effect {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Nonempty a]
    (L : Matrix a b ℂ) (ε : ℝ) :
    ∃ F : Matrix (a ⊕ b) (a ⊕ b) ℂ,
      0 ≤ F ∧ F ≤ 1 ∧
      F.submatrix Sum.inl Sum.inl = (1 + ε ^ 2 * ‖L‖ ^ 2)⁻¹ • (1 : Matrix a a ℂ) ∧
      ∀ y : b → ℂ, F *ᵥ (Sum.elim (ε • (L *ᵥ y)) y) = 0 := by
  let J : Matrix (a ⊕ b) a ℂ := fromRows 1 ((-ε) • Lᴴ)
  let d : ℝ := 1 + ε ^ 2 * ‖L‖ ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  let F : Matrix (a ⊕ b) (a ⊕ b) ℂ := d⁻¹ • (J * Jᴴ)
  have hgram : Jᴴ * J = 1 + (ε ^ 2) • (L * Lᴴ) := by
    unfold J
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows,
      conjTranspose_one, one_mul, conjTranspose_smul, conjTranspose_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp [pow_two]
  have hnorm (A : Matrix a b ℂ) : ‖A * Aᴴ‖ = ‖A‖ ^ 2 := by
    simpa [pow_two, l2_opNorm_conjTranspose] using l2_opNorm_conjTranspose_mul_self Aᴴ
  have hnormJ : ‖J * Jᴴ‖ = ‖Jᴴ * J‖ := by
    have h := l2_opNorm_conjTranspose_mul_self Jᴴ
    simpa only [conjTranspose_conjTranspose, l2_opNorm_conjTranspose,
      l2_opNorm_conjTranspose_mul_self] using h
  have hFp : 0 ≤ F := (posSemidef_self_mul_conjTranspose J).smul
    (inv_nonneg.mpr hd.le) |>.nonneg
  refine ⟨F, hFp, ?_, ?_, ?_⟩
  · apply (CStarAlgebra.norm_le_one_iff_of_nonneg F hFp).mp
    have hJ : ‖J * Jᴴ‖ ≤ d := by
      rw [hnormJ, hgram]
      calc
        ‖(1 : Matrix a a ℂ) + ε ^ 2 • (L * Lᴴ)‖ ≤
            ‖(1 : Matrix a a ℂ)‖ + ‖ε ^ 2 • (L * Lᴴ)‖ := norm_add_le _ _
        _ = d := by
          unfold d
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ), norm_smul, RCLike.norm_ofReal,
            abs_of_nonneg (sq_nonneg _), hnorm, norm_one]
    change ‖d⁻¹ • (J * Jᴴ)‖ ≤ 1
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr hd.le), inv_mul_le_iff₀ hd, mul_one]
    exact hJ
  · ext i j
    simp only [F, J, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      fromRows_mul_fromCols, conjTranspose_one, submatrix_apply, Matrix.smul_apply,
      fromBlocks_apply₁₁, one_mul]
    rfl
  · intro y
    have hkill : Jᴴ *ᵥ (Sum.elim (ε • (L *ᵥ y)) y) = 0 := by
      unfold J
      rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
        conjTranspose_smul, conjTranspose_conjTranspose, fromCols_mulVec_sumElim,
        one_mulVec, smul_mulVec]
      simp
    change (d⁻¹ • (J * Jᴴ)) *ᵥ _ = 0
    rw [smul_mulVec, ← mulVec_mulVec, hkill, mulVec_zero, smul_zero]

/-- If the prepared supports have zero common intersection, a single norm bound
gives effects that annihilate the perturbed comparison columns. The compression
onto the distinguished reference coordinate tends to the identity. -/
private theorem support_effect {I a : Type*} [Fintype I] [DecidableEq I]
    [Fintype a] [DecidableEq a] [Nonempty a]
    (S : Option I → Submodule ℂ (a → ℂ)) (hS : (⨅ i, S i) = ⊥) (pivot : I) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ,
      ∃ F : Matrix (a ⊕ (I × a)) (a ⊕ (I × a)) ℂ,
        0 ≤ F ∧ F ≤ 1 ∧
        F.submatrix Sum.inl Sum.inl = (1 + ε ^ 2 * C)⁻¹ • (1 : Matrix a a ℂ) ∧
        ∀ x : (i : Option I) → S i,
          F *ᵥ (Sum.elim (ε • (x (some pivot) : a → ℂ))
            (fun p => differences S x p.1 p.2)) = 0 := by
  obtain ⟨recover, hrecover⟩ := recover_coordinates S hS
  let curry := (LinearEquiv.curry ℂ ℂ I a).toLinearMap
  let L := (recover (some pivot)).comp curry
  refine ⟨‖L.toMatrix'‖ ^ 2, sq_nonneg _, fun ε => ?_⟩
  obtain ⟨F, hF, hF₁, htop, hkill⟩ := graph_effect L.toMatrix' ε
  refine ⟨F, hF, hF₁, htop, fun x => ?_⟩
  let y : (I × a) → ℂ := fun p => differences S x p.1 p.2
  have hy : L.toMatrix' *ᵥ y = (x (some pivot) : a → ℂ) := by
    rw [LinearMap.toMatrix'_mulVec]
    exact hrecover x (some pivot)
  simpa only [hy] using hkill y

section Simplex

open scoped Kronecker

variable {I a : Type*} [Fintype I] [DecidableEq I] [Fintype a] [DecidableEq a] [Nonempty a]

private def simplexVector (pivot : I) (ε : ℝ) (i : Option I) : Option I → ℂ
  | none => if i = some pivot then (ε : ℂ) else 0
  | some j => (if i = some j then 1 else 0) - (if i = none then 1 else 0)

private def splitReference : a ⊕ (I × a) ≃ Option I × a where
  toFun := Sum.elim (fun j => (none, j)) (fun p => (some p.1, p.2))
  invFun p := match p.1 with
    | none => Sum.inl p.2
    | some i => Sum.inr (i, p.2)
  left_inv s := by cases s <;> rfl
  right_inv := by rintro ⟨_ | _, _⟩ <;> rfl

/-- A scalar-compression effect annihilates each negative simplex contribution
when the prepared matrices have trivial intersection of ranges. -/
private theorem simplex_effect (τ : Option I → Matrix a a ℂ)
    (hτ : (⨅ i, (τ i).mulVecLin.range) = ⊥) (pivot : I) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ,
      ∃ F : Matrix (Option I × a) (Option I × a) ℂ,
        0 ≤ F ∧ F ≤ 1 ∧
        F.submatrix (Prod.mk none) (Prod.mk none) = (1 + ε ^ 2 * C)⁻¹ • (1 : Matrix a a ℂ) ∧
        ∀ i, F * (vecMulVec (simplexVector pivot ε i) (star (simplexVector pivot ε i)) ⊗ₖ
          τ i) = 0 := by
  let S (i : Option I) := (τ i).mulVecLin.range
  obtain ⟨C, hC, hF⟩ := support_effect S hτ pivot
  refine ⟨C, hC, fun ε => ?_⟩
  obtain ⟨G, hG, hG₁, htop, hkill⟩ := hF ε
  let e : a ⊕ (I × a) ≃ Option I × a := splitReference
  let F := G.submatrix e.symm e.symm
  refine ⟨F, (hG.posSemidef.submatrix _).nonneg, ?_, htop, ?_⟩
  · apply sub_nonneg.mp
    simpa [F, Matrix.submatrix_sub, Matrix.submatrix_one_equiv] using
      ((sub_nonneg.mpr hG₁).posSemidef.submatrix e.symm).nonneg
  · intro i
    let w := simplexVector pivot ε i
    ext row col
    have hcol : (τ i).col col.2 ∈ S i := by
      change (τ i).col col.2 ∈ (τ i).mulVecLin.range
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨col.2, rfl⟩
    let x : (j : Option I) → S j := Pi.single i ⟨(τ i).col col.2, hcol⟩
    have hx (j : Option I) : (x j : a → ℂ) = if j = i then (τ i).col col.2 else 0 := by
      by_cases h : j = i
      · subst j
        simp [x]
      · simp [x, h]
    have hk := congrFun (hkill x) (e.symm row)
    have hc :
        (fun s : a ⊕ (I × a) => w (e s).1 * τ i (e s).2 col.2) =
          Sum.elim (ε • (x (some pivot) : a → ℂ)) (fun p => differences S x p.1 p.2) := by
      funext s
      cases s with
      | inl j =>
        change (if i = some pivot then (ε : ℂ) else 0) * τ i j col.2 =
          (ε • (x (some pivot) : a → ℂ)) j
        rw [hx]
        by_cases h : i = some pivot <;> simp [h, eq_comm, Matrix.col, Complex.real_smul]
      | inr p =>
        change ((if i = some p.1 then 1 else 0) - (if i = none then 1 else 0)) *
          τ i p.2 col.2 = (x (some p.1) : a → ℂ) p.2 - (x none : a → ℂ) p.2
        rw [hx, hx, sub_mul]
        by_cases h₁ : i = some p.1 <;> by_cases h₂ : i = none <;>
          simp [h₁, h₂, eq_comm, Matrix.col]
    rw [← hc, Matrix.mulVec, dotProduct] at hk
    change _ = (0 : ℂ) at hk
    change (∑ j, G (e.symm row) (e.symm j) *
      ((w j.1 * star (w col.1)) * τ i j.2 col.2)) = 0
    calc
      _ = (∑ j, G (e.symm row) (e.symm j) * (w j.1 * τ i j.2 col.2)) * star (w col.1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by
        rw [← e.sum_comp (fun j => G (e.symm row) (e.symm j) * (w j.1 * τ i j.2 col.2))]
        simp only [Equiv.symm_apply_apply, hk, zero_mul]

omit [DecidableEq a] [Nonempty a] in
/-- The reference ray at `none` tests only the compression of the effect to
that reference coordinate. -/
private theorem distinguished_trace (F : Matrix (Option I × a) (Option I × a) ℂ)
    (T : Matrix a a ℂ) :
    (F * ((Matrix.single none none 1 : Matrix (Option I) (Option I) ℂ) ⊗ₖ T)).trace =
      (F.submatrix (Prod.mk none) (Prod.mk none) * T).trace := by
  let P : Matrix (Option I) (Option I) ℂ := Matrix.single none none 1
  rw [Matrix.trace_mul_comm, Matrix.trace_mul_comm (F.submatrix _ _) T]
  have h (i : Option I) (j : a) : ((P ⊗ₖ T) * F) (i, j) (i, j) =
      if i = none then (T * F.submatrix (Prod.mk none) (Prod.mk none)) j j else 0 := by
    cases i <;>
      simp [P, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.single,
        Fintype.sum_prod_type, Matrix.submatrix_apply]
  change ((P ⊗ₖ T) * F).trace = _
  simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, h]

/-- The negative simplex terms contribute zero to the measured trace, even
after scaling them to calibrate the two input states. -/
private theorem simplex_payoff (τ : Option I → Matrix a a ℂ)
    (hτ : (⨅ i, (τ i).mulVecLin.range) = ⊥) (htrace : (τ none).trace = 1) (pivot : I) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε t : ℝ,
      ∃ F : Matrix (Option I × a) (Option I × a) ℂ,
        0 ≤ F ∧ F ≤ 1 ∧
        (F * ((Matrix.single none none 1 : Matrix (Option I) (Option I) ℂ) ⊗ₖ τ none -
          ∑ i, t • (vecMulVec (simplexVector pivot ε i) (star (simplexVector pivot ε i)) ⊗ₖ
            τ i))).trace =
          ((1 + ε ^ 2 * C)⁻¹ : ℝ) • (1 : ℂ) := by
  obtain ⟨C, hC, hF⟩ := simplex_effect τ hτ pivot
  refine ⟨C, hC, fun ε t => ?_⟩
  obtain ⟨F, hF₀, hF₁, htop, hkill⟩ := hF ε
  refine ⟨F, hF₀, hF₁, ?_⟩
  simp only [mul_sub, Matrix.mul_sum, Matrix.mul_smul, hkill, smul_zero,
    Finset.sum_const_zero, sub_zero, distinguished_trace, htop, Matrix.smul_mul,
    one_mul, Matrix.trace_smul, htrace]

end Simplex

section Calibration

variable {I n : Type*} [Fintype I] [Fintype n]

/-- Calibrate a positive block and prescribed negative blocks to two positive
families with identical sums of trace one. -/
private theorem calibrate_blocks (γ : ℝ) (hγ : 1 < γ) (P : Matrix n n ℂ)
    (hP : P.PosSemidef) (hPtr : P.trace = 1) (Y : Option I → Matrix n n ℂ)
    (hY : ∀ i, (Y i).PosSemidef) (hdom : γ • P ≤ ∑ i, Y i) :
    ∃ (c : ℝ) (ρ σ : Option I → Matrix n n ℂ), 0 < c ∧
      (∀ i, (ρ i).PosSemidef) ∧ (∀ i, (σ i).PosSemidef) ∧
      (∑ i, ρ i) = ∑ i, σ i ∧ (∑ i, ρ i).trace = 1 ∧
      ∀ i, ρ i - γ • σ i = c • ((if i = none then P else 0) - Y i) := by
  classical
  have hg : 0 < γ := by linarith
  have hg₁ : 0 < γ - 1 := sub_pos.mpr hγ
  let K := (γ - 1)⁻¹ • ((∑ i, Y i) - γ • P)
  have hK : K.PosSemidef := (sub_nonneg.mpr hdom).posSemidef.smul (inv_nonneg.mpr hg₁.le)
  have hKrel : (γ - 1) • K = (∑ i, Y i) - γ • P := by
    simp [K, smul_smul, mul_inv_cancel₀ hg₁.ne']
  have htrK := Complex.nonneg_iff.mp hK.trace_nonneg
  let z : ℝ := 1 + K.trace.re
  have hz : 0 < z := by dsimp [z]; linarith [htrK.1]
  let c := z⁻¹
  have hc : 0 < c := inv_pos.mpr hz
  let ρ : Option I → Matrix n n ℂ := fun
    | none => c • (P + K)
    | some _ => 0
  let σ : Option I → Matrix n n ℂ := fun i =>
    c • (γ⁻¹ • (Y i + if i = none then K else 0))
  refine ⟨c, ρ, σ, hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i
    · exact (hP.add hK).smul hc.le
    · exact Matrix.PosSemidef.zero
  · intro i
    apply Matrix.PosSemidef.smul _ hc.le
    apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr hg.le)
    apply (hY i).add
    split <;> first | exact hK | exact Matrix.PosSemidef.zero
  · have hsum : (∑ i, Y i) + K = γ • (P + K) := by
      calc
        _ = ((∑ i, Y i) - γ • P) + (γ • P + K) := by abel
        _ = _ := by rw [← hKrel, sub_smul, one_smul, smul_add]; abel
    have hρ : (∑ i, ρ i) = c • (P + K) := by simp [ρ, Fintype.sum_option]
    rw [hρ]
    simp only [σ, ← Finset.smul_sum, Finset.sum_add_distrib]
    have hsumK : (∑ i : Option I, if i = none then K else 0) = K := by simp
    rw [hsumK, hsum, smul_smul γ⁻¹ γ, inv_mul_cancel₀ hg.ne', one_smul]
  · have hρ : (∑ i, ρ i) = c • (P + K) := by simp [ρ, Fintype.sum_option]
    have htrace : (P + K).trace = (z : ℂ) := by
      apply Complex.ext <;> simp [z, Matrix.trace_add, hPtr, ← htrK.2]
    rw [hρ, Matrix.trace_smul, htrace, Complex.real_smul]
    exact_mod_cast inv_mul_cancel₀ hz.ne'
  · intro i
    have hs : γ • σ i = c • (Y i + if i = none then K else 0) := by
      dsimp only [σ]
      rw [smul_comm γ c, smul_smul γ γ⁻¹, mul_inv_cancel₀ hg.ne', one_smul]
    rw [hs]
    cases i with
    | none =>
      change c • (P + K) - c • (Y none + K) = c • (P - Y none)
      rw [← smul_sub]
      congr 1
      abel
    | some i => simp [ρ, ← smul_neg]

end Calibration

section Dominance

variable {I n : Type*} [Fintype I] [Finite n]

private def ray (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

private theorem sum_ray_le (v : I → n → ℂ) :
    ray (∑ i, v i) ≤ (Fintype.card I : ℝ) • ∑ i, ray (v i) := by
  apply sub_nonneg.mp
  have h : (2 : ℝ) • ((Fintype.card I : ℝ) • ∑ i, ray (v i) - ray (∑ i, v i)) =
      ∑ i, ∑ j, ray (v i - v j) := by
    ext p q
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply, ray, vecMulVec_apply,
      Pi.star_apply, Pi.sub_apply, star_sub, Finset.sum_apply, star_sum, Complex.real_smul,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  have hp : (∑ i, ∑ j, ray (v i - v j)).PosSemidef :=
    Matrix.posSemidef_sum _ fun i _ =>
      Matrix.posSemidef_sum _ fun j _ => Matrix.posSemidef_vecMulVec_self_star _
  have hp' := (h ▸ hp : ((2 : ℝ) •
    ((Fintype.card I : ℝ) • ∑ i, ray (v i) - ray (∑ i, v i))).PosSemidef)
  simpa [smul_smul] using (hp'.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).nonneg

end Dominance

section SimplexCalibration

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The simplex rays can be scaled to dominate the prescribed positive ray
at each nonzero perturbation. -/
private theorem simplex_dominates (pivot : I) {γ ε : ℝ} (hγ : 0 < γ) (hε : ε ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ γ • (Matrix.single none none 1 : Matrix (Option I) (Option I) ℂ) ≤
      ∑ i, t • ray (simplexVector pivot ε i) := by
  let v := simplexVector pivot ε
  let e : Option I → ℂ := Pi.single none 1
  let P : Matrix (Option I) (Option I) ℂ := Matrix.single none none 1
  have hsum : ∑ i, v i = ε • e := by
    funext r
    cases r with
    | none => simp [v, e, simplexVector, Finset.sum_apply, Complex.real_smul]
    | some j => simp [v, e, simplexVector, Finset.sum_apply, Finset.sum_sub_distrib]
  have hP : ray (∑ i, v i) = ε ^ 2 • P := by
    rw [hsum]
    ext i j
    cases i <;> cases j <;>
      simp [ray, e, P, Matrix.single, vecMulVec_apply, Complex.real_smul, pow_two]
  let c : ℝ := γ / ε ^ 2
  have hc : 0 < c := div_pos hγ (sq_pos_of_ne_zero hε)
  have hcε : c * ε ^ 2 = γ := div_mul_cancel₀ _ (pow_ne_zero _ hε)
  have hcard : 0 < (Fintype.card (Option I) : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨c * Fintype.card (Option I), mul_pos hc hcard, ?_⟩
  have h := smul_le_smul_of_nonneg_left (sum_ray_le v) hc.le
  rwa [hP, smul_smul, hcε, smul_smul, Finset.smul_sum] at h

end SimplexCalibration

section Witness

open scoped Kronecker

variable {I a : Type*} [Fintype I] [DecidableEq I] [Fintype a] [DecidableEq a] [Nonempty a]

/-- Equal-marginal input blocks with an exact denominator and a measured output
retention factor tending to one as the perturbation vanishes. -/
private theorem simplex_witness (τ : Option I → Matrix a a ℂ)
    (hτ : (⨅ i, (τ i).mulVecLin.range) = ⊥) (htrace : (τ none).trace = 1)
    (pivot : I) (γ : ℝ) (hγ : 1 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ≠ 0 →
      ∃ (c : ℝ) (ρ σ : Option I → Matrix (Option I) (Option I) ℂ)
        (F : Matrix (Option I × a) (Option I × a) ℂ),
        0 < c ∧ (∀ i, (ρ i).PosSemidef) ∧ (∀ i, (σ i).PosSemidef) ∧
        (∑ i, ρ i) = (∑ i, σ i) ∧ (∑ i, ρ i).trace = 1 ∧ 0 ≤ F ∧ F ≤ 1 ∧
        (∑ i, (((ρ i - γ • σ i)⁺ : Matrix (Option I) (Option I) ℂ)).trace) = (c : ℂ) ∧
        (F * ∑ i, (ρ i - γ • σ i) ⊗ₖ τ i).trace = (c : ℂ) * ((1 + ε ^ 2 * C)⁻¹ : ℝ) := by
  obtain ⟨C, hC, hF⟩ := simplex_payoff τ hτ htrace pivot
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨t, ht, hdom⟩ := simplex_dominates pivot (lt_trans zero_lt_one hγ) hε
  let P : Matrix (Option I) (Option I) ℂ := Matrix.single none none 1
  let Y (i : Option I) := t • ray (simplexVector pivot ε i)
  have hPtr : P.trace = 1 := by simp [P]
  have hP : P.PosSemidef := by
    rw [show P = ray (Pi.single (none : Option I) (1 : ℂ)) by
      simp [P, ray, Pi.star_single, Matrix.single_eq_single_vecMulVec_single]]
    exact Matrix.posSemidef_vecMulVec_self_star _
  have hY (i : Option I) : (Y i).PosSemidef :=
    (Matrix.posSemidef_vecMulVec_self_star (simplexVector pivot ε i)).smul ht.le
  obtain ⟨c, ρ, σ, hc, hρ, hσ, hsum, htr, hdiff⟩ :=
    calibrate_blocks γ hγ P hP hPtr Y hY hdom
  obtain ⟨F, hF₀, hF₁, hpay⟩ := hF ε t
  refine ⟨c, ρ, σ, F, hc, hρ, hσ, hsum, htr, hF₀, hF₁, ?_, ?_⟩
  · have hzero : P * Y none = 0 := by
      ext i j
      cases i <;>
        simp [P, Y, ray, Matrix.mul_apply, Matrix.single, vecMulVec_apply,
          Matrix.smul_apply, simplexVector]
    have hblock (i : Option I) : (ρ i - γ • σ i)⁺ = if i = none then c • P else 0 := by
      rw [hdiff, CFC.posPart_smul_of_nonneg hc.le]
      cases i with
      | none =>
        simp only [ite_true]
        rw [(CFC.posPart_negPart_unique rfl hzero hP.nonneg (hY none).nonneg).1]
      | some i =>
        simp only [Option.some_ne_none, ite_false, zero_sub]
        have hneg := (IsSelfAdjoint.of_nonneg (hY (some i)).nonneg).neg
        rw [(CFC.posPart_eq_zero_iff _ hneg).mpr (neg_nonpos.mpr (hY (some i)).nonneg), smul_zero]
    simp [hblock, Matrix.trace_smul, hPtr, Complex.real_smul]
  · have hout : (∑ i, (ρ i - γ • σ i) ⊗ₖ τ i) =
        c • (P ⊗ₖ τ none - ∑ i, Y i ⊗ₖ τ i) := by
      have hterm (i : Option I) : (ρ i - γ • σ i) ⊗ₖ τ i =
          c • ((if i = none then P ⊗ₖ τ none else 0) - Y i ⊗ₖ τ i) := by
        let L : Matrix (Option I) (Option I) ℂ →ₗ[ℝ] Matrix (Option I × a) (Option I × a) ℂ :=
          (Matrix.kroneckerBilinear (R := ℝ)).flip (τ i)
        change L (ρ i - γ • σ i) = _
        rw [hdiff, map_smul, map_sub]
        cases i with
        | none => rfl
        | some i =>
          change c • ((0 : Matrix (Option I) (Option I) ℂ) ⊗ₖ τ (some i) - Y (some i) ⊗ₖ
            τ (some i)) = c • (0 - Y (some i) ⊗ₖ τ (some i))
          rw [Matrix.zero_kronecker]
      simp [hterm, ← Finset.smul_sum, Finset.sum_sub_distrib]
    rw [hout, Matrix.mul_smul, Matrix.trace_smul]
    have hp : (F * (P ⊗ₖ τ none - ∑ i, Y i ⊗ₖ τ i)).trace =
        ((1 + ε ^ 2 * C)⁻¹ : ℝ) • (1 : ℂ) := by
      simpa only [P, Y, ray, Matrix.smul_kronecker] using hpay
    rw [hp]
    simp [Complex.real_smul]

end Witness

end HockeyStickSupportLinearCore

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport

open _root_.Matrix
open scoped ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (referenceLinear)
open ConditionalHockeyStickOrthogonalReduction (act amp E posTrace ptr amp_sub_smul)
open UmegakiReferenceTransport (amp_kronecker)
open CompleteHockeyStickRefutation (completeCoefficient completeRatios ratio_le_one
  amp_psd effect_le_posTrace)
open RHLinalg (rtrace)

variable {A R B : Type} [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
  [Fintype B] [DecidableEq B]

omit [Fintype R] [DecidableEq R] in
private theorem block_sum (X : A → Matrix R R ℂ) :
    Matrix.blockDiagonal X = ∑ i, X i ⊗ₖ Matrix.single i i 1 := by
  ext ⟨r, i⟩ ⟨s, j⟩
  by_cases h : i = j
  · subst j
    simp [Matrix.blockDiagonal_apply, Matrix.sum_apply, Matrix.single,
      mul_ite, eq_comm]
  · have hne (k : A) : ¬(k = i ∧ k = j) := fun hk => h (hk.1.symm.trans hk.2)
    simp [Matrix.blockDiagonal_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Matrix.single, h, hne]

private theorem block_psd (X : A → Matrix R R ℂ) (hX : ∀ i, (X i).PosSemidef) :
    (Matrix.blockDiagonal X).PosSemidef := by
  rw [← Matrix.blockDiagonal'_submatrix_eq_blockDiagonal]
  exact (D5.S3.Quantum.Measurement.FiniteDetectionDarkSpace.positiveBlockDiagonal X hX).submatrix _

private theorem block_posPart (X : A → Matrix R R ℂ) (hX : ∀ i, (X i).IsHermitian) :
    (Matrix.blockDiagonal X)⁺ = Matrix.blockDiagonal (fun i => (X i)⁺) := by
  refine (CFC.posPart_negPart_unique
    (c := Matrix.blockDiagonal (fun i => (X i)⁻)) ?_ ?_ ?_ ?_).1
  · rw [← Matrix.blockDiagonal_sub]
    exact congrArg Matrix.blockDiagonal (funext fun i => (CFC.posPart_sub_negPart _ (hX i)).symm)
  · rw [← Matrix.blockDiagonal_mul]
    simp only [CFC.posPart_mul_negPart, ← Pi.zero_def, Matrix.blockDiagonal_zero]
  · exact (block_psd _ fun i => Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg (X i))).nonneg
  · exact (block_psd _ fun i => Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg (X i))).nonneg

private theorem block_amp (N : QuantumChannel A B) (X : A → Matrix R R ℂ) :
    amp N (Matrix.blockDiagonal X) = ∑ i, X i ⊗ₖ act N (Matrix.single i i 1) := by
  rw [block_sum]
  let L : Matrix (R × A) (R × A) ℂ →ₗ[ℂ] Matrix (R × B) (R × B) ℂ :=
    CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((referenceLinear N).comp CStarMatrix.ofMatrixₗ.toLinearMap)
  change L (∑ i, X i ⊗ₖ Matrix.single i i 1) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => amp_kronecker N (X i) (Matrix.single i i 1)

/-- For any finite channel, trivial intersection of the output supports of the
computational basis states implies complete hockey-stick coefficient one at every
parameter strictly greater than one. The witnesses use a reference of input dimension. -/
theorem result {I : Type} [Fintype I] [DecidableEq I] [Nonempty B]
    (N : QuantumChannel (Option I) B) (pivot : I) (γ : ℝ) (hγ : 1 < γ)
    (hS : (⨅ i, (act N (Matrix.single i i 1)).mulVecLin.range) = ⊥) :
    completeCoefficient N γ false = 1 := by
  let τ (i : Option I) := act N (Matrix.single i i 1)
  have htrτ : (τ none).trace = 1 := by
    exact (N.trace_preserving (CStarMatrix.ofMatrix (Matrix.single (none : Option I) none 1))).trans
      (by change (Matrix.single (none : Option I) none (1 : ℂ)).trace = 1; simp)
  obtain ⟨C, hC, hWitness⟩ := HockeyStickSupportLinearCore.simplex_witness τ hS htrτ pivot γ hγ
  have hBound : BddAbove (insert 0 (completeRatios N γ false)) :=
    ⟨1, fun _ h => ratio_le_one N γ false h⟩
  have hUpper : completeCoefficient N γ false ≤ 1 :=
    csSup_le ⟨0, Set.mem_insert _ _⟩ fun _ h => ratio_le_one N γ false h
  apply le_antisymm hUpper
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  have hden : 0 < 1 + C := by linarith
  let ε : ℝ := min 1 ((1 - t) / (1 + C))
  have hε : 0 < ε := lt_min zero_lt_one (div_pos (sub_pos.mpr ht) hden)
  have hε₁ : ε ≤ 1 := min_le_left _ _
  have hε₂ : ε * (1 + C) ≤ 1 - t :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hεC : ε ^ 2 * C ≤ 1 - t := by
    calc
      ε ^ 2 * C ≤ ε * C := mul_le_mul_of_nonneg_right (by nlinarith) hC
      _ ≤ ε * (1 + C) := by nlinarith
      _ ≤ 1 - t := hε₂
  have hfac : t ≤ (1 + ε ^ 2 * C)⁻¹ := by
    have hp : 0 < 1 + ε ^ 2 * C := by positivity
    rw [← mul_one ((1 + ε ^ 2 * C)⁻¹), le_inv_mul_iff₀ hp]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.le) (mul_nonneg (sq_nonneg ε) hC)]
  obtain ⟨c, ρ, σ, F, hc, hρ, hσ, hsum, htr, hF, hF₁, hinput, hout⟩ :=
    hWitness ε hε.ne'
  let P := Matrix.blockDiagonal ρ
  let Q := Matrix.blockDiagonal σ
  have hP := block_psd ρ hρ
  have hQ := block_psd σ hσ
  have hPtr : P.trace = 1 := by rwa [Matrix.trace_blockDiagonal, ← Matrix.trace_sum]
  have hQtr : Q.trace = 1 := by
    rwa [Matrix.trace_blockDiagonal, ← Matrix.trace_sum, ← hsum]
  have hPQ : ptr P = ptr Q := by
    change D5.S3.Quantum.Recovery.BKMFlagRefinement.marginal ρ =
      D5.S3.Quantum.Recovery.BKMFlagRefinement.marginal σ
    simpa only [D5.S3.Quantum.Recovery.BKMFlagRefinement.marginal_eq_sum] using hsum
  let D : Option I → Matrix (Option I) (Option I) ℂ := fun i => ρ i - γ • σ i
  have hD : P - γ • Q = Matrix.blockDiagonal D := by
    change Matrix.blockDiagonal ρ - γ • Matrix.blockDiagonal σ = Matrix.blockDiagonal (ρ - γ • σ)
    rw [Matrix.blockDiagonal_sub, Matrix.blockDiagonal_smul]
  have hDherm (i : Option I) : (D i).IsHermitian :=
    (hρ i).isHermitian.sub ((hσ i).isHermitian.smul (IsSelfAdjoint.all γ))
  have hE : E γ P Q = c := by
    change ((P - γ • Q)⁺).trace.re = c
    rw [hD, block_posPart D hDherm, Matrix.trace_blockDiagonal, hinput, Complex.ofReal_re]
  have hdiff : amp N P - γ • amp N Q = ∑ i, D i ⊗ₖ τ i := by
    rw [← amp_sub_smul, hD, block_amp]
  have hpay : c * (1 + ε ^ 2 * C)⁻¹ ≤ E γ (amp N P) (amp N Q) := by
    have hh := (amp_psd N hP).isHermitian.sub ((amp_psd N hQ).isHermitian.smul
      (IsSelfAdjoint.all γ))
    have hb := effect_le_posTrace hh hF hF₁
    have hre : rtrace (F * (amp N P - γ • amp N Q)) = c * (1 + ε ^ 2 * C)⁻¹ := by
      rw [hdiff]
      change (F * ∑ i, D i ⊗ₖ τ i).trace.re = _
      rw [hout]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    change rtrace (F * (amp N P - γ • amp N Q)) ≤ E γ (amp N P) (amp N Q) at hb
    linarith
  have hm : E γ (amp N P) (amp N Q) / E γ P Q ∈ completeRatios N γ false := by
    exact ⟨Option I, inferInstance, inferInstance, P, Q, hP, hPtr, hQ, hQtr, hPQ,
      by simp, hE ▸ hc, rfl⟩
  refine hfac.trans ((le_div_iff₀ (hE ▸ hc)).mpr ?_) |>.trans
    (le_csSup hBound (Set.mem_insert_of_mem _ hm))
  simpa [hE, mul_comm] using hpay

end D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport
