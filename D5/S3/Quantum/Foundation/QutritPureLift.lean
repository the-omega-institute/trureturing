/- GID: D5/S3/Quantum/Foundation/QutritPureLift
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/QutritPureLift
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original pure lifts are unique at unit support across an actual qutrit face. -/

import D5.S3.Quantum.Foundation.WholePairBallConfirmation
import D5.S3.Quantum.Foundation.HitSectionGeneration
import D5.S3.Quantum.Foundation.HermitianExclusionBall
import D5.S3.Quantum.Matrix.CartesianVariance
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Unique original pure lifts across the homogeneous span of an actual qutrit face. -/

noncomputable section
open scoped Matrix ComplexOrder RealInnerProductSpace BigOperators

namespace D5.S3.Quantum.Foundation.QutritPureLift

open CircuitBalancedConfirmation WholePairBallConfirmation
open HitSectionGeneration SectionROGFrame

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  {C : PointedCone ℝ V} {u g : V →ₗ[ℝ] ℝ}

/-- Two different original pure zeros of a positive support on one actual
pair ball force the support to vanish on the entire ball. -/
private theorem zero_on_pairBase
    {p q : pure C u} (chart : BallChart C u p q)
    (hg : ∀ x ∈ C, 0 ≤ g x)
    (x y : pure C u) (hxy : x ≠ y)
    (hx : (x : V) ∈ pairBase C u p q)
    (hy : (y : V) ∈ pairBase C u p q)
    (hxg : g x = 0) (hyg : g y = 0) :
    ∀ z ∈ pairBase C u p q, g z = 0 := by
  rw [← chart.whole] at hx hy
  obtain ⟨v, hv, hvx⟩ := hx
  obtain ⟨w, hw, hwy⟩ := hy
  have hvn : ‖v‖ = 1 := chart_pure_norm chart (by simpa using hv)
    (by rw [hvx]; exact x.property)
  have hwn : ‖w‖ = 1 := chart_pure_norm chart (by simpa using hw)
    (by rw [hwy]; exact y.property)
  have hformula := affine_zero_antipode (g.toAffineMap.comp chart.param)
    (n := -v) (by simpa using hvn)
    (fun s hs => hg _ (chart_mem chart hs).1.1)
    (by change g (chart.param (- -v)) = 0; simpa [hvx] using hxg)
  have hformula' (s) :
      g (chart.param s) =
        g (chart.param (-v)) / 2 * (1 + ⟪-v, s⟫) := hformula s
  have hzero : g (chart.param (-v)) = 0 := by
    by_contra hne
    have he := hformula' w
    rw [hwy, hyg] at he
    have hi : 1 + ⟪-v, w⟫ = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left (div_ne_zero hne (by norm_num))
    rw [inner_neg_left] at hi
    have hn : ‖v - w‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hvn, hwn]
      linarith
    have hvw : v = w := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
    apply hxy
    apply Subtype.ext
    calc
      (x : V) = chart.param v := hvx.symm
      _ = chart.param w := congrArg chart.param hvw
      _ = (y : V) := hwy
  intro z hz
  rw [← chart.whole] at hz
  obtain ⟨s, _, rfl⟩ := hz
  rw [hformula' s, hzero]
  simp

omit [FiniteDimensional ℝ V] in
/-- A nonnegative difference of two original pure rays with the same
positive support value forces equality. The weights refer to the original
unit, and the second summand is in the original cone. -/
private theorem pure_lift_eq_of_add
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (p q : pure C u) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hgp : g (a • (p : V)) = 1) (hgq : g (b • (q : V)) = 1)
    {d : V} (hd : d ∈ C)
    (heq : a • (p : V) = b • (q : V) + d) :
    a • (p : V) = b • (q : V) := by
  by_cases hd0 : d = 0
  · simpa [hd0] using heq
  have hdu := hu d hd hd0
  have hmass : a = b + u d := by
    have h := congrArg u heq
    simpa only [map_add, map_smul, smul_eq_mul,
      (pure_mem p).2, (pure_mem q).2, mul_one] using h
  have hmix : (b / a) • (q : V) + (u d / a) • ((u d)⁻¹ • d) = (p : V) := by
    have h := congrArg (fun z : V => a⁻¹ • z) heq
    simp only [smul_add, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at h
    have hc : u d / a * (u d)⁻¹ = a⁻¹ := by field_simp [ha.ne', hdu.ne']
    rw [smul_smul, hc]
    have hb' : b / a = a⁻¹ * b := by rw [div_eq_mul_inv, mul_comm]
    rw [hb']
    exact h.symm
  have hseg : (p : V) ∈ openSegment ℝ (q : V) ((u d)⁻¹ • d) :=
    ⟨b / a, u d / a, div_pos hb ha, div_pos hdu ha, by
      rw [← add_div, ← hmass, div_self ha.ne'], hmix⟩
  have hpq : (q : V) = p := p.property.2 (pure_mem q)
    (normalized_mem hu hd hd0) hseg
  have hga : a * g p = 1 := by simpa using hgp
  have hgb : b * g p = 1 := by simpa [hpq] using hgq
  have hgn : g p ≠ 0 := by
    intro h
    simp [h] at hga
  have hab : a = b := mul_right_cancel₀ hgn (hga.trans hgb.symm)
  rw [hpq, hab]

/-- The indefinite crossing. The side with a single spectral atom fixes one
actual pair ball. Every cone face containing those endpoints must also
contain an opposite-sign atom. Its two different pure support zeros force
the entire ball into the support hyperplane. -/
private theorem crossing_impossible
    (F : C.Face) (hg : ∀ z ∈ C, 0 ≤ g z)
    (hgF : ∀ z ∈ F, g z = 0) (hB : wholePairBalls C u)
    (p q x y : pure C u) (hxF : (x : V) ∈ F) (hyF : (y : V) ∈ F)
    (hxy : x ≠ y) {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hgp : g (a • (p : V)) = 1)
    {z : V} (hz : z ∈ F)
    (heq : a • (p : V) + c • (x : V) =
      b • (q : V) + d • (y : V) + z) : False := by
  have hpx : p ≠ x := by
    intro h
    have hzero : g (p : V) = 0 := by rw [h]; exact hgF _ hxF
    simp [hzero] at hgp
  obtain ⟨chart⟩ := hB p x hpx
  have hxpair : (x : V) ∈ pairBase C u p x :=
    ⟨pure_mem x, fun _ _ hx => hx⟩
  have hypair : (y : V) ∈ pairBase C u p x := by
    refine ⟨pure_mem y, ?_⟩
    intro G hpG hxG
    have hsum : b • (q : V) + d • (y : V) + z ∈ G := by
      rw [← heq]
      exact G.toPointedCone.add_mem (G.toPointedCone.smul_mem ha.le hpG)
        (G.toPointedCone.smul_mem hc.le hxG)
    have hqC := C.smul_mem hb.le (pure_mem q).1
    have hyC := C.smul_mem hd.le (pure_mem y).1
    have hsub := G.isFaceOf.mem_of_add_mem_left (C.add_mem hqC hyC)
      (F.isFaceOf.le hz) hsum
    exact (G.toPointedCone.smul_mem_iff hd).mp
      (G.isFaceOf.mem_of_add_mem_right hqC hyC hsub)
  have hpPair : (p : V) ∈ pairBase C u p x :=
    ⟨pure_mem p, fun _ hp _ => hp⟩
  have hzero := zero_on_pairBase chart hg x y hxy hxpair hypair
    (hgF _ hxF) (hgF _ hyF) p hpPair
  simp [hzero] at hgp

/-- The exact geometry needed from a three-state signed spectral expansion.
The three labels belong to the entire original face and are pairwise distinct.
Zero coefficients are allowed, so singular and semidefinite differences are
included. -/
private theorem scaled_pure_eq_of_three_term_difference
    (F : C.Face) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : ∀ x ∈ C, 0 ≤ g x) (hgF : ∀ x ∈ F, g x = 0)
    (hB : wholePairBalls C u)
    (p q : pure C u) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hgp : g (a • (p : V)) = 1) (hgq : g (b • (q : V)) = 1)
    (v : Fin 3 → pure C u) (hinj : Function.Injective v)
    (hvF : ∀ i, (v i : V) ∈ F)
    (c : Fin 3 → ℝ)
    (heq : a • (p : V) - b • (q : V) = ∑ i, c i • (v i : V)) :
    a • (p : V) = b • (q : V) := by
  classical
  by_cases hpos : ∀ i, 0 ≤ c i
  · have hd : a • (p : V) - b • (q : V) ∈ C := by
      rw [heq]
      exact C.sum_mem (fun i _ => C.smul_mem (hpos i) (pure_mem (v i)).1)
    exact pure_lift_eq_of_add hu p q ha hb hgp hgq hd (by abel)
  by_cases hneg : ∀ i, c i ≤ 0
  · have heq' : b • (q : V) - a • (p : V) = ∑ i, (-c i) • (v i : V) := by
      calc
        _ = -(a • (p : V) - b • (q : V)) := by abel
        _ = _ := by rw [heq, ← Finset.sum_neg_distrib]; simp only [neg_smul]
    have hd : b • (q : V) - a • (p : V) ∈ C := by
      rw [heq']
      exact C.sum_mem (fun i _ => C.smul_mem (neg_nonneg.mpr (hneg i)) (pure_mem (v i)).1)
    exact (pure_lift_eq_of_add hu q p hb ha hgq hgp hd (by abel)).symm
  push Not at hpos hneg
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj⟩ := hneg
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    linarith
  have hthird : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  obtain ⟨k, hki, hkj⟩ := hthird
  have hsum : (∑ l, c l • (v l : V)) =
      c i • (v i : V) + c j • (v j : V) + c k • (v k : V) := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all [Fin.sum_univ_three] <;> abel
  rw [hsum] at heq
  exfalso
  by_cases hk : 0 ≤ c k
  · apply crossing_impossible F hg hgF hB p q (v i) (v j) (hvF i) (hvF j)
      (fun h => hij (hinj h)) ha hb (neg_pos.mpr hi) hj hgp
      (F.toPointedCone.smul_mem hk (hvF k))
    simp only [neg_smul]
    calc
      a • (p : V) + -(c i • (v i : V)) =
          b • (q : V) + (a • (p : V) - b • (q : V)) - c i • (v i : V) := by abel
      _ = _ := by rw [heq]; abel
  · apply crossing_impossible F hg hgF hB q p (v j) (v i) (hvF j) (hvF i)
      (fun h => hij (hinj h).symm) hb ha hj (neg_pos.mpr hi) hgq
      (F.toPointedCone.smul_mem (neg_nonneg.mpr (le_of_not_ge hk)) (hvF k))
    simp only [neg_smul]
    calc
      b • (q : V) + c j • (v j : V) =
          a • (p : V) - (a • (p : V) - b • (q : V)) + c j • (v j : V) := by abel
      _ = _ := by rw [heq]; abel

private theorem hermitian_spectral_sum (A : HermitianMat (Fin 3) ℂ) :
    A = ∑ i, A.H.eigenvalues i • rankOne (A.H.eigenvectorBasis i) := by
  apply HermitianMat.ext
  change A.mat = (∑ i, A.H.eigenvalues i • rankOne (A.H.eigenvectorBasis i)).mat
  rw [HermitianMat.mat_finset_sum]
  simp only [HermitianMat.mat_smul]
  exact D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum A.mat A.H

private theorem rankOne_basis_injective
    (B : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3))) :
    Function.Injective (fun i => rankOne (B i)) := by
  intro i j h
  by_contra hij
  have horth : star (B j : Fin 3 → ℂ) ⬝ᵥ (B i : Fin 3 → ℂ) = 0 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [orthonormal_iff_ite.mp B.orthonormal, Ne.symm hij]
  have hself : star (B i : Fin 3 → ℂ) ⬝ᵥ (B i : Fin 3 → ℂ) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simp [orthonormal_iff_ite.mp B.orthonormal]
  have hact := congrArg (fun A : HermitianMat (Fin 3) ℂ => A.mat *ᵥ (B i : Fin 3 → ℂ)) h
  change Matrix.vecMulVec (B i : Fin 3 → ℂ) (star (B i : Fin 3 → ℂ)) *ᵥ
      (B i : Fin 3 → ℂ) =
    Matrix.vecMulVec (B j : Fin 3 → ℂ) (star (B j : Fin 3 → ℂ)) *ᵥ
      (B i : Fin 3 → ℂ) at hact
  have hi : (B i : Fin 3 → ℂ) = 0 := by
    simpa [Matrix.vecMulVec_mulVec, hself, horth] using hact
  exact B.orthonormal.ne_zero i (by simpa using congrArg (WithLp.toLp 2) hi)

omit [FiniteDimensional ℝ V] in
/-- Spectral atoms of the actual complex qutrit face, pulled back along its
real-linear trace-preserving PSD coordinates. Each atom is an original pure
state of C by the faciality of F. -/
private theorem original_qutrit_spectral_expansion
    (F : C.Face)
    (e : Submodule.span ℝ (F : Set V) ≃ₗ[ℝ] HermitianMat (Fin 3) ℂ)
    (hcone : ∀ x : Submodule.span ℝ (F : Set V), (x : V) ∈ F ↔ 0 ≤ e x)
    (htrace : ∀ x : Submodule.span ℝ (F : Set V), (e x).trace = u x)
    (d : Submodule.span ℝ (F : Set V)) :
    ∃ (v : Fin 3 → pure C u) (c : Fin 3 → ℝ),
      Function.Injective v ∧ (∀ i, (v i : V) ∈ F) ∧
      (d : V) = ∑ i, c i • (v i : V) := by
  classical
  let S := Submodule.span ℝ (F : Set V)
  let I : HermitianMat (Fin 3) ℂ →ₗ[ℝ] V := S.subtype.comp e.symm.toLinearMap
  have hI : Function.Injective I :=
    Subtype.val_injective.comp e.symm.injective
  let K := CircuitBalancedConfirmation.base
    (HermitianExclusionKernel.cone : PointedCone ℝ (HermitianMat (Fin 3) ℂ))
    HermitianExclusionKernel.unit
  have hK : K = SectionROGFrame.base (⊤ : Submodule ℝ (HermitianMat (Fin 3) ℂ)) := by
    ext X
    simp [K, CircuitBalancedConfirmation.base, SectionROGFrame.base,
      HermitianExclusionKernel.cone, HermitianExclusionKernel.unit]
  have hIimage : I '' K = CircuitBalancedConfirmation.base F.toPointedCone u := by
    ext x
    constructor
    · rintro ⟨X, hX, rfl⟩
      rw [hK] at hX
      refine ⟨(hcone (e.symm X)).mpr (by simpa using hX.2.1), ?_⟩
      have ht : u (e.symm X) = X.trace := by
        simpa using (htrace (e.symm X)).symm
      exact ht.trans hX.2.2
    · intro hx
      let z : S := ⟨x, Submodule.subset_span hx.1⟩
      refine ⟨e z, ?_, by simp [I, z]⟩
      rw [hK]
      exact ⟨Submodule.mem_top, (hcone z).mp hx.1, (htrace z).trans hx.2⟩
  let A := e d
  let P : Fin 3 → HermitianMat (Fin 3) ℂ := fun i => rankOne (A.H.eigenvectorBasis i)
  have hPpure (i : Fin 3) : P i ∈ K.extremePoints ℝ := by
    rw [hK, whole_pure_carrier _ HermitianExclusionBall.whole_rog]
    exact ⟨A.H.eigenvectorBasis i, A.H.eigenvectorBasis.orthonormal.norm_eq_one i,
      rfl, Submodule.mem_top⟩
  have hKconv : Convex ℝ K := CircuitBalancedConfirmation.base_convex _ _
  have hVpure (i : Fin 3) : I (P i) ∈ pure C u := by
    have h := CircuitBalancedConfirmation.affine_extreme_image K hKconv
      I.toAffineMap (fun _ _ _ _ he => hI he) (hPpure i)
    change I (P i) ∈ (I '' K).extremePoints ℝ at h
    rw [hIimage] at h
    exact (face_base_extreme F).extremePoints_subset_extremePoints h
  let v : Fin 3 → pure C u := fun i => ⟨I (P i), hVpure i⟩
  have hvF (i : Fin 3) : (v i : V) ∈ F := by
    have hmem : I (P i) ∈ I '' K := ⟨P i, (hPpure i).1, rfl⟩
    rw [hIimage] at hmem
    exact hmem.1
  refine ⟨v, A.H.eigenvalues, ?_, hvF, ?_⟩
  · intro i j h
    exact rankOne_basis_injective A.H.eigenvectorBasis
      (hI (congrArg (fun p : pure C u => (p : V)) h))
  · have he := congrArg I (hermitian_spectral_sum A)
    simpa [I, A, P, v, map_sum, map_smul] using he

/-- Step 1 of the short carrier-fifteen quotient proof.
The quotient is exactly by the homogeneous span of the actual face F.
The set on which it is injective consists of positive multiples of literal
original pure states scaled to g = 1. -/
theorem unique_original_pure_lift
    (F : C.Face) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : ∀ x ∈ C, 0 ≤ g x) (hgF : ∀ x ∈ F, g x = 0)
    (hB : wholePairBalls C u)
    (e : Submodule.span ℝ (F : Set V) ≃ₗ[ℝ] HermitianMat (Fin 3) ℂ)
    (hcone : ∀ x : Submodule.span ℝ (F : Set V), (x : V) ∈ F ↔ 0 ≤ e x)
    (htrace : ∀ x : Submodule.span ℝ (F : Set V), (e x).trace = u x) :
    Set.InjOn (Submodule.span ℝ (F : Set V)).mkQ
      {r : V | ∃ (p : pure C u) (a : ℝ), 0 < a ∧ r = a • (p : V) ∧ g r = 1} := by
  rintro _ ⟨p, a, ha, rfl, hgp⟩ _ ⟨q, b, hb, rfl, hgq⟩ he
  let S := Submodule.span ℝ (F : Set V)
  have hd : a • (p : V) - b • (q : V) ∈ S := by
    exact (Submodule.Quotient.eq S).mp (by simpa only [Submodule.mkQ_apply] using he)
  obtain ⟨v, c, hinj, hvF, heq⟩ :=
    original_qutrit_spectral_expansion F e hcone htrace ⟨_, hd⟩
  exact scaled_pure_eq_of_three_term_difference F hu hg hgF hB
    p q ha hb hgp hgq v hinj hvF c heq

end D5.S3.Quantum.Foundation.QutritPureLift
