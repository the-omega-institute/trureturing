/- GID: D5/S3/Quantum/ProcessReconstruction/ExactConstantOne
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/ExactConstantOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete local diamond errors bound global unitary error with constant one. -/

import D5.S3.Quantum.ProcessReconstruction.DominantReflection
import D5.S3.Quantum.ProcessReconstruction.RobustDiamond
import D5.S3.Quantum.ProcessReconstruction.SpectrumGeometry

/-!
Arrighi, Nesme and Werner (arXiv:0711.3975, Theorem 1) use conjugated
local SWAPs. Huang et al. (arXiv:2401.10095, Eq. (109) and Lemma 9)
use SWAP sewing and bound its error using Pauli observables. Bravyi,
Parham and Tran compare their SWAP statistic to the global unitary-channel
distance (DOI 10.4230/LIPIcs.ITCS.2026.27, §2, Lemma 4). The angular and
reflection arguments here give a bound for complete output-channel errors.

This is a deterministic reconstruction inequality for complete single-output
errors on the global input. The multiplicative approximation algorithm
question in Bravyi–Parham–Tran §1.2 is a separate problem.
-/

noncomputable section

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator InnerProductSpace
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteStateChannel

namespace UnitaryReconstruction

universe u

local notation "ℓ²" => EuclideanSpace ℂ
local notation "L" => Matrix.toEuclideanCLM (𝕜 := ℂ)

section Sites

variable {ι : Type u} [Fintype ι] [DecidableEq ι] (d : ι → Type u)
  [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)] [∀ i, Nonempty (d i)]

local notation:max "B" W:arg => referenceUnitary (System d) W

omit [∀ i, Nonempty (d i)] in
theorem spectral_chord_lt_of_small_localErrors (W : unitaryGroup (System d) ℂ)
    (hs : ∀ i, localError d i W 1 ≤ 1)
    (htotal : (∑ i, localError d i W 1) < 2)
    {p q : ℂ} (hp : p ∈ spectrum ℂ W.val) (hq : q ∈ spectrum ℂ W.val) :
    ‖p - q‖ < Real.sqrt 3 := by
  let : InnerProductSpace ℝ (ℓ² (System d × System d)) :=
    InnerProductSpace.rclikeToReal ℂ _
  obtain ⟨x, hx, hxe⟩ := spectrum_unit_eigenvector W hp
  obtain ⟨y, hy, hye⟩ := spectrum_unit_eigenvector W hq
  let v := tensorVector x y
  have hv : ‖v‖ = 1 := tensorVector_norm_one hx hy
  let f (s : Finset ι) := L (partiallySwapped d s W).val v
  have hf (s : Finset ι) : ‖f s‖ = 1 :=
    (unitary_euclidean_norm _ _).trans hv
  have h := finset_unit_chord_lt_sqrt_three Finset.univ f (fun i => localError d i W 1)
    (fun s _ => hf s) (fun _ _ => diamondDistance_nonneg' _ _) (fun i _ => hs i) (by
      intro s _ i _ hi
      change ‖L _ v - L _ v‖ ≤ _
      rw [← _root_.sub_apply, ← map_sub]
      exact (Matrix.l2_opNorm_mulVec _ v).trans
        (by simpa only [hv, mul_one, opNorm] using norm_partial_step d W s i hi)) htotal
  have huniv : f Finset.univ = p • v := by
    change L (partiallySwapped d Finset.univ W).val (tensorVector x y) = _
    rw [partiallySwapped_univ, kron_tensorVector, hxe, map_one, one_apply_eq_self]
    apply (WithLp.equiv 2 _).injective
    ext ⟨i,j⟩
    simp [v, tensorVector, mul_assoc]
  have hempty : f ∅ = q • v := by
    change L (partiallySwapped d ∅ W).val (tensorVector x y) = _
    rw [partiallySwapped_empty]
    change L ((1 : Matrix (System d) (System d) ℂ) ⊗ₖ W.val) (tensorVector x y) = _
    rw [kron_tensorVector, hye, map_one, one_apply_eq_self]
    apply (WithLp.equiv 2 _).injective
    ext ⟨i,j⟩
    simp [v, tensorVector, mul_left_comm]
  simpa only [huniv, hempty, ← sub_smul, norm_smul, hv, mul_one] using h

theorem diamond_le_sum_localError_against_one (W : unitaryGroup (System d) ℂ) :
    diamondDistance (conjugation W) (conjugation 1) ≤ ∑ i, localError d i W 1 := by
  classical
  by_cases h : (∑ i, localError d i W 1) < 2
  · have hrel : relativeUnitary W 1 = W := by simp [relativeUnitary]
    have hchord {p q : ℂ} (hp : p ∈ spectrum ℂ W.val) (hq : q ∈ spectrum ℂ W.val) :
        ‖p - q‖ ≤ ∑ i, localError d i W 1 :=
      (spectrum_chord_le W p q hp hq).trans (by
        have h' := relative_kron_norm W 1
        rw [hrel] at h'
        change opNorm (W.valᴴ ⊗ₖ W.val - 1) =
          opNorm (W.valᴴ ⊗ₖ W.val - (1 : Matrix (System d) (System d) ℂ)ᴴ ⊗ₖ
            (1 : Matrix (System d) (System d) ℂ)) at h'
        rw [h']
        exact swap_sewing_opNorm_le d W 1)
    have hnorm (z : ℂ) (hz : z ∈ spectrum ℂ W.val) : ‖z‖ = 1 :=
      spectrum.norm_eq_one_of_unitary W.prop hz
    by_cases hlarge : ∃ i, 1 ≤ localError d i W 1
    · obtain ⟨i, hi⟩ := hlarge
      have hnot : (0 : ℂ) ∉ convexHull ℝ (spectrum ℂ W.val) := by
        intro hz
        obtain ⟨v, hv, he⟩ := overlap_of_mem_spectral_hull W 0 hz
        exact no_zero_overlap_of_dominant d W i hi h v hv he
      have hf := Matrix.finite_spectrum W.val
      have hn := spectrum.nonempty W.val
      obtain ⟨c, t, hc, ht, _, hplane, p, hp, q, hq, heq⟩ :=
        unitCircle_halfPlane_with_chord_of_zero_not_mem_convexHull hf hn hnorm hnot
      have hbound := diamond_le_of_spectral_halfPlane W 1 c hc t ht.le (by rwa [hrel])
      exact hbound.trans (heq ▸ hchord hp hq)
    · have hsmall (i : ι) : localError d i W 1 ≤ 1 :=
        (lt_of_not_ge fun hi => hlarge ⟨i, hi⟩).le
      obtain ⟨p, hp, q, hq, hmax⟩ := spectral_diameter_attained W
      obtain ⟨c, hc, t, ht, heq, hplane⟩ := circle_diameter_halfPlane
        (hnorm p hp) (hnorm q hq) (spectral_chord_lt_of_small_localErrors d W hsmall h hp hq)
      have hspec : ∀ z ∈ spectrum ℂ (relativeUnitary W 1).val, t ≤ (c * z).re := by
        rw [hrel]
        exact fun z hz => hplane z (hnorm z hz) (hmax z hz p hp) (hmax z hz q hq)
      have hroot : 2 * Real.sqrt (1 - t ^ 2) = ‖p - q‖ := by
        apply (sq_eq_sq₀ (by positivity) (norm_nonneg _)).mp
        rw [mul_pow, Real.sq_sqrt (by nlinarith [sq_nonneg ‖p - q‖])]
        nlinarith
      exact (diamond_le_of_spectral_halfPlane W 1 c hc t ht.le hspec).trans
        (hroot ▸ hchord hp hq)
  · exact (diamondDistance_le_two _ _).trans (le_of_not_gt h)

/-- The sharp unhalved diamond inequality on arbitrary finite products of
nonempty sites. Each summand discards every output except the indicated
site and takes the diamond distance on the full global input. -/
theorem diamond_le_sum_localError (U V : unitaryGroup (System d) ℂ) :
    diamondDistance (conjugation U) (conjugation V) ≤ ∑ i, localError d i U V := by
  have hglobal := diamondDistance_precompose_unitary (conjugation U) (conjugation V) (star V)
  rw [← conjugation_mul, ← conjugation_mul, Unitary.mul_star_self] at hglobal
  have hlocal (i : ι) : localError d i (U * star V) 1 = localError d i U V := by
    have h' := diamondDistance_precompose_unitary (siteChannel d i U) (siteChannel d i V) (star V)
    change diamondDistance ((reducedConjugation (splitSite d i) U).comp (conjugation (star V)))
      ((reducedConjugation (splitSite d i) V).comp (conjugation (star V))) = _ at h'
    rw [← reducedConjugation_mul, ← reducedConjugation_mul, Unitary.mul_star_self] at h'
    exact h'
  rw [← hglobal, ← Finset.sum_congr rfl (fun i _ => hlocal i)]
  exact diamond_le_sum_localError_against_one d (U * star V)

/-- The bound applies to every joint input state on the total input and an
arbitrary finite reference. -/
theorem referenceError_le_sum_localError (U V : unitaryGroup (System d) ℂ)
    {r : Type*} [Fintype r] [DecidableEq r] (ρ : DensityState (r × System d)) :
    referenceError (conjugation U) (conjugation V) ρ ≤ ∑ i, localError d i U V :=
  (referenceError_le_diamond _ _ ρ).trans (diamond_le_sum_localError d U V)

end Sites

end UnitaryReconstruction

noncomputable section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace UnitaryReconstruction

private theorem basisState_dot {a : Type*} [Fintype a] [DecidableEq a] (x : a) :
    star (Pi.single x (1 : ℂ)) ⬝ᵥ Pi.single x (1 : ℂ) = 1 := by
  simp [dotProduct, Pi.single_apply]

private theorem distinguish_basis_swap {a : Type*} [Fintype a] [DecidableEq a] {x y : a}
    (hxy : x ≠ y) :
    diamondDistance (conjugation (permUnitary (Equiv.swap x y))) (conjugation 1) = 2 := by
  let v (z : a) : Unit × a → ℂ := Pi.single ((),z) 1
  let ρ := pureState (v x) (basisState_dot ((),x))
  let U := permUnitary (Equiv.swap x y)
  have hvec : (referenceUnitary Unit U).val *ᵥ v x = v y := by
    ext ⟨r,z⟩
    cases r
    simp only [v, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change (1 : Matrix Unit Unit ℂ) () () * (Equiv.swap x y).permMatrix ℂ z x =
      if ((),z) = ((),y) then 1 else 0
    simp only [Matrix.one_apply_eq, one_mul, perm_entry, Prod.mk.injEq]
    have he : Equiv.swap x y z = x ↔ z = y := by
      rw [← Equiv.eq_symm_apply, Equiv.symm_swap, Equiv.swap_apply_left]
    simp [he]
  have hstate (z : a) : (vecMulVec (v z) (star (v z))).trace = 1 := by
    rw [Matrix.trace_vecMulVec, dotProduct_comm]
    exact basisState_dot ((),z)
  have hinner : star (v y) ⬝ᵥ v x = 0 := by
    simp [v, dotProduct, Pi.single_apply, hxy]
  have hstar : star (v x) ᵥ* (referenceUnitary Unit U).valᴴ = star (v y) := by
    rw [← Matrix.star_mulVec, hvec]
  have herr : referenceError (conjugation U) (conjugation 1) ρ = 2 := by
    change traceNorm (referenceMatrix (conjugation U) (vecMulVec (v x) (star (v x))) -
      referenceMatrix (conjugation 1) (vecMulVec (v x) (star (v x)))) = 2
    rw [referenceMatrix_conjugation, referenceMatrix_conjugation, referenceUnitary_one]
    change traceNorm ((referenceUnitary Unit U).val * vecMulVec (v x) (star (v x)) *
      (referenceUnitary Unit U).valᴴ -
        1 * vecMulVec (v x) (star (v x)) * (1 : Matrix _ _ ℂ)ᴴ) = 2
    rw [Matrix.mul_vecMulVec, hvec, Matrix.vecMulVec_mul, hstar,
      Matrix.conjTranspose_one, one_mul, mul_one,
      traceNorm_sub_orthogonal _ _ (Matrix.posSemidef_vecMulVec_self_star _)
        (Matrix.posSemidef_vecMulVec_self_star _) (by
          rw [Matrix.vecMulVec_mul_vecMulVec, hinner, zero_smul]
          ext i j; simp [Matrix.vecMulVec]), hstate, hstate]
    norm_num
  exact le_antisymm (diamondDistance_le _ _ (by norm_num) fun _ => referenceError_le_two _ _)
    (herr ▸ referenceError_le_diamond _ _ ρ)

/-- A single qubit reaches equality with both sides equal to two. -/
theorem sharp_one_site :
    ∃ U V : unitaryGroup (System (fun _ : Unit => Bool)) ℂ,
      diamondDistance (conjugation U) (conjugation V) = 2 ∧
      (∑ i, localError (fun _ : Unit => Bool) i U V) = 2 := by
  let x : Unit → Bool := fun _ => false
  let y : Unit → Bool := fun _ => true
  let U := permUnitary (Equiv.swap x y)
  have hxy : x ≠ y := by
    intro he
    exact Bool.false_ne_true (congrFun he ())
  have hglobal := distinguish_basis_swap hxy
  refine ⟨U, 1, hglobal, le_antisymm ?_ ?_⟩
  · rw [Fintype.sum_unique]
    exact diamondDistance_le _ _ (by norm_num) fun _ => referenceError_le_two _ _
  · rw [← hglobal]
    exact diamond_le_sum_localError (fun _ : Unit => Bool) U 1

end UnitaryReconstruction
