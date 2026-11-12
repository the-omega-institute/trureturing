/-
Original mixed-Jacobi proof of charged translation.

Use p=-a(alpha,b), q=-a(beta,b)-1, r=-bilinear(alpha,beta)-1.
The three ACTUAL families have support in {0}, {0}, and the empty set.
Source products kill the nonzero left indices. The finite Taylor proof in
ActualGroundChargedSelection kills the original E inner modes on the right.
No Z-product identity, spectrum, action law, or inverse is a premise.

The scalar is the unchanged lower-triangular PLUS half-diagonal epsilon.
The typed inverse explicitly transports the resulting weight index back
to b. Raw Omega equalities below state both inverse laws without casts.
There is no nonzero-module, positive-rank, or nonzero-charge hypothesis.
-/
import D5.S3.VertexAlgebra.Modules.ActualGroundChargedSelection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.Modules.ActualGroundChargedTranslations

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FullJacobiCurrentTransport ActualCurrentTaylor ActualChargedGroundCalculus
open ActualGroundFiniteReconstruction ActualGroundJointWeights ActualGroundChargedSelection
open StateFieldResidueReconstruction (integerBinomial)

universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]
variable (J : FullJacobiLatticeModule D M)
variable (hNil : OriginalPositiveNilpotence J)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

/-- Independent support audit of the actual source-product family. -/
theorem charged_left_support (α β b : Charge D) (v : Omega J) :
    Function.support (jacobiLeft J.stateField (groundState D α) (groundState D β)
      v.val (-weightPairing α b) (-weightPairing β b - 1)
      (-bilinear D α β - 1)) ⊆ ({0} : Set ℕ) := by
  intro j hj
  by_contra hn
  have hj0 : j ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn
  have hp := source_ground_above_leading α β j hj0
  exact hj (by simp [jacobiLeft, hp, mode])

include hNil H hHG hGH in
/-- Independent support audit of the first original mode-product family. -/
theorem charged_first_support (α β b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    Function.support (jacobiFirst J.stateField (groundState D α) (groundState D β)
      v.val (-weightPairing α b) (-weightPairing β b - 1)
      (-bilinear D α β - 1)) ⊆ ({0} : Set ℕ) := by
  intro j hj
  by_contra hn
  have hj0 : j ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn
  have he := E_above_leading J hNil H hHG hGH β b
    (-weightPairing β b - 1 + j) v hv (by omega)
  apply hj
  change (((-1 : ℂ)^j) * integerBinomial (-bilinear D α β - 1) j) •
    E J α (-weightPairing α b + (-bilinear D α β - 1) - j)
      (E J β (-weightPairing β b - 1 + j) v.val) = 0
  rw [he, map_zero, smul_zero]

include hNil H hHG hGH in
/-- Independent support audit of the second original mode-product family.
Here p+j is already above the leading alpha mode for every j, even j=0. -/
theorem charged_second_support (α β b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    Function.support (jacobiSecond J.stateField (groundState D α) (groundState D β)
      v.val (-weightPairing α b) (-weightPairing β b - 1)
      (-bilinear D α β - 1)) ⊆ (∅ : Set ℕ) := by
  intro j hj
  have he := E_above_leading J hNil H hHG hGH α b
    (-weightPairing α b + j) v hv (by omega)
  have hz : jacobiSecond J.stateField (groundState D α) (groundState D β)
      v.val (-weightPairing α b) (-weightPairing β b - 1)
      (-bilinear D α β - 1) j = 0 := by
    change (((-1 : ℂ)^j) * integerBinomial (-bilinear D α β - 1) j) •
      (StateFieldResidueReconstruction.epsilon (-bilinear D α β - 1) •
        E J β (-weightPairing β b - 1 + (-bilinear D α β - 1) - j)
          (E J α (-weightPairing α b + j) v.val)) = 0
    simp only [he, map_zero, smul_zero]
  exact (hj hz).elim

/-- Extract the three separately finite original sums. At index zero the
first outer mode is leading on b+G beta, by weightPairing_shift. -/
theorem S_comp_raw_M (α β b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    (S J hNil H hHG hGH α (shiftWeight b β)
      (S J hNil H hHG hGH β b v) : M) =
        epsilon D α β • (S J hNil H hHG hGH (α + β) b v : M) := by
  classical
  let p : ℤ := -weightPairing α b
  let q : ℤ := -weightPairing β b - 1
  let r : ℤ := -bilinear D α β - 1
  obtain ⟨hl, hf, hs, h⟩ := J.borcherds
    (groundState D α) (groundState D β) v.val p q r
  have hls := charged_left_support J α β b v
  have hfs := charged_first_support J hNil H hHG hGH α β b v hv
  have hss := charged_second_support J hNil H hHG hGH α β b v hv
  have hleft_zero (j : ℕ) (hj : j ≠ 0) :
      jacobiLeft J.stateField (groundState D α) (groundState D β) v.val p q r j = 0 := by
    by_contra hn
    exact hj (by simpa only [Set.mem_singleton_iff] using hls hn)
  have hfirst_zero (j : ℕ) (hj : j ≠ 0) :
      jacobiFirst J.stateField (groundState D α) (groundState D β) v.val p q r j = 0 := by
    by_contra hn
    exact hj (by simpa only [Set.mem_singleton_iff] using hfs hn)
  have hsecond_zero (j : ℕ) :
      jacobiSecond J.stateField (groundState D α) (groundState D β) v.val p q r j = 0 := by
    by_contra hn
    exact hss hn
  have hleft0 :
      jacobiLeft J.stateField (groundState D α) (groundState D β) v.val p q r 0 =
        epsilon D α β • (S J hNil H hHG hGH (α + β) b v : M) := by
    have hi : p + q = -weightPairing (α + β) b - 1 := by
      dsimp only [p, q]
      rw [weightPairing_add]
      omega
    change integerBinomial p 0 •
      mode J (sourceProduct D (groundState D α) (r + 0) (groundState D β))
        (p + q - 0) v.val = _
    rw [add_zero, sub_zero, hi]
    dsimp only [r]
    rw [source_ground_leading]
    simpa [integerBinomial, mode, E] using
      congrArg (fun z : M => epsilon D α β • z)
        (E_leading J hNil H hHG hGH (α + β) b v hv)
  have hfirst0 :
      jacobiFirst J.stateField (groundState D α) (groundState D β) v.val p q r 0 =
        (S J hNil H hHG hGH α (shiftWeight b β)
          (S J hNil H hHG hGH β b v) : M) := by
    have hi : p + r = -weightPairing α (shiftWeight b β) - 1 := by
      dsimp only [p, r]
      rw [weightPairing_shift]
      omega
    change (((-1 : ℂ)^0) * integerBinomial r 0) •
      E J α (p + r - 0) (E J β (q + 0) v.val) = _
    simp only [pow_zero, integerBinomial, Ring.choose_zero_right, Int.cast_one,
      one_mul, one_smul, sub_zero, add_zero]
    dsimp only [q]
    rw [E_leading J hNil H hHG hGH β b v hv, hi]
    exact E_leading J hNil H hHG hGH α (shiftWeight b β)
      (S J hNil H hHG hGH β b v) (S_mem_jointWeight J hNil H hHG hGH β b v hv)
  simp_rw [smul_sub] at h
  change (∑ᶠ j : ℕ, jacobiLeft J.stateField _ _ _ p q r j) =
    ∑ᶠ j : ℕ, (jacobiFirst J.stateField _ _ _ p q r j -
      jacobiSecond J.stateField _ _ _ p q r j) at h
  rw [finsum_sub_distrib hf hs, finsum_eq_single _ 0 hleft_zero,
    finsum_eq_single _ 0 hfirst_zero, hleft0, hfirst0] at h
  simpa only [hsecond_zero, finsum_zero, sub_zero] using h.symm

/-- Coercion-free Omega equality; no index casts are hidden in this law. -/
theorem S_comp (α β b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    S J hNil H hHG hGH α (shiftWeight b β) (S J hNil H hHG hGH β b v) =
      epsilon D α β • S J hNil H hHG hGH (α + β) b v := by
  apply Subtype.ext
  exact S_comp_raw_M J hNil H hHG hGH α β b v hv

/-- The charge-zero mode is the original vacuum mode on arbitrary Omega. -/
theorem S_zero (b : Charge D) :
    S J hNil H hHG hGH (0 : Charge D) b = 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change Pi J hNil H hHG (E J 0 (-weightPairing 0 b - 1) v.val) = v.val
  have he : E J (0 : Charge D) (-1) = LinearMap.id := by
    change mode J (LatticeAllStateField.vacuum D) (-1) = LinearMap.id
    exact (vacuum_modes J (-1)).trans (if_pos rfl)
  simp only [weightPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    neg_zero, zero_sub]
  rw [he, LinearMap.id_apply]
  exact Pi_fixes J hNil H hHG hGH v.val v.property

/-- The explicit index identity used by the inverse map. -/
theorem shiftWeight_cancel (b α : Charge D) :
    shiftWeight (shiftWeight b α) (-α) = b := by
  simp only [shiftWeight, Matrix.mulVec_neg, add_assoc, add_neg_cancel, add_zero]

/-- First unnormalized inverse equality on actual Omega. -/
theorem S_neg_comp (α b : Charge D) (v : Omega J)
    (hv : v ∈ jointWeight J b) :
    S J hNil H hHG hGH (-α) (shiftWeight b α) (S J hNil H hHG hGH α b v) =
      epsilon D (-α) α • v := by
  simpa only [neg_add_cancel, S_zero, Module.End.one_apply] using
    S_comp J hNil H hHG hGH (-α) α b v hv

/-- Reversed order, with shiftWeight_cancel made explicit in the mode label. -/
theorem S_comp_neg (α b : Charge D) (w : Omega J)
    (hw : w ∈ jointWeight J (shiftWeight b α)) :
    S J hNil H hHG hGH α b (S J hNil H hHG hGH (-α) (shiftWeight b α) w) =
      epsilon D (-α) α • w := by
  have h := S_comp J hNil H hHG hGH α (-α) (shiftWeight b α) w hw
  rw [shiftWeight_cancel, add_neg_cancel, S_zero, Module.End.one_apply,
    ← original_epsilon_opposite α] at h
  exact h

/-- The inverse scalar is the original epsilon(-alpha,alpha)^-1. -/
def Sinv (α b : Charge D) : Module.End ℂ (Omega J) :=
  (epsilon D (-α) α)⁻¹ • S J hNil H hHG hGH (-α) (shiftWeight b α)

/-- Raw Omega left inverse, with no subtype transport or hidden cast. -/
theorem Sinv_S (α b : Charge D) (v : Omega J) (hv : v ∈ jointWeight J b) :
    Sinv J hNil H hHG hGH α b (S J hNil H hHG hGH α b v) = v := by
  rw [Sinv, LinearMap.smul_apply, S_neg_comp J hNil H hHG hGH α b v hv,
    smul_smul, inv_mul_cancel₀ (original_epsilon_nonzero (-α) α), one_smul]

/-- Raw Omega right inverse, on the actual target weight. -/
theorem S_Sinv (α b : Charge D) (w : Omega J)
    (hw : w ∈ jointWeight J (shiftWeight b α)) :
    S J hNil H hHG hGH α b (Sinv J hNil H hHG hGH α b w) = w := by
  rw [Sinv, LinearMap.smul_apply, map_smul,
    S_comp_neg J hNil H hHG hGH α b w hw, smul_smul,
    inv_mul_cancel₀ (original_epsilon_nonzero (-α) α), one_smul]

/-- Genuine linear map between the actual joint eigenspaces. -/
def translation (α b : Charge D) :
    jointWeight J b →ₗ[ℂ] jointWeight J (shiftWeight b α) :=
  ((S J hNil H hHG hGH α b).comp (jointWeight J b).subtype).codRestrict
    (jointWeight J (shiftWeight b α))
    (fun v => S_mem_jointWeight J hNil H hHG hGH α b v.val v.property)

/-- The target of S_-alpha is initially indexed by (b+G alpha)+G(-alpha).
Transport it along shiftWeight_cancel before constructing the subtype. -/
def inverseTranslation (α b : Charge D) :
    jointWeight J (shiftWeight b α) →ₗ[ℂ] jointWeight J b :=
  ((Sinv J hNil H hHG hGH α b).comp
    (jointWeight J (shiftWeight b α)).subtype).codRestrict (jointWeight J b)
    (by
      intro w
      have hz := S_mem_jointWeight J hNil H hHG hGH (-α)
        (shiftWeight b α) w.val w.property
      rw [shiftWeight_cancel] at hz
      exact (jointWeight J b).smul_mem ((epsilon D (-α) α)⁻¹) hz)

/-- An honest typed linear equivalence, obtained from the proved raw laws.
It also exists when either space, M, or the lattice rank is zero. -/
def translationEquiv (α b : Charge D) :
    jointWeight J b ≃ₗ[ℂ] jointWeight J (shiftWeight b α) where
  toLinearMap := translation J hNil H hHG hGH α b
  invFun := inverseTranslation J hNil H hHG hGH α b
  left_inv v := by
    apply Subtype.ext
    exact Sinv_S J hNil H hHG hGH α b v.val v.property
  right_inv w := by
    apply Subtype.ext
    exact S_Sinv J hNil H hHG hGH α b w.val w.property

end D5.S3.VertexAlgebra.Modules.ActualGroundChargedTranslations
