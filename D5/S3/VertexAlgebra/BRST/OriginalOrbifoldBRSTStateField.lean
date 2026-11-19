/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTStateField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTStateField
   mirror-E: none(waiver:algebraic-original-matter-ghost-field)
   anchors: []
   utility: none
   digest: Tensor fields realize the native BRST charge and total stress modes. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterTensorField
import D5.S3.Quantum.Fermionic.BcGhostConformalBRSTState

/-!
The tensor construction follows Bakalov–Kac (arXiv:math/0402315, §4.1) and the
pointwise finite convolution in `OriginalOrbifoldMatterTensorField`. The BRST
reindexing follows `LatticeMatterGhostStateField.current_zero_mode`. The
ghost field and current use the Scott Carnahan Apache-2.0 normal-product
calculus attributed in their suppliers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTStateField

open OriginalOrbifoldCriticalMatter
open OriginalOrbifoldMatterTensorField (stateField stressState)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)

local notation "ghostVacuum" => CountableOccupationFock.vacuum

private def cutoff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : VertexOperator ℂ V) (v : V) : ℤ :=
  -((HahnModule.of ℂ).symm (A v)).order

private theorem mode_eq_zero_of_cutoff_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : VertexOperator ℂ V) (v : V) (n : ℤ) (hn : cutoff A v ≤ n) :
    (A[[n]]) v = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  dsimp [cutoff] at hn
  omega

/-- At fixed indices the tensor coefficient summand is linear in the state and the input. -/
def modeSummand (n k : ℤ) : State →ₗ[ℂ] Module.End ℂ State :=
  TensorProduct.map₂
    ((LinearMap.proj k).comp (VertexOperator.ncoeff.comp stateField))
    ((LinearMap.proj (n - 1 - k)).comp (VertexOperator.ncoeff.comp BcGhostStateField.Y))

private theorem modeSummand_tmul (u v : Matter) (a b : Fock) (n k : ℤ) :
    modeSummand n k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) =
      ((stateField u)[[k]]) v ⊗ₜ[ℂ] ((BcGhostStateField.Y a)[[n - 1 - k]]) b := rfl

/-- The two pointwise mode tails confine the literal pure tensor summand to a finite interval. -/
theorem support_tmul (u v : Matter) (a b : Fock) (n M G : ℤ)
    (hm : ∀ k : ℤ, M ≤ k → ((stateField u)[[k]]) v = 0)
    (hg : ∀ j : ℤ, G ≤ j → ((BcGhostStateField.Y a)[[j]]) b = 0) :
    Function.support (fun k =>
      ((stateField u)[[k]]) v ⊗ₜ[ℂ] ((BcGhostStateField.Y a)[[n - 1 - k]]) b) ⊆
      Set.Icc (n - G) (M - 1) := by
  intro k hk
  by_contra h
  have hout : k < n - G ∨ M - 1 < k := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using h
  apply hk
  dsimp only
  rcases hout with hl | hr
  · rw [hg _ (by omega), TensorProduct.tmul_zero]
  · rw [hm _ (by omega), TensorProduct.zero_tmul]

private theorem support_tmul_cutoff (u v : Matter) (a b : Fock) (n : ℤ) :
    Function.support (fun k => modeSummand n k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)) ⊆
      Set.Icc (n - cutoff (BcGhostStateField.Y a) b) (cutoff (stateField u) v - 1) := by
  simpa only [modeSummand_tmul] using
    support_tmul u v a b n _ _ (mode_eq_zero_of_cutoff_le _ _) (mode_eq_zero_of_cutoff_le _ _)

/-- Each coefficient is a finite sum on arbitrary algebraic state and input tensors. -/
theorem modeSummand_finite (s x : State) (n : ℤ) :
    Function.HasFiniteSupport (fun k : ℤ => modeSummand n k s x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b => exact (Set.finite_Icc _ _).subset (support_tmul_cutoff u v a b n)
    | add x y hx hy => simpa only [map_add, Pi.add_def] using hx.add hy
  | add s t hs ht => simpa only [map_add, LinearMap.add_apply, Pi.add_def] using hs.add ht

private theorem modeSummand_truncation (s x : State) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ k : ℤ, modeSummand n k s x = 0 := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      refine ⟨cutoff (stateField u) v + cutoff (BcGhostStateField.Y a) b, ?_⟩
      intro n hn k
      by_contra hk
      have h := support_tmul_cutoff u v a b n hk
      rw [Set.mem_Icc] at h
      omega
    | add x y hx hy =>
      obtain ⟨N, hN⟩ := hx
      obtain ⟨P, hP⟩ := hy
      exact ⟨max N P, fun n hn k => by
        rw [map_add, hN n (by omega) k, hP n (by omega) k, add_zero]⟩
  | add s t hs ht =>
    obtain ⟨N, hN⟩ := hs
    obtain ⟨P, hP⟩ := ht
    exact ⟨max N P, fun n hn k => by
      rw [map_add, LinearMap.add_apply, hN n (by omega) k, hP n (by omega) k, add_zero]⟩

private def coefficient (n : ℤ) : State →ₗ[ℂ] Module.End ℂ State where
  toFun s := {
    toFun x := ∑ᶠ k : ℤ, modeSummand n k s x
    map_add' x y := by
      simp only [map_add]
      exact finsum_add_distrib (modeSummand_finite s x n) (modeSummand_finite s y n)
    map_smul' z x := by
      simp only [map_smul, RingHom.id_apply]
      exact (smul_finsum' z (modeSummand_finite s x n)).symm }
  map_add' s t := by
    apply LinearMap.ext
    intro x
    change (∑ᶠ k : ℤ, modeSummand n k (s + t) x) =
      (∑ᶠ k : ℤ, modeSummand n k s x) + (∑ᶠ k : ℤ, modeSummand n k t x)
    simp only [map_add, LinearMap.add_apply]
    exact finsum_add_distrib (modeSummand_finite s x n) (modeSummand_finite t x n)
  map_smul' z s := by
    apply LinearMap.ext
    intro x
    change (∑ᶠ k : ℤ, modeSummand n k (z • s) x) = z • ∑ᶠ k : ℤ, modeSummand n k s x
    simp only [map_smul, LinearMap.smul_apply]
    exact (smul_finsum' z (modeSummand_finite s x n)).symm

private def field (s : State) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fun power => coefficient (-power - 1) s) (by
    intro x
    obtain ⟨N, hN⟩ := modeSummand_truncation s x
    refine ⟨-N, ?_⟩
    intro power hp
    by_contra hn
    exact hp (finsum_eq_zero_of_forall_eq_zero (hN (-power - 1) (by omega))))

private theorem field_ncoeff (s : State) (n : ℤ) :
    (field s)[[n]] = coefficient n s := by
  rw [field, VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

/-- The linear state-field map on the original matter–bc carrier. -/
def Y : State →ₗ[ℂ] VertexOperator ℂ State where
  toFun := field
  map_add' s t := by
    apply HVertexOperator.coeff_inj
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_ncoeff, map_add, Pi.add_apply]
  map_smul' z s := by
    apply HVertexOperator.coeff_inj
    funext power
    simp only [VertexOperator.coeff_eq_ncoeff, field_ncoeff, map_smul, Pi.smul_apply,
      RingHom.id_apply]

theorem Y_ncoeff_apply (s x : State) (n : ℤ) :
    ((Y s)[[n]]) x = ∑ᶠ k : ℤ, modeSummand n k s x := by
  change ((field s)[[n]]) x = _
  rw [field_ncoeff]
  rfl

/-- The matter mode `k` pairs with the ghost mode `n - 1 - k`. -/
theorem Y_tmul (u v : Matter) (a b : Fock) (n : ℤ) :
    ((Y (u ⊗ₜ[ℂ] a))[[n]]) (v ⊗ₜ[ℂ] b) =
      ∑ᶠ k : ℤ, ((stateField u)[[k]]) v ⊗ₜ[ℂ] ((BcGhostStateField.Y a)[[n - 1 - k]]) b := by
  rw [Y_ncoeff_apply]
  exact finsum_congr (fun k => modeSummand_tmul u v a b n k)

/-- Large normalized modes vanish pointwise on the entire algebraic carrier. -/
theorem Y_truncation (s x : State) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ((Y s)[[n]]) x = 0 := by
  obtain ⟨N, hN⟩ := modeSummand_truncation s x
  exact ⟨N, fun n hn => by
    rw [Y_ncoeff_apply]
    exact finsum_eq_zero_of_forall_eq_zero (hN n hn)⟩

private theorem identity_ncoeff {V : Type*} [AddCommGroup V] [Module ℂ V] (n : ℤ) :
    ((FieldNormalProduct.identityField : VertexOperator ℂ V)[[n]]) =
      if n = -1 then LinearMap.id else 0 := by
  rw [FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]
  simp only [show -n - 1 = 0 ↔ n = -1 by omega]

/-- Inserting the ghost vacuum lifts the matter field through the ghost identity. -/
theorem right_vacuum_ncoeff (u : Matter) (n : ℤ) :
    ((Y (u ⊗ₜ[ℂ] ghostVacuum))[[n]]) =
      TensorProduct.map ((stateField u)[[n]]) LinearMap.id := by
  apply TensorProduct.ext'
  intro v b
  rw [Y_tmul, BcGhostStateField.stateField_creation.1, finsum_eq_single _ n]
  · rw [identity_ncoeff, ite_eq_left (show n - 1 - n = -1 by omega)]
    rfl
  · intro k hk
    simp [identity_ncoeff, show n - 1 - k ≠ -1 by omega]

/-- Inserting the matter vacuum lifts the ghost field through the matter identity. -/
theorem left_vacuum_ncoeff (a : Fock) (n : ℤ) :
    ((Y (matterVacuum ⊗ₜ[ℂ] a))[[n]]) =
      TensorProduct.map LinearMap.id ((BcGhostStateField.Y a)[[n]]) := by
  apply TensorProduct.ext'
  intro v b
  rw [Y_tmul, OriginalOrbifoldMatterTensorField.stateField_vacuum, finsum_eq_single _ (-1)]
  · rw [identity_ncoeff, ite_eq_left rfl, show n - 1 - -1 = n by omega]
    rfl
  · intro k hk
    simp [identity_ncoeff, hk]

/-- The native total vacuum gives the identity field. -/
theorem Y_vacuum : Y vacuum = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, vacuum,
    right_vacuum_ncoeff, OriginalOrbifoldMatterTensorField.stateField_vacuum,
    identity_ncoeff, identity_ncoeff]
  split_ifs <;> simp [TensorProduct.map_id]

/-- The lifted `b` field has the native integer modes. -/
theorem b_modes (n : ℤ) :
    ((Y (matterVacuum ⊗ₜ[ℂ] ket {0}))[[n]]) = b (n - 1) := by
  rw [left_vacuum_ncoeff, BcGhostStateField.stateField_creation.2.2.2.1]
  rfl

/-- The lifted `c` field has the native integer modes. -/
theorem c_modes (n : ℤ) :
    ((Y (matterVacuum ⊗ₜ[ℂ] ket {1}))[[n]]) = VirasoroBRST.ghostC matterDatum (n + 2) := by
  rw [left_vacuum_ncoeff, BcGhostStateField.stateField_creation.2.2.2.2]
  rfl

/-- The sum of the two conformal states inserted with the opposite vacuum. -/
def OmegaTotal : State :=
  stressState ⊗ₜ[ℂ] ghostVacuum + matterVacuum ⊗ₜ[ℂ] BcGhostConformalBRSTState.Omega

/-- The total stress coefficients are exactly the native total Virasoro operators. -/
theorem conformal_modes (n : ℤ) :
    ((Y OmegaTotal)[[n + 1]]) = VirasoroBRST.Ltotal matterDatum n := by
  simp only [OmegaTotal, map_add, Pi.add_apply, right_vacuum_ncoeff, left_vacuum_ncoeff,
    OriginalOrbifoldMatterTensorField.stressState_modes, BcGhostConformalBRSTState.conformal_modes]
  rfl

/-- The literal BRST current state from the matter stress, ghost `c`, and cubic ghost current. -/
def J : State :=
  stressState ⊗ₜ[ℂ] ket {1} + matterVacuum ⊗ₜ[ℂ] BcGhostConformalBRSTState.Jg

private theorem matter_current_zero_mode :
    ((Y (stressState ⊗ₜ[ℂ] ket {1}))[[0]]) = VirasoroBRST.T matterDatum := by
  apply TensorProduct.ext'
  intro v b
  rw [Y_tmul]
  let e : ℤ ≃ ℤ := Equiv.addRight 1
  calc
    _ = ∑ᶠ m : ℤ, ((stateField stressState)[[e m]]) v ⊗ₜ[ℂ]
        ((BcGhostStateField.Y (ket {1}))[[0 - 1 - e m]]) b :=
      (finsum_comp_equiv e).symm
    _ = ∑ᶠ m : ℤ, VirasoroBRST.summand matterDatum m (v ⊗ₜ[ℂ] b) := by
      apply finsum_congr
      intro m
      dsimp [e]
      rw [OriginalOrbifoldMatterTensorField.stressState_modes,
        BcGhostStateField.stateField_creation.2.2.2.2,
        show (-1 : ℤ) - (m + 1) + 2 = -m by omega]
      rfl
    _ = _ := rfl

/-- The zero coefficient of the actual total current is the native BRST endomorphism. -/
theorem current_zero_mode : ((Y J)[[0]]) = Q := by
  simp only [J, map_add, Pi.add_apply, matter_current_zero_mode, left_vacuum_ncoeff,
    BcGhostConformalBRSTState.current_zero_mode]
  rfl

#print axioms modeSummand
#print axioms support_tmul
#print axioms modeSummand_finite
#print axioms Y
#print axioms Y_ncoeff_apply
#print axioms Y_tmul
#print axioms Y_truncation
#print axioms right_vacuum_ncoeff
#print axioms left_vacuum_ncoeff
#print axioms Y_vacuum
#print axioms b_modes
#print axioms c_modes
#print axioms OmegaTotal
#print axioms conformal_modes
#print axioms J
#print axioms matter_current_zero_mode
#print axioms current_zero_mode

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTStateField
