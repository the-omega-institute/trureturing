/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterTensorField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldMatterTensorField
   mirror-E: none(waiver:algebraic-original-matter-field)
   anchors: []
   utility: none
   digest: Finite tensor state-field convolution and the native BRST stress modes. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldCriticalMatter

/-!
The actual Leech orbifold and hyperbolic lattice fields act on the original
algebraic BRST matter carrier by pointwise finite convolution. The tensor-field
construction follows Bakalov--Kac (arXiv:math/0402315, §4.1) and the
pointwise construction in `LatticeMatterGhostStateField`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldMatterTensorField

open OriginalOrbifoldCriticalMatter
open ActualLeechHyperbolic (leechData leech_spec)
open TwistedGround

private abbrev orbifoldField := orbifoldVertexAlgebra.stateField
private abbrev hyperbolicField := LatticeAllStateField.Y hyperbolicData
private abbrev orbifoldVacuum := orbifoldVertexAlgebra.vacuum
private abbrev hyperbolicVacuum := LatticeAllStateField.vacuum hyperbolicData

private def cutoff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : VertexOperator ℂ V) (v : V) : ℤ :=
  -((HahnModule.of ℂ).symm (A v)).order

private theorem mode_eq_zero_of_cutoff_le {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : VertexOperator ℂ V) (v : V) (n : ℤ) (hn : cutoff A v ≤ n) :
    (A[[n]]) v = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  dsimp [cutoff] at hn
  omega

/-- At fixed indices the summand is linear in both the tensor state and its input. -/
def modeSummand (n k : ℤ) : Matter →ₗ[ℂ] Module.End ℂ Matter :=
  TensorProduct.map₂
    ((LinearMap.proj k).comp (VertexOperator.ncoeff.comp orbifoldField))
    ((LinearMap.proj (n - 1 - k)).comp (VertexOperator.ncoeff.comp hyperbolicField))

private theorem modeSummand_tmul (a x : Orbifold) (b y : Hyperbolic) (n k : ℤ) :
    modeSummand n k (a ⊗ₜ[ℂ] b) (x ⊗ₜ[ℂ] y) =
      ((orbifoldField a)[[k]]) x ⊗ₜ[ℂ] ((hyperbolicField b)[[n - 1 - k]]) y := rfl

/-- The convolution on a pure pair is confined to the intersection of the two mode tails. -/
theorem support_tmul (a x : Orbifold) (b y : Hyperbolic) (n A B : ℤ)
    (ha : ∀ k : ℤ, A ≤ k → ((orbifoldVertexAlgebra.stateField a)[[k]]) x = 0)
    (hb : ∀ j : ℤ, B ≤ j → ((LatticeAllStateField.Y hyperbolicData b)[[j]]) y = 0) :
    Function.support (fun k =>
      ((orbifoldVertexAlgebra.stateField a)[[k]]) x ⊗ₜ[ℂ]
        ((LatticeAllStateField.Y hyperbolicData b)[[n - 1 - k]]) y) ⊆
      Set.Icc (n - B) (A - 1) := by
  intro k hk
  by_contra h
  have hout : k < n - B ∨ A - 1 < k := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using h
  apply hk
  dsimp only
  rcases hout with hl | hr
  · rw [hb _ (by omega), TensorProduct.tmul_zero]
  · rw [ha _ (by omega), TensorProduct.zero_tmul]

private theorem support_tmul_cutoff (a x : Orbifold) (b y : Hyperbolic) (n : ℤ) :
    Function.support (fun k => modeSummand n k (a ⊗ₜ[ℂ] b) (x ⊗ₜ[ℂ] y)) ⊆
      Set.Icc (n - cutoff (hyperbolicField b) y) (cutoff (orbifoldField a) x - 1) := by
  simpa only [modeSummand_tmul] using
    support_tmul a x b y n _ _ (mode_eq_zero_of_cutoff_le _ _) (mode_eq_zero_of_cutoff_le _ _)

/-- Each mode is a finite sum on every pair of algebraic tensors. -/
theorem modeSummand_finite (s x : Matter) (n : ℤ) :
    Function.HasFiniteSupport (fun k : ℤ => modeSummand n k s x) := by
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | tmul x y => exact (Set.finite_Icc _ _).subset (support_tmul_cutoff a x b y n)
    | add x y hx hy => simpa only [map_add, Pi.add_def] using hx.add hy
  | add s t hs ht => simpa only [map_add, LinearMap.add_apply, Pi.add_def] using hs.add ht

private theorem modeSummand_truncation (s x : Matter) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ∀ k : ℤ, modeSummand n k s x = 0 := by
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      refine ⟨cutoff (orbifoldField a) x + cutoff (hyperbolicField b) y, ?_⟩
      intro n hn k
      by_contra hk
      have h := support_tmul_cutoff a x b y n hk
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

private def coefficient (n : ℤ) : Matter →ₗ[ℂ] Module.End ℂ Matter where
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

private def field (s : Matter) : VertexOperator ℂ Matter :=
  VertexOperator.of_coeff (fun power => coefficient (-power - 1) s) (by
    intro x
    obtain ⟨N, hN⟩ := modeSummand_truncation s x
    refine ⟨-N, ?_⟩
    intro power hp
    by_contra hn
    exact hp (finsum_eq_zero_of_forall_eq_zero (hN (-power - 1) (by omega))))

private theorem field_ncoeff (s : Matter) (n : ℤ) :
    (field s)[[n]] = coefficient n s := by
  rw [field, VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

/-- The literal linear tensor state-field map on the native BRST matter carrier. -/
def stateField : Matter →ₗ[ℂ] VertexOperator ℂ Matter where
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

theorem stateField_ncoeff_apply (s x : Matter) (n : ℤ) :
    ((stateField s)[[n]]) x = ∑ᶠ k : ℤ, modeSummand n k s x := by
  change ((field s)[[n]]) x = _
  rw [field_ncoeff]
  rfl

/-- Normalized modes convolve with index `n - 1 - k` on the hyperbolic factor. -/
theorem stateField_tmul (a x : Orbifold) (b y : Hyperbolic) (n : ℤ) :
    ((stateField (a ⊗ₜ[ℂ] b))[[n]]) (x ⊗ₜ[ℂ] y) =
      ∑ᶠ k : ℤ, ((orbifoldVertexAlgebra.stateField a)[[k]]) x ⊗ₜ[ℂ]
        ((LatticeAllStateField.Y hyperbolicData b)[[n - 1 - k]]) y := by
  rw [stateField_ncoeff_apply]
  exact finsum_congr (fun k => modeSummand_tmul a x b y n k)

/-- Large normalized modes vanish pointwise on the entire matter carrier. -/
theorem stateField_truncation (s x : Matter) :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ((stateField s)[[n]]) x = 0 := by
  obtain ⟨N, hN⟩ := modeSummand_truncation s x
  exact ⟨N, fun n hn => by
    rw [stateField_ncoeff_apply]
    exact finsum_eq_zero_of_forall_eq_zero (hN n hn)⟩

private theorem identity_ncoeff {V : Type*} [AddCommGroup V] [Module ℂ V] (n : ℤ) :
    ((FieldNormalProduct.identityField : VertexOperator ℂ V)[[n]]) =
      if n = -1 then LinearMap.id else 0 := by
  rw [FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]
  simp only [show -n - 1 = 0 ↔ n = -1 by omega]

private theorem right_vacuum_ncoeff (a : Orbifold) (n : ℤ) :
    ((stateField (a ⊗ₜ[ℂ] hyperbolicVacuum))[[n]]) =
      ((orbifoldField a)[[n]]).rTensor Hyperbolic := by
  apply TensorProduct.ext'
  intro x y
  rw [stateField_tmul, LatticeAllStateField.stateField_vacuum, finsum_eq_single _ n]
  · rw [identity_ncoeff, ite_eq_left (show n - 1 - n = -1 by omega)]
    rfl
  · intro k hk
    simp [identity_ncoeff, show n - 1 - k ≠ -1 by omega]

private theorem left_vacuum_ncoeff (b : Hyperbolic) (n : ℤ) :
    ((stateField (orbifoldVacuum ⊗ₜ[ℂ] b))[[n]]) =
      ((hyperbolicField b)[[n]]).lTensor Orbifold := by
  apply TensorProduct.ext'
  intro x y
  rw [stateField_tmul, orbifoldVertexAlgebra.vacuum_field, finsum_eq_single _ (-1)]
  · rw [identity_ncoeff, ite_eq_left rfl, show n - 1 - -1 = n by omega]
    rfl
  · intro k hk
    simp [identity_ncoeff, hk]

/-- The field of the actual matter vacuum is the identity field. -/
theorem stateField_vacuum : stateField matterVacuum = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext power
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff, matterVacuum,
    right_vacuum_ncoeff, orbifoldVertexAlgebra.vacuum_field, identity_ncoeff, identity_ncoeff]
  split_ifs <;> simp [LinearMap.rTensor_id]

/-- Sum of the actual conformal states inserted with the opposite vacuum. -/
def stressState : Matter :=
  OriginalOrbifoldConformal.conformalVector leechData leech_spec.2.1 ⊗ₜ[ℂ] hyperbolicVacuum +
    orbifoldVacuum ⊗ₜ[ℂ] LatticeActualConformalState.omega hyperbolicData hyperbolicInverse

/-- The coefficient at power `-n - 2` of the stress field is the native BRST mode. -/
theorem stressState_modes (n : ℤ) :
    ((stateField stressState)[[n + 1]]) = OriginalOrbifoldCriticalMatter.mode n := by
  simp only [stressState, map_add, Pi.add_apply, right_vacuum_ncoeff, left_vacuum_ncoeff,
    LatticeActualConformalState.omega_modes, mode, hyperbolicMode]
  rw [orbifoldMode_eq_stateField]

private theorem ncoeff_matterVacuum_tmul (a : Orbifold) (b : Hyperbolic) (n : ℤ) :
    ((stateField (a ⊗ₜ[ℂ] b))[[n]]) matterVacuum =
      ∑ k ∈ Finset.Icc n (-1), ((orbifoldField a)[[k]]) orbifoldVacuum ⊗ₜ[ℂ]
        ((hyperbolicField b)[[n - 1 - k]]) hyperbolicVacuum := by
  rw [stateField_ncoeff_apply]
  calc
    _ = ∑ k ∈ Finset.Icc n (-1), modeSummand n k (a ⊗ₜ[ℂ] b) matterVacuum := by
      apply finsum_eq_sum_of_support_subset
      simpa only [matterVacuum, modeSummand_tmul, sub_zero, zero_sub, Finset.coe_Icc] using
        support_tmul a orbifoldVacuum b hyperbolicVacuum n 0 0
          (orbifoldVertexAlgebra.creativity a)
          (LatticeAllStateField.stateField_creativity hyperbolicData b)
    _ = _ := by simp only [matterVacuum, modeSummand_tmul]

/-- The constant coefficient of a field on the vacuum recovers the state. -/
theorem stateField_creation (s : Matter) : ((stateField s)[[-1]]) matterVacuum = s := by
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    rw [ncoeff_matterVacuum_tmul, Finset.Icc_self, Finset.sum_singleton,
      show (-1 : ℤ) - 1 - -1 = -1 by omega]
    rw [orbifoldVertexAlgebra.creation, LatticeAllStateField.stateField_creation]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

/-- A field acting on the vacuum has no negative powers. -/
theorem stateField_creativity (s : Matter) (n : ℤ) (hn : 0 ≤ n) :
    ((stateField s)[[n]]) matterVacuum = 0 := by
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    rw [ncoeff_matterVacuum_tmul, Finset.Icc_eq_empty_of_lt (by omega), Finset.sum_empty]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht, add_zero]

private theorem orbifold_creation_translation (a : Orbifold) :
    ((orbifoldField a)[[-2]]) orbifoldVacuum = orbifoldVertexAlgebra.translation a := by
  have h := LinearMap.congr_fun (orbifoldVertexAlgebra.covariance a (-1)) orbifoldVacuum
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    orbifoldVertexAlgebra.creation, orbifoldVertexAlgebra.translation_vacuum,
    map_zero, sub_zero, Int.cast_neg, Int.cast_one, neg_neg, one_smul,
    show (-1 : ℤ) - 1 = -2 by omega] using h.symm

/-- The linear coefficient on the vacuum recovers the actual BRST matter translation. -/
theorem stateField_creation_translation (s : Matter) :
    ((stateField s)[[-2]]) matterVacuum = OriginalOrbifoldCriticalMatter.mode (-1) s := by
  rw [mode_minus_one_eq_translation]
  induction s using TensorProduct.inductionOn with
  | tmul a b =>
    have hI : Finset.Icc (-2 : ℤ) (-1) = {-2, -1} := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [ncoeff_matterVacuum_tmul, hI, Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [show (-2 : ℤ) - 1 - -2 = -1 by omega,
      show (-2 : ℤ) - 1 - -1 = -2 by omega, orbifoldVertexAlgebra.creation,
      LatticeAllStateField.stateField_creation, orbifold_creation_translation,
      ← LatticeActualVertexAlgebra.translation_as_mode, LinearMap.add_apply,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

#print axioms modeSummand
#print axioms stateField
#print axioms support_tmul
#print axioms modeSummand_finite
#print axioms stateField_ncoeff_apply
#print axioms stateField_tmul
#print axioms stateField_truncation
#print axioms stateField_vacuum
#print axioms stressState
#print axioms stressState_modes
#print axioms stateField_creation
#print axioms stateField_creativity
#print axioms stateField_creation_translation

end D5.S3.VertexAlgebra.OriginalOrbifoldMatterTensorField
