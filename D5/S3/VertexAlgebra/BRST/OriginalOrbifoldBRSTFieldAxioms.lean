/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTFieldAxioms
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTFieldAxioms
   mirror-E: none(waiver:algebraic-original-brst-field-axioms)
   anchors: []
   utility: none
   digest: Vacuum creation, translation covariance, and parity for the native BRST field. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTSignedLocality

/-!
The vacuum and parity computations use the original matter–ghost tensor
coefficients. The translation proof follows the finite index shift in
`OriginalOrbifoldMatterTensorProducts.stateField_covariance`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTFieldAxioms

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open OriginalOrbifoldCriticalMatter (Matter State matterDatum matterVacuum vacuum)
open OriginalOrbifoldMatterTensorField (stateField)
open OriginalOrbifoldBRSTStateField (Y Y_tmul Y_ncoeff_apply modeSummand modeSummand_finite)
open OriginalOrbifoldBRSTSignedLocality (parity)
open private modeSummand_tmul from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTStateField

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

local notation "ghostVacuum" => CountableOccupationFock.vacuum

/-- The sum of the matter and ghost translations acting on the original tensor carrier. -/
def translation : Module.End ℂ State :=
  TensorProduct.map OriginalOrbifoldMatterVertexAlgebra.actualVertexAlgebra.translation
    LinearMap.id + TensorProduct.map LinearMap.id (BcGhostVirasoro.L (-1))

/-- The tensor translation is the native total Virasoro mode at minus one. -/
theorem translation_eq_total_mode : translation = VirasoroBRST.Ltotal matterDatum (-1) := rfl

/-- Virasoro index minus one is normalized state-field index zero. -/
theorem translation_eq_conformal_ncoeff :
    translation = ((Y OriginalOrbifoldBRSTStateField.OmegaTotal)[[0]]) := by
  rw [translation_eq_total_mode]
  exact (OriginalOrbifoldBRSTStateField.conformal_modes (-1)).symm

private theorem translation_tmul (v : Matter) (b : Fock) :
    translation (v ⊗ₜ[ℂ] b) = OriginalOrbifoldCriticalMatter.mode (-1) v ⊗ₜ[ℂ] b +
      v ⊗ₜ[ℂ] BcGhostVirasoro.L (-1) b := by
  rw [translation_eq_total_mode]
  rfl

/-- The native total translation annihilates the tensor vacuum. -/
theorem translation_vacuum : translation vacuum = 0 := by
  rw [vacuum, translation_tmul, OriginalOrbifoldMatterTensorProducts.translation_vacuum,
    BcGhostStateField.stateField_translation.1, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, add_zero]

private theorem vacuum_summand_eq_zero (u : Matter) (a : Fock) (n k : ℤ)
    (h : 0 ≤ k ∨ 0 ≤ n - 1 - k) :
    ((stateField u)[[k]]) matterVacuum ⊗ₜ[ℂ]
      ((BcGhostStateField.Y a)[[n - 1 - k]]) ghostVacuum = 0 := by
  rcases h with hm | hg
  · rw [OriginalOrbifoldMatterTensorField.stateField_creativity u k hm, TensorProduct.zero_tmul]
  · rw [BcGhostStateField.stateField_creation.2.2.1 a (n - 1 - k) hg, TensorProduct.tmul_zero]

/-- The minus-one mode creates every state from the native tensor vacuum. -/
theorem stateField_creation (s : State) : ((Y s)[[-1]]) vacuum = s := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    rw [vacuum, Y_tmul, finsum_eq_single _ (-1)]
    · rw [show (-1 : ℤ) - 1 - -1 = -1 by omega,
        OriginalOrbifoldMatterTensorField.stateField_creation,
        BcGhostStateField.stateField_creation.2.1]
    · intro k hk
      exact vacuum_summand_eq_zero u a (-1) k (by omega)
  | add s t hs ht => simp [map_add, hs, ht]

/-- Every nonnegative mode of every state annihilates the native tensor vacuum. -/
theorem stateField_creativity (s : State) (n : ℤ) (hn : 0 ≤ n) :
    ((Y s)[[n]]) vacuum = 0 := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    rw [vacuum, Y_tmul]
    exact finsum_eq_zero_of_forall_eq_zero (fun k => vacuum_summand_eq_zero u a n k (by omega))
  | add s t hs ht => simp [map_add, hs, ht]

private theorem summand_covariance (s : State) (n k : ℤ) :
    translation * modeSummand n k s - modeSummand n k s * translation =
      -(k : ℂ) • modeSummand (n - 1) (k - 1) s +
        -((n - 1 - k : ℤ) : ℂ) • modeSummand (n - 1) k s := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    apply TensorProduct.ext'
    intro v b
    have hm := LinearMap.congr_fun
      (OriginalOrbifoldMatterTensorProducts.stateField_covariance u k) v
    have hg := LinearMap.congr_fun (BcGhostStateField.stateField_translation.2 a (n - 1 - k)) b
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply] at hm hg
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, modeSummand_tmul, translation_tmul, map_add]
    rw [sub_eq_iff_eq_add.mp hm, sub_eq_iff_eq_add.mp hg,
      show n - 1 - 1 - (k - 1) = n - 1 - k by omega,
      show n - 1 - k - 1 = n - 1 - 1 - k by omega]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    abel
  | add s t hs ht =>
    simp only [map_add, mul_add, add_mul] at *
    rw [show ∀ A B C D : Module.End ℂ State,
      (A + B) - (C + D) = (A - C) + (B - D) by intros; abel, hs, ht]
    simp only [smul_add]
    abel

/-- The native translation commutator differentiates the field at every integer mode. -/
theorem stateField_covariance (s : State) (n : ℤ) :
    translation * ((Y s)[[n]]) - ((Y s)[[n]]) * translation =
      -(n : ℂ) • ((Y s)[[n - 1]]) := by
  apply LinearMap.ext
  intro x
  let f : ℤ → State := fun k => modeSummand (n - 1) k s x
  have hf : Function.HasFiniteSupport f := modeSummand_finite s x (n - 1)
  let shift : ℤ ≃ ℤ := Equiv.subRight 1
  have hLeft : Function.HasFiniteSupport (fun k : ℤ => -(k : ℂ) • f (k - 1)) :=
    (hf.comp_of_injective shift.injective).smul_right (fun k : ℤ => -(k : ℂ))
  have hRight : Function.HasFiniteSupport (fun k : ℤ => -((n - 1 - k : ℤ) : ℂ) • f k) :=
    hf.smul_right (fun k : ℤ => -((n - 1 - k : ℤ) : ℂ))
  have hShift : (∑ᶠ k : ℤ, -(k : ℂ) • f (k - 1)) =
      ∑ᶠ k : ℤ, -((k + 1 : ℤ) : ℂ) • f k := by
    let g : ℤ → State := fun k => -((k + 1 : ℤ) : ℂ) • f k
    calc
      _ = ∑ᶠ k : ℤ, g (shift k) := by
        apply finsum_congr
        intro k
        change -(k : ℂ) • f (k - 1) = -((k - 1 + 1 : ℤ) : ℂ) • f (k - 1)
        rw [sub_add_cancel]
      _ = _ := finsum_comp_equiv shift
  change translation (((Y s)[[n]]) x) - ((Y s)[[n]]) (translation x) =
    -(n : ℂ) • ((Y s)[[n - 1]]) x
  rw [Y_ncoeff_apply s x n, Y_ncoeff_apply s (translation x) n,
    map_finsum translation (modeSummand_finite s x n),
    ← finsum_sub_distrib ((modeSummand_finite s x n).fun_comp (map_zero translation))
      (modeSummand_finite s (translation x) n)]
  calc
    _ = ∑ᶠ k : ℤ, (-(k : ℂ) • f (k - 1) + -((n - 1 - k : ℤ) : ℂ) • f k) := by
      apply finsum_congr
      intro k
      exact LinearMap.congr_fun (summand_covariance s n k) x
    _ = _ := by
      rw [finsum_add_distrib hLeft hRight, hShift,
        ← finsum_add_distrib
          (f := fun k : ℤ => -((k + 1 : ℤ) : ℂ) • f k)
          (g := fun k : ℤ => -((n - 1 - k : ℤ) : ℂ) • f k)
          (hf.smul_right (fun k : ℤ => -((k + 1 : ℤ) : ℂ))) hRight]
      simp_rw [← add_smul, show ∀ k : ℤ,
        -((k + 1 : ℤ) : ℂ) + -((n - 1 - k : ℤ) : ℂ) = -(n : ℂ) by
          intro k
          push_cast
          ring]
      rw [← smul_finsum' _ hf, Y_ncoeff_apply]

/-- The ghost parity lifted to the full carrier squares to the identity. -/
theorem parity_involution : parity * parity = (1 : Module.End ℂ State) := by
  apply TensorProduct.ext'
  intro v b
  have hb := LinearMap.congr_fun CountableOccupationFock.parity_involution b
  change CountableOccupationFock.parity (CountableOccupationFock.parity b) = b at hb
  simpa only [parity, Module.End.mul_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    Module.End.one_apply] using congrArg (fun w => v ⊗ₜ[ℂ] w) hb

private theorem summand_parity (s : State) (n k : ℤ) :
    parity * modeSummand n k s = modeSummand n k (parity s) * parity := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    apply TensorProduct.ext'
    intro v b
    have h := LinearMap.congr_fun (BcGhostStateField.stateField_parity a (n - 1 - k)) b
    simpa only [parity, modeSummand_tmul, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply] using
      congrArg (fun w => ((stateField u)[[k]]) v ⊗ₜ[ℂ] w) h
  | add s t hs ht => simp only [map_add, mul_add, add_mul, hs, ht]

/-- Parity intertwines the actual modes for arbitrary field states. -/
theorem stateField_parity (s : State) (n : ℤ) :
    parity * ((Y s)[[n]]) = ((Y (parity s))[[n]]) * parity := by
  apply LinearMap.ext
  intro x
  change parity (((Y s)[[n]]) x) = ((Y (parity s))[[n]]) (parity x)
  rw [Y_ncoeff_apply, Y_ncoeff_apply, map_finsum parity (modeSummand_finite s x n)]
  exact finsum_congr (fun k => LinearMap.congr_fun (summand_parity s n k) x)

/-- Every integer mode product of homogeneous states has their summed parity. -/
theorem homogeneous_mode_product (s t : State) (p q : ℕ) (n : ℤ)
    (hs : parity s = (-1 : ℂ) ^ p • s) (ht : parity t = (-1 : ℂ) ^ q • t) :
    parity (((Y s)[[n]]) t) = (-1 : ℂ) ^ (p + q) • ((Y s)[[n]]) t := by
  have h := LinearMap.congr_fun (stateField_parity s n) t
  change parity (((Y s)[[n]]) t) = ((Y (parity s))[[n]]) (parity t) at h
  rw [h, hs, ht, map_smul]
  simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, smul_smul, ← pow_add,
    Nat.add_comm q p]

#print axioms translation
#print axioms translation_eq_total_mode
#print axioms translation_eq_conformal_ncoeff
#print axioms translation_vacuum
#print axioms OriginalOrbifoldBRSTStateField.Y_vacuum
#print axioms stateField_creation
#print axioms stateField_creativity
#print axioms stateField_covariance
#print axioms parity_involution
#print axioms stateField_parity
#print axioms homogeneous_mode_product

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTFieldAxioms
