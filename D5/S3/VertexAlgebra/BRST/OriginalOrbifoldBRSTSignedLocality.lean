/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTSignedLocality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTSignedLocality
   mirror-E: none(waiver:algebraic-original-brst-signed-locality)
   anchors: []
   utility: none
   digest: Ordered mode products and uniform signed locality on the original BRST tensor. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTStateField
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterVertexAlgebra
import D5.S3.Quantum.Fermionic.BcGhostStateFieldLocality
import D5.S3.VertexAlgebra.StateField.TensorCoefficientSignedLocality

/-! Both ordered mode products are finite coefficient convolutions. The signed tensor locality
theorem applies to pure homogeneous field states, and ghost parity projection extends it through
the algebraic tensor relations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTSignedLocality

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open OriginalOrbifoldCriticalMatter (Matter State)
open OriginalOrbifoldMatterTensorField (stateField)
open OriginalOrbifoldBRSTStateField (Y Y_tmul modeSummand_finite)
open FieldNormalProductLocality (delta deltaEnd)
open StateField.TensorCoefficientLocality (pairFinite_forward forwardBounded_modes)
open StateField.TensorCoefficientSignedLocality (tensorField_signed_locality_of_ordered_products)

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

local notation "YM" => stateField
local notation "YG" => BcGhostStateField.Y

/-- The ordered product on a pure input is the finite sum over the outer and inner matter mode
indices. Interchanging the two field states and their indices gives the opposite order. -/
theorem ordered_product_tmul (u v x : Matter) (a b y : Fock) (m n : ℤ) :
    ((Y (u ⊗ₜ[ℂ] a))[[m]]) (((Y (v ⊗ₜ[ℂ] b))[[n]]) (x ⊗ₜ[ℂ] y)) =
      ∑ᶠ ij : ℤ × ℤ, ((YM u)[[ij.1]]) (((YM v)[[ij.2]]) x) ⊗ₜ[ℂ]
        ((YG a)[[m - 1 - ij.1]]) (((YG b)[[n - 1 - ij.2]]) y) := by
  let inner (j : ℤ) : State := ((YM v)[[j]]) x ⊗ₜ[ℂ] ((YG b)[[n - 1 - j]]) y
  let term (ij : ℤ × ℤ) : State :=
    ((YM u)[[ij.1]]) (((YM v)[[ij.2]]) x) ⊗ₜ[ℂ]
      ((YG a)[[m - 1 - ij.1]]) (((YG b)[[n - 1 - ij.2]]) y)
  have hInner : Function.HasFiniteSupport inner :=
    modeSummand_finite (v ⊗ₜ[ℂ] b) (x ⊗ₜ[ℂ] y) n
  have hTerm : Function.HasFiniteSupport term :=
    pairFinite_forward (forwardBounded_modes (YM u) (YM v) x)
      (forwardBounded_modes (YG a) (YG b) y) m n
  let swap := Equiv.prodComm ℤ ℤ
  calc
    _ = ((Y (u ⊗ₜ[ℂ] a))[[m]]) (∑ᶠ j : ℤ, inner j) := by rw [Y_tmul v x b y n]
    _ = ∑ᶠ j : ℤ, ∑ᶠ i : ℤ, term (i, j) := by
      rw [map_finsum _ hInner]
      exact finsum_congr (fun j => Y_tmul u (((YM v)[[j]]) x) a (((YG b)[[n - 1 - j]]) y) m)
    _ = ∑ᶠ ij : ℤ × ℤ, term (swap ij) :=
      (finsum_curry (term ∘ swap) (hTerm.fun_comp_of_injective (g := swap) swap.injective)).symm
    _ = ∑ᶠ ij : ℤ × ℤ, term ij := finsum_comp_equiv swap

/-- Ghost parity on the original tensor carrier acts by the identity on matter. -/
def parity : Module.End ℂ State :=
  TensorProduct.map LinearMap.id CountableOccupationFock.parity

private def signedComm (sign : ℂ) (A B : VertexOperator ℂ State) :
    ℤ → ℤ → Module.End ℂ State :=
  fun m n => (A[[m]]) * (B[[n]]) - sign • ((B[[n]]) * (A[[m]]))

private def SignedLocal (sign : ℂ) (A B : VertexOperator ℂ State) : Prop :=
  ∃ N : ℕ, delta^[N] (signedComm sign A B) = 0

private theorem locality_add_distributions (F G : ℤ → ℤ → Module.End ℂ State)
    (hF : ∃ N : ℕ, delta^[N] F = 0) (hG : ∃ N : ℕ, delta^[N] G = 0) :
    ∃ N : ℕ, delta^[N] (F + G) = 0 := by
  obtain ⟨M, hM⟩ := hF
  obtain ⟨N, hN⟩ := hG
  refine ⟨max M N, ?_⟩
  have hFM := FiniteFieldLocality.monotone F M (max M N) (le_max_left _ _) hM
  have hGN := FiniteFieldLocality.monotone G N (max M N) (le_max_right _ _) hN
  change deltaEnd^[max M N] (F + G) = 0
  rw [← Module.End.pow_apply, map_add, Module.End.pow_apply, Module.End.pow_apply]
  change delta^[max M N] F + delta^[max M N] G = 0
  rw [hFM, hGN, add_zero]

private theorem local_add_left (sign : ℂ) (A B C : VertexOperator ℂ State)
    (hA : SignedLocal sign A C) (hB : SignedLocal sign B C) :
    SignedLocal sign (A + B) C := by
  have h : signedComm sign (A + B) C = signedComm sign A C + signedComm sign B C := by
    funext m n
    simp only [signedComm, map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    abel
  unfold SignedLocal
  rw [h]
  exact locality_add_distributions _ _ hA hB

private theorem local_add_right (sign : ℂ) (A B C : VertexOperator ℂ State)
    (hB : SignedLocal sign A B) (hC : SignedLocal sign A C) :
    SignedLocal sign A (B + C) := by
  have h : signedComm sign A (B + C) = signedComm sign A B + signedComm sign A C := by
    funext m n
    simp only [signedComm, map_add, Pi.add_apply, mul_add, add_mul, smul_add]
    abel
  unfold SignedLocal
  rw [h]
  exact locality_add_distributions _ _ hB hC

private theorem pure_locality (u v : Matter) (a b : Fock) (p q : ℕ)
    (ha : CountableOccupationFock.parity a = (-1 : ℂ) ^ p • a)
    (hb : CountableOccupationFock.parity b = (-1 : ℂ) ^ q • b) :
    SignedLocal ((-1 : ℂ) ^ (p * q)) (Y (u ⊗ₜ[ℂ] a)) (Y (v ⊗ₜ[ℂ] b)) := by
  obtain ⟨M, hM⟩ := OriginalOrbifoldMatterVertexAlgebra.stateField_locality u v
  obtain ⟨N, hN⟩ := BcGhostStateFieldLocality.stateField_locality a b p q ha hb
  exact ⟨M + N, tensorField_signed_locality_of_ordered_products
    (YM u) (YM v) (YG a) (YG b) (Y (u ⊗ₜ[ℂ] a)) (Y (v ⊗ₜ[ℂ] b)) _ M N hM hN
    (fun x y m n => ordered_product_tmul u v x a b y m n)
    (fun x y n m => ordered_product_tmul v u x b a y n m)⟩

private def ghostProjection (p : ℕ) : Module.End ℂ Fock :=
  (2 : ℂ)⁻¹ • (LinearMap.id + (-1 : ℂ) ^ p • CountableOccupationFock.parity)

private theorem ghostProjection_homogeneous (p : ℕ) (a : Fock) :
    CountableOccupationFock.parity (ghostProjection p a) =
      (-1 : ℂ) ^ p • ghostProjection p a := by
  let z : ℂ := (-1 : ℂ) ^ p
  have hz : z * z = 1 := by simp [z, ← mul_pow]
  have hinv := LinearMap.congr_fun CountableOccupationFock.parity_involution a
  change CountableOccupationFock.parity (CountableOccupationFock.parity a) = a at hinv
  change CountableOccupationFock.parity ((2 : ℂ)⁻¹ •
    (a + z • CountableOccupationFock.parity a)) =
      z • ((2 : ℂ)⁻¹ • (a + z • CountableOccupationFock.parity a))
  rw [map_smul, map_add, map_smul, hinv, smul_comm z (2 : ℂ)⁻¹]
  congr 1
  rw [smul_add, smul_smul, hz, one_smul, add_comm]

private def project (p : ℕ) : Module.End ℂ State :=
  TensorProduct.map LinearMap.id (ghostProjection p)

private theorem project_fixed (p : ℕ) (x : State)
    (hx : parity x = (-1 : ℂ) ^ p • x) : project p x = x := by
  have hz : (-1 : ℂ) ^ p * (-1 : ℂ) ^ p = 1 := by simp [← mul_pow]
  rw [project, ghostProjection, TensorProduct.map_smul_right, TensorProduct.map_add_right,
    TensorProduct.map_id, TensorProduct.map_smul_right]
  change (2 : ℂ)⁻¹ • (x + (-1 : ℂ) ^ p • parity x) = x
  rw [hx, smul_smul, hz, one_smul, ← two_smul ℂ x, smul_smul]
  norm_num

/-- A single exponent for each pair of homogeneous original BRST field states kills their
signed commutator as an endomorphism-valued distribution. -/
theorem stateField_locality (x y : State) (p q : ℕ)
    (hx : parity x = (-1 : ℂ) ^ p • x)
    (hy : parity y = (-1 : ℂ) ^ q • y) :
    ∃ N : ℕ, delta^[N] (fun m n =>
      ((Y x)[[m]]) * ((Y y)[[n]]) - (-1 : ℂ) ^ (p * q) •
        (((Y y)[[n]]) * ((Y x)[[m]]))) = 0 := by
  let sign : ℂ := (-1 : ℂ) ^ (p * q)
  have allProjected (s t : State) : SignedLocal sign (Y (project p s)) (Y (project q t)) := by
    induction s using TensorProduct.inductionOn with
    | tmul u a =>
      induction t using TensorProduct.inductionOn with
      | tmul v b =>
        simp only [project, TensorProduct.map_tmul, LinearMap.id_apply]
        exact pure_locality u v (ghostProjection p a) (ghostProjection q b) p q
          (ghostProjection_homogeneous p a) (ghostProjection_homogeneous q b)
      | add s t hs ht =>
        simp only [map_add]
        exact local_add_right sign _ _ _ hs ht
    | add s t hs ht =>
      simp only [map_add]
      exact local_add_left sign _ _ _ hs ht
  have h := allProjected x y
  rw [project_fixed p x hx, project_fixed q y hy] at h
  exact h

#print axioms parity
#print axioms ordered_product_tmul
#print axioms stateField_locality

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTSignedLocality
