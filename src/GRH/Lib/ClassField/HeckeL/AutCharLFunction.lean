import GRH.Lib.ClassField.HeckeL.HeckeContinuation
import GRH.Lib.ClassField.HeckeCharacter.SplittingCharOnU1
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Hecke L-functions: Euler product, continuation to s = 1, non-vanishing, prime densities
(known result; see Lib.ClassField.HeckeL.HeckeContinuation).

Part of: ℓ-adic avatar of an algebraic Hecke character and its local behaviour (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM field
(known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: L-function of a base-changed U(1) character: type, symmetry, non-vanishing for s ≥ 1. -/

noncomputable section


open WeilData Finset Complex Real
variable {E} [Field E] [CMType E] {ψ} {m : (E →+* ℂ) → ℤ} {k}
  (hk : ∀ w, m (Φ w) + m (star (Φ w)) = k) (H : IsHeckeOfType ψ fun w ↦ m (Φ w) - m (star (Φ w)))

/-- For ψ a character of finite ideles of type m(Φ_w) − m(Φ̄_w), with m(Φ_w) + m(Φ̄_w) = k
constant, the algebraic Hecke character ψ|·|^{k/2} of infinity type m. -/
def IsHeckeOfType.toAlgebraic : AlgHeckeChar E :=
  ⟨(ψ * .toHomUnits ⟨⟨(finIdeleAbs · |>.sqrt), by simp⟩, id (by
  simp [finIdeleAbs])⟩ ^ k, .ofAdd m), (_ ⊓ idelesUnitOff ∅).isOpen_mono (by aesop_cat (add simp
  [finIdeleAbs, ideleAbs_eq_prod_of_v_eq_one])) (H.1.and (isOpen_idelesUnitOff _)), fun x ↦ by
  simp [abs_norm_eq_prod_norm_sq, eq_inv_of_mul_eq_one_left (H.2 x), prod_embeddings_eq_prod_pairs,
    sqrt_prod, ← prod_zpow, ← mul_inv, ← prod_mul_distrib]; congr! 1
  simp [← hk ‹_›, div_zpow, zpow_add₀, zpow_sub₀, field, ← mul_zpow, mul_conj', sq]⟩

@[simp] lemma IsHeckeOfType.toAlgebraic_locIdele w x : ((H.toAlgebraic hk).1.1 (locIdele w x)).1 =
  ψ (locIdele w x) * √w.q ^ (k * (Valued.v x.1).log) := by simp [toAlgebraic,
  norm_locField_eq_q_zpow, sqrt_eq_rpow, zpow_mul', ← rpow_zpow_comm]

variable {n e} (χ : HeckeChar E) (ν : AutChar E)

/-- If the unitary Hecke character χ is z ↦ ∏_w (z_w/|z_w|)^{n_w} at infinity, its finite part
has type n: open kernel, and inverse to ∏_w (Φ_w x/|Φ_w x|)^{n_w} on E^×. -/
lemma HeckeChar.isHeckeOfType_finPart (h : ∀ z, χ.1 (.map (.inl ..) z) = ∏ w,
  (z.1 w / ‖z.1 w‖) ^ n w) : IsHeckeOfType χ.finPart n := ⟨χ.finPart.ker.isOpen_of_mem_nhds
  ((char_eventually_eq_one _ (χ.1.comp ⟨_, .units_map _ (.prodMk_right
  _)⟩).2).mono fun _ h ↦ by ext; congrm $h), fun x ↦ by simpa [h, Circle.ext_iff] using! χ.2 (.map
  (.inr ..) (principalIdele (K := E) x) * .map (.inl ..) (x.map (.pi _))) (by aesop)⟩

lemma WeilData.charUnramifiedAt_upsilon [SplittingChar E] (v : FinPlace E) : CharUnramifiedAt
  υ.finPart v := by simp_all [CharUnramifiedAt, HeckeChar.finPart, upsilon_eq_atUnif_zpow v]

/-- The partial Hecke L-function of the character x ↦ ν(x/x̄) of E, without the Euler factors at
S ∪ S̄. -/
def AutChar.L S := eulerProd (heckeCoeff ν.baseChange.finPart (.conjClosure S))

namespace AutChar.HasWeight

variable {ν S} {ψ : _} [h : ν.HasWeight e ψ] {w} (a : ψ w = 1) (b : ψ (star w) = 1)
include h

lemma baseChange_apply_inf z : ν.baseChange.1 (.map (.inl ..) z) = ∏ w, (z.1 w / ‖z.1 w‖) ^ (2 • e)
  w := by erw [h.2] <;> simp [coe_divStar, zpow_mul, ← OneMemClass.one_def]; grind [mul_conj']

/-- If the character ν of U(1)(𝔸) has weight e and tame part ψ, then the restriction of x ↦
ν(x/x̄) to the finite ideles of E is the finite part of a Hecke character of type 2e. -/
lemma isHeckeOfType : IsHeckeOfType ν.baseChange.finPart (2 • e) :=
  ν.baseChange.isHeckeOfType_finPart h.baseChange_apply_inf

/-- Let ν have weight e ≠ 0 and some tame part, and let S be finite. Then the L-function of x ↦
ν(x/x̄) without the factors at S ∪ S̄ is non-zero at every real s ≥ 1. -/
lemma L_ne_zero (hS : S.Finite) (he : e ≠ 0) {s} : 1 ≤ s → ν.L S s ≠ 0 :=
  h.isHeckeOfType.eulerProd_ne_zero hS.cj ((h.isHeckeOfType.pow 2).ne_one (by grind))

include a b

lemma charUnramifiedAt : CharUnramifiedAt ν.baseChange.finPart w :=
  fun _ _ ↦ by ext; simp [(h.exists_baseChange_finPart_locIdele ..).2, MulChar.one_apply, *]

/-- Let ν have weight e and tame part ψ, with ψ_w and ψ_w̄ trivial. Then the Hecke character x ↦
ν(x/x̄) takes mutually inverse values at the chosen uniformisers at w̄ and at w. -/
lemma atUnif_star : ν.baseChange.atUnif (star w) = (ν.baseChange.atUnif w)⁻¹ := by
  simpa [star_locIdele, (h.charUnramifiedAt b (by rwa [star_star])).apply_locIdele_eq_zpow
    (.map _ _), HeckeChar.atUnif] using
    (congr($(congr(ν.1 $(Subtype.ext (Prod.ext (star_mul_star ..) (star_mul' ..)).symm)).trans
    (map_inv ..)).1) : (ν.baseChange.finPart (star _)).1 = ν⁻¹.baseChange.atUnif w)

variable [WeilData E] (k j : ℤ)

/-- For a character ν of U(1) of weight e, the algebraic Hecke character ν(x/x̄) υ(x)^{−k}
|x|^{j−k/2}, of infinity type j + e − k on the CM type, j − e on its conjugate. -/
def toAlgebraic := IsHeckeOfType.toAlgebraic (m := fun σ ↦ j + ite (σ = Φ (.mk σ)) (e (.mk σ) - k)
  (-e (.mk σ))) (k := 2 * j - k) (by simp; lia) ((ν.baseChange * (υ ^ k)⁻¹).isHeckeOfType_finPart
  fun z ↦ by cases k <;> simp [h.baseChange_apply_inf, field, upsilon_eq_prod_mul_of_v_eq 1,
  two_mul, zpow_add₀, zpow_sub₀, (z.isUnit.apply _).ne_zero, prod_pow])

lemma charUnramifiedAt_toAlgebraic : CharUnramifiedAt (h.toAlgebraic k j).1.1 w :=
  fun _ _ ↦ by ext; simp [toAlgebraic, h.charUnramifiedAt .., charUnramifiedAt_upsilon .., *]
