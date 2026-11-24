/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechBRSTCoefficientRealForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechBRSTCoefficientRealForm
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Native coefficient conjugation of the actual Leech relative BRST complex. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldAbsoluteQTranspose
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldModeRealForm
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldEvenCurrent
import D5.S3.VertexAlgebra.Lattice.ActualCoefficientRealForm

/-!
The conjugation fixes each plane charge, commutes with the original differential
and relative constraints, and descends to the ghost-one kernel/image quotient.

proof_shape: coefficientConjugation_Q, coefficientConjugation_momentum_iff,
  coefficientConjugation_originalMode, coefficientConjugationCohomology_bracket: content
admission_basis: escape-witness
escape_witness: The two real stress states give conjugation on every original
matter Virasoro coefficient. Together with the real ghost modes and cubic charge
this yields conjugation of the actual finite BRST sum. Conjugation of the
occupation-word fields passes through both finite tensor convolutions.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators DirectSum TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (Orbifold)
open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane hyperbolicMatter matter)
open ActualLeechOrbifoldModeRealForm (orbifoldConjugation Y_ncoeff_kappa)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostBilinear (kappa kappa_apply kappa_b kappa_c kappa_ket)
open BcGhostCharge (charge ghostNumber)
open BcGhostChargeTensor (liftGhost)
open Lattice.ActualCoefficientRealForm
  (fixedKappa fixedKappa_involutive fixedKappa_leechStress kappa_hyperbolicStress stateField_kappa)
open LatticeGeneratingFieldLocality (Carrier Charge)
open LatticeMatterGhostCoupling (State)
open LatticeQuartetContraction (chargeMatter chargeProject tp_tmul)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open RelativeBracket (B N Degree Momentum current relative_iff)
open SourceBPZ.OriginalMatterHermitian
  (kappaCarrier kappaCarrier_add kappaCarrier_smul kappaCarrier_involutive kappaCarrier_single)
open TwistedGround.ActualLeechTwistedTensorRealForm
  (negativeConjugation negativeConjugation_involutive)

open private kappa_add kappa_smul from D5.S3.Quantum.Fermionic.BcGhostBilinear
open private number_ket from D5.S3.Quantum.Fermionic.BcGhostCharge
open private kappa_Qg from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldAbsoluteQTranspose
open private matter_mode_tmul rightLift_tmul from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

private def planeConjugation : Carrier hyperbolicPlane →ₗ⋆[ℂ] Carrier hyperbolicPlane where
  toFun := kappaCarrier
  map_add' := kappaCarrier_add
  map_smul' := kappaCarrier_smul

private def ghostConjugation : Fock →ₗ⋆[ℂ] Fock where
  toFun := kappa
  map_add' := kappa_add
  map_smul' := kappa_smul

private theorem orbifoldConjugation_involutive : Function.Involutive orbifoldConjugation := by
  intro v
  apply Prod.ext
  · exact fixedKappa_involutive leechData v.1
  · exact negativeConjugation_involutive v.2

private theorem ghostConjugation_involutive : Function.Involutive ghostConjugation := by
  intro g
  apply Finsupp.ext
  intro S
  change kappa (kappa g) S = g S
  simp only [kappa_apply, star_star]

private def matterConjugation : Matter →ₗ⋆[ℂ] Matter :=
  TensorProduct.map orbifoldConjugation planeConjugation

private theorem matterConjugation_tmul (v : Orbifold) (u : Carrier hyperbolicPlane) :
    matterConjugation (v ⊗ₜ[ℂ] u) = orbifoldConjugation v ⊗ₜ[ℂ] planeConjugation u :=
  TensorProduct.map_tmul _ _ _ _

/-- Coefficient conjugation on the original order of matter and ghost tensor factors. -/
def coefficientConjugation : ComplexState →ₗ⋆[ℂ] ComplexState :=
  TensorProduct.map matterConjugation ghostConjugation

theorem coefficientConjugation_tmul (v : Matter) (g : Fock) :
    coefficientConjugation (v ⊗ₜ[ℂ] g) = matterConjugation v ⊗ₜ[ℂ] ghostConjugation g :=
  TensorProduct.map_tmul _ _ _ _

private theorem matterConjugation_involutive : Function.Involutive matterConjugation := by
  have h : (matterConjugation.comp matterConjugation : Module.End ℂ Matter) = LinearMap.id := by
    apply TensorProduct.ext'
    intro v u
    have hu : planeConjugation (planeConjugation u) = u := kappaCarrier_involutive u
    simp only [LinearMap.comp_apply, LinearMap.id_apply, matterConjugation_tmul,
      orbifoldConjugation_involutive v, hu]
  intro x
  exact LinearMap.congr_fun h x

theorem coefficientConjugation_involutive : Function.Involutive coefficientConjugation := by
  have h : (coefficientConjugation.comp coefficientConjugation : Module.End ℂ ComplexState) =
      LinearMap.id := by
    apply TensorProduct.ext'
    intro v g
    simp only [LinearMap.comp_apply, LinearMap.id_apply, coefficientConjugation_tmul,
      matterConjugation_involutive v, ghostConjugation_involutive g]
  intro x
  exact LinearMap.congr_fun h x

private theorem orbifoldConjugation_mode (n : ℤ) (v : Orbifold) :
    orbifoldConjugation (ActualLeechOrbifoldMatter.mode n v) =
      ActualLeechOrbifoldMatter.mode n (orbifoldConjugation v) := by
  have hω : orbifoldConjugation ActualLeechOrbifoldMatter.omega =
      ActualLeechOrbifoldMatter.omega := by
    apply Prod.ext
    · exact fixedKappa_leechStress
    · exact negativeConjugation.map_zero
  have h := Y_ncoeff_kappa (n + 1) ActualLeechOrbifoldMatter.omega v
  rw [hω] at h
  exact h

private theorem planeConjugation_mode (n : ℤ) (u : Carrier hyperbolicPlane) :
    planeConjugation (hyperbolicMatter.mode n u) =
      hyperbolicMatter.mode n (planeConjugation u) := by
  have h := stateField_kappa hyperbolicPlane
    (LatticeActualConformalState.omega hyperbolicPlane (gramComplex hyperbolicPlane)) u (n + 1)
  let L := sugawaraMode hyperbolicPlane (gramComplex hyperbolicPlane) n
  change kappaCarrier (L u) = L (kappaCarrier u)
  simpa only [kappa_hyperbolicStress, LatticeActualConformalState.omega_modes] using h

private theorem matterConjugation_mode (n : ℤ) (v : Matter) :
    matterConjugation (matter.mode n v) = matter.mode n (matterConjugation v) := by
  have h : (matterConjugation.comp (matter.mode n) : Matter →ₗ⋆[ℂ] Matter) =
      (matter.mode n).comp matterConjugation := by
    apply TensorProduct.ext'
    intro w u
    simp only [LinearMap.comp_apply, matter_mode_tmul, map_add, matterConjugation_tmul,
      orbifoldConjugation_mode, planeConjugation_mode]
  exact LinearMap.congr_fun h v

private theorem coefficientConjugation_summand (n : ℤ) (x : ComplexState) :
    coefficientConjugation (VirasoroBRST.summand matter n x) =
      VirasoroBRST.summand matter n (coefficientConjugation x) := by
  have h : (coefficientConjugation.comp (VirasoroBRST.summand matter n) :
      ComplexState →ₗ⋆[ℂ] ComplexState) =
      (VirasoroBRST.summand matter n).comp coefficientConjugation := by
    apply TensorProduct.ext'
    intro v g
    have hc : ghostConjugation (BcGhostFock.c (-n) g) =
        BcGhostFock.c (-n) (ghostConjugation g) := kappa_c (-n) g
    simp only [LinearMap.comp_apply, VirasoroBRST.summand, TensorProduct.map_tmul,
      coefficientConjugation_tmul, matterConjugation_mode, hc]
  exact LinearMap.congr_fun h x

private theorem coefficientConjugation_liftGhost (G : Module.End ℂ Fock)
    (hG : ∀ g, ghostConjugation (G g) = G (ghostConjugation g)) (x : ComplexState) :
    coefficientConjugation (liftGhost G x) = liftGhost G (coefficientConjugation x) := by
  have h : (coefficientConjugation.comp (liftGhost G) : ComplexState →ₗ⋆[ℂ] ComplexState) =
      (liftGhost G).comp coefficientConjugation := by
    apply TensorProduct.ext'
    intro v g
    simp only [LinearMap.comp_apply, liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
      coefficientConjugation_tmul, hG]
  exact LinearMap.congr_fun h x

/-- The matter/c sum and the actual cubic ghost charge are both real. -/
theorem coefficientConjugation_Q (x : ComplexState) :
    coefficientConjugation (Q x) = Q (coefficientConjugation x) := by
  change coefficientConjugation
      ((∑ᶠ n : ℤ, VirasoroBRST.summand matter n x) + liftGhost BcGhostBRST.Qg x) =
    (∑ᶠ n : ℤ, VirasoroBRST.summand matter n (coefficientConjugation x)) +
      liftGhost BcGhostBRST.Qg (coefficientConjugation x)
  rw [map_add, coefficientConjugation_liftGhost _ kappa_Qg,
    map_finsum coefficientConjugation (VirasoroBRST.summand_finite matter x)]
  simp only [coefficientConjugation_summand]

theorem coefficientConjugation_ghostB (r : ℤ) (x : ComplexState) :
    coefficientConjugation (VirasoroBRST.ghostB matter r x) =
      VirasoroBRST.ghostB matter r (coefficientConjugation x) :=
  coefficientConjugation_liftGhost _ (kappa_b r) x

theorem coefficientConjugation_b0 (x : ComplexState) :
    coefficientConjugation (b0 x) = b0 (coefficientConjugation x) :=
  coefficientConjugation_ghostB 0 x

/-- The zero-index antighost Ward identity gives reality of the actual total energy. -/
theorem coefficientConjugation_E (x : ComplexState) :
    coefficientConjugation (E x) = E (coefficientConjugation x) := by
  have h : Q * b0 + b0 * Q = E := VirasoroBRST.Q_ward_b matter 0
  rw [← h]
  change coefficientConjugation (Q (b0 x) + b0 (Q x)) =
    Q (b0 (coefficientConjugation x)) + b0 (Q (coefficientConjugation x))
  rw [map_add, coefficientConjugation_Q, coefficientConjugation_b0,
    coefficientConjugation_b0, coefficientConjugation_Q]

private theorem ghostConjugation_number (g : Fock) :
    ghostConjugation (ghostNumber g) = ghostNumber (ghostConjugation g) := by
  classical
  have h : (ghostConjugation.comp ghostNumber : Fock →ₗ⋆[ℂ] Fock) =
      ghostNumber.comp ghostConjugation := by
    apply Finsupp.lhom_ext
    intro S z
    change ghostConjugation (ghostNumber (Finsupp.single S z)) =
      ghostNumber (ghostConjugation (Finsupp.single S z))
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    rw [hs]
    have hk : ghostConjugation (ket S) = ket S := kappa_ket S
    simp only [map_smulₛₗ, RingHom.id_apply, map_intCast, number_ket, hk]
  exact LinearMap.congr_fun h g

theorem coefficientConjugation_N (x : ComplexState) :
    coefficientConjugation (N x) = N (coefficientConjugation x) :=
  coefficientConjugation_liftGhost _ ghostConjugation_number x

private theorem planeConjugation_chargeMatter (p : Charge hyperbolicPlane)
    (u : Carrier hyperbolicPlane) :
    planeConjugation (chargeMatter p u) = chargeMatter p (planeConjugation u) := by
  change kappaCarrier (Finsupp.single p (u p)) = Finsupp.single p (kappaCarrier u p)
  exact kappaCarrier_single p (u p)

private def planeGhostConjugation : State hyperbolicPlane →ₗ⋆[ℂ] State hyperbolicPlane :=
  TensorProduct.map planeConjugation ghostConjugation

private theorem planeGhostConjugation_tmul (u : Carrier hyperbolicPlane) (g : Fock) :
    planeGhostConjugation (u ⊗ₜ[ℂ] g) = planeConjugation u ⊗ₜ[ℂ] ghostConjugation g :=
  TensorProduct.map_tmul _ _ _ _

private def assocConjugation : AssocState →ₗ⋆[ℂ] AssocState :=
  TensorProduct.map orbifoldConjugation planeGhostConjugation

private theorem assocConjugation_tmul (v : Orbifold) (y : State hyperbolicPlane) :
    assocConjugation (v ⊗ₜ[ℂ] y) = orbifoldConjugation v ⊗ₜ[ℂ] planeGhostConjugation y :=
  TensorProduct.map_tmul _ _ _ _

private theorem reassoc_coefficientConjugation (x : ComplexState) :
    reassoc (coefficientConjugation x) = assocConjugation (reassoc x) := by
  have h : (reassoc.toLinearMap.comp coefficientConjugation : ComplexState →ₗ⋆[ℂ] AssocState) =
      assocConjugation.comp reassoc.toLinearMap := by
    apply TensorProduct.ext'
    intro v g
    change reassoc (coefficientConjugation (v ⊗ₜ[ℂ] g)) =
      assocConjugation (reassoc (v ⊗ₜ[ℂ] g))
    induction v using TensorProduct.inductionOn with
    | tmul w u => rfl
    | add v w hv hw =>
      rw [TensorProduct.add_tmul, coefficientConjugation.map_add, reassoc.map_add,
        reassoc.map_add, assocConjugation.map_add, hv, hw]
  exact LinearMap.congr_fun h x

private theorem planeGhostConjugation_chargeProject (p : Charge hyperbolicPlane)
    (y : State hyperbolicPlane) :
    planeGhostConjugation (chargeProject p y) = chargeProject p (planeGhostConjugation y) := by
  have h : (planeGhostConjugation.comp (chargeProject p) :
      State hyperbolicPlane →ₗ⋆[ℂ] State hyperbolicPlane) =
      (chargeProject p).comp planeGhostConjugation := by
    apply TensorProduct.ext'
    intro u g
    simp only [LinearMap.comp_apply, chargeProject, tp_tmul, Module.End.one_apply,
      planeGhostConjugation_tmul, planeConjugation_chargeMatter]
  exact LinearMap.congr_fun h y

private theorem assocConjugation_chargeProject (p : Charge hyperbolicPlane) (y : AssocState) :
    assocConjugation (rightLift (chargeProject p) y) =
      rightLift (chargeProject p) (assocConjugation y) := by
  have h : (assocConjugation.comp (rightLift (chargeProject p)) : AssocState →ₗ⋆[ℂ] AssocState) =
      (rightLift (chargeProject p)).comp assocConjugation := by
    apply TensorProduct.ext'
    intro v a
    simp only [LinearMap.comp_apply, rightLift_tmul, assocConjugation_tmul,
      planeGhostConjugation_chargeProject]
  exact LinearMap.congr_fun h y

/-- Coefficient conjugation preserves the literal momentum without changing its label. -/
theorem coefficientConjugation_momentum_iff (p : Charge hyperbolicPlane) (x : ComplexState) :
    Momentum p (coefficientConjugation x) ↔ Momentum p x := by
  have hinj : Function.Injective assocConjugation := by
    intro a d had
    have h : reassoc (coefficientConjugation (reassoc.symm a)) =
        reassoc (coefficientConjugation (reassoc.symm d)) := by
      simpa only [reassoc_coefficientConjugation, reassoc.apply_symm_apply] using had
    exact reassoc.symm.injective (coefficientConjugation_involutive.injective (reassoc.injective h))
  unfold Momentum
  rw [reassoc_coefficientConjugation, ← assocConjugation_chargeProject]
  exact ⟨fun h => hinj h, congrArg assocConjugation⟩

private theorem coefficientConjugation_shell {p : Charge hyperbolicPlane} {x : ComplexState}
    (hx : reassoc x ∈ relativeShell p) :
    reassoc (coefficientConjugation x) ∈ relativeShell p := by
  obtain ⟨hp, hb, he⟩ := (relative_iff p x).mp hx
  refine (relative_iff p (coefficientConjugation x)).mpr ⟨?_, ?_, ?_⟩
  · exact (coefficientConjugation_momentum_iff p x).mpr hp
  · rw [← coefficientConjugation_b0, hb, map_zero]
  · rw [← coefficientConjugation_E, he, map_zero]

theorem coefficientConjugation_degree {g : ℤ} {x : ComplexState} (hx : Degree g x) :
    Degree g (coefficientConjugation x) := by
  change N (coefficientConjugation x) = (g : ℂ) • coefficientConjugation x
  rw [← coefficientConjugation_N, hx, map_smulₛₗ, map_intCast]

local instance (p : Charge hyperbolicPlane) : AddCommGroup (RelativeCohomology.NativeShell p) :=
  Submodule.addCommGroup _

/-- Conjugation restricts to the original relative carrier at each momentum. -/
def coefficientConjugationNativeShell (p : Charge hyperbolicPlane) :
    RelativeCohomology.NativeShell p →ₗ⋆[ℂ] RelativeCohomology.NativeShell p :=
  coefficientConjugation.restrict fun _ hx => coefficientConjugation_shell hx

theorem coefficientConjugationNativeShell_involutive (p : Charge hyperbolicPlane) :
    Function.Involutive (coefficientConjugationNativeShell p) := by
  intro x
  exact Subtype.ext (coefficientConjugation_involutive x.val)

theorem coefficientConjugationNativeShell_Q (p : Charge hyperbolicPlane)
    (x : RelativeCohomology.NativeShell p) :
    coefficientConjugationNativeShell p (RelativeCohomology.nativeQ p x) =
      RelativeCohomology.nativeQ p (coefficientConjugationNativeShell p x) :=
  Subtype.ext (coefficientConjugation_Q x.val)

section GhostModes

open FieldNormalProduct (identityField dividedDerivative)
open private signedNormalMinusOne generatingMode generatingField wordField Y_ket
  derivative_modes forward_finite reverse_finite from D5.S3.Quantum.Fermionic.BcGhostStateField

private theorem ghostConjugation_derivative (species : Bool) (order : ℕ) (n : ℤ) (v : Fock) :
    ghostConjugation (((dividedDerivative order (generatingField species))[[n]]) v) =
      ((dividedDerivative order (generatingField species))[[n]]) (ghostConjugation v) := by
  simp only [derivative_modes, LinearMap.smul_apply, map_smulₛₗ, map_intCast]
  have hb (k : ℤ) : ghostConjugation (BcGhostFock.b k v) =
      BcGhostFock.b k (ghostConjugation v) := kappa_b k v
  have hc (k : ℤ) : ghostConjugation (BcGhostFock.c k v) =
      BcGhostFock.c k (ghostConjugation v) := kappa_c k v
  cases species <;> simp [generatingMode, hb, hc]

private theorem ghostConjugation_signedNormal (sign : ℂ)
    (hsign : (starRingEnd ℂ) sign = sign) (A B : VertexOperator ℂ Fock)
    (hA : ∀ (n : ℤ) (v : Fock), ghostConjugation ((A[[n]]) v) = (A[[n]]) (ghostConjugation v))
    (hB : ∀ (n : ℤ) (v : Fock), ghostConjugation ((B[[n]]) v) = (B[[n]]) (ghostConjugation v))
    (n : ℤ) (v : Fock) :
    ghostConjugation (((signedNormalMinusOne sign A B).1[[n]]) v) =
      ((signedNormalMinusOne sign A B).1[[n]]) (ghostConjugation v) := by
  have hf : Function.HasFiniteSupport
      (fun i : ℕ => (A[[-(i : ℤ) - 1]]) ((B[[n + i]]) v)) := by
    simpa only [show ∀ i : ℕ, (-1 : ℤ) - i = -(i : ℤ) - 1 by intro i; omega] using
      forward_finite A B (-1) n v
  have hr : Function.HasFiniteSupport
      (fun i : ℕ => (B[[n - i - 1]]) ((A[[i]]) v)) := by
    simpa only [show ∀ i : ℕ, n - 1 - i = n - i - 1 by intro i; omega] using
      reverse_finite B A (n - 1) v
  rw [(signedNormalMinusOne sign A B).2 n v,
    (signedNormalMinusOne sign A B).2 n (ghostConjugation v),
    map_add, map_smulₛₗ, hsign, map_finsum ghostConjugation hf, map_finsum ghostConjugation hr]
  simp only [hA, hB]

private theorem ghostConjugation_word (w : List ℕ) (n : ℤ) (v : Fock) :
    ghostConjugation (((wordField w)[[n]]) v) = ((wordField w)[[n]]) (ghostConjugation v) := by
  induction w generalizing n v with
  | nil =>
    have h (k : ℤ) : (identityField : VertexOperator ℂ Fock)[[k]] =
        if k = -1 then LinearMap.id else 0 := by
      rw [identityField, VertexOperator.ncoeff_of_coeff]
      simp only [show -k - 1 = 0 ↔ k = -1 by omega]
    simp only [wordField, h]
    split_ifs <;> simp only [LinearMap.id_apply, LinearMap.zero_apply, map_zero]
  | cons j w ih =>
    simp only [wordField]
    exact ghostConjugation_signedNormal ((-1 : ℂ) ^ w.length)
      (by simp only [map_pow, map_neg, map_one])
      (dividedDerivative (j / 2) (generatingField (j % 2 == 1))) (wordField w)
      (ghostConjugation_derivative _ _) ih n v

private theorem ghostConjugation_field (n : ℤ) (a b : Fock) :
    ghostConjugation (((BcGhostStateField.Y a)[[n]]) b) =
      ((BcGhostStateField.Y (ghostConjugation a))[[n]]) (ghostConjugation b) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc => simp only [map_add, Pi.add_apply, LinearMap.add_apply, ha, hc]
  | single S z =>
    have hs : Finsupp.single S z = z • ket S := by simp [ket]
    have hk : ghostConjugation (ket S) = ket S := kappa_ket S
    simp only [hs, map_smulₛₗ, RingHom.id_apply, Pi.smul_apply, LinearMap.smul_apply,
      hk, Y_ket, ghostConjugation_word]

end GhostModes

section PlaneGhostModes

open private term term_tmul term_finite Y_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

private theorem planeConjugation_field (n : ℤ) (u v : Carrier hyperbolicPlane) :
    planeConjugation (((LatticeAllStateField.Y hyperbolicPlane u)[[n]]) v) =
      ((LatticeAllStateField.Y hyperbolicPlane (planeConjugation u))[[n]]) (planeConjugation v) :=
  stateField_kappa hyperbolicPlane u v n

private theorem planeGhostConjugation_field (n : ℤ) (s x : State hyperbolicPlane) :
    planeGhostConjugation (((LatticeMatterGhostStateField.Y hyperbolicPlane s)[[n]]) x) =
      ((LatticeMatterGhostStateField.Y hyperbolicPlane (planeGhostConjugation s))[[n]])
        (planeGhostConjugation x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      simp only [Y_modes]
      rw [map_finsum planeGhostConjugation
        (term_finite hyperbolicPlane (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) n)]
      apply finsum_congr
      intro k
      simp only [term_tmul, planeGhostConjugation_tmul, planeConjugation_field,
        ghostConjugation_field]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

end PlaneGhostModes

section OriginalModes

open private term term_tmul term_finite assocY_modes from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes

private theorem assocConjugation_field (n : ℤ) (s x : AssocState) :
    assocConjugation (((assocY s)[[n]]) x) =
      ((assocY (assocConjugation s))[[n]]) (assocConjugation x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      simp only [assocY_modes]
      rw [map_finsum assocConjugation (term_finite (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) n)]
      apply finsum_congr
      intro k
      simp only [term_tmul, assocConjugation_tmul, Y_ncoeff_kappa, planeGhostConjugation_field]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

theorem coefficientConjugation_originalMode (n : ℤ) (s x : ComplexState) :
    coefficientConjugation (originalMode n s x) =
      originalMode n (coefficientConjugation s) (coefficientConjugation x) := by
  apply reassoc.injective
  simpa only [reassoc_coefficientConjugation, reassoc_originalMode] using
    assocConjugation_field n (reassoc s) (reassoc x)

/-- In particular the actual antighost-descended zero mode is covariant. -/
theorem coefficientConjugation_current (x y : ComplexState) :
    coefficientConjugation (current x y) = current (coefficientConjugation x)
      (coefficientConjugation y) := by
  change coefficientConjugation (originalMode 0 (B x) y) =
    originalMode 0 (B (coefficientConjugation x)) (coefficientConjugation y)
  rw [coefficientConjugation_originalMode, coefficientConjugation_ghostB (-1) x]

end OriginalModes

section Cohomology

open RelativeBracket
  (nativeValue bracket bracket_mk MomentumH1 momentumBracket momentumBracket_incl)
open RelativeCohomology (GradedCycles GradedBoundaries GradedCohomology)
open private degree_shell native_mem native_degree native_closed cycleOf nativeValue_injective
  native_add native_smul native_boundary boundary_of_native native_cycleCurrent from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

local notation "Cycles" => fun p : Charge hyperbolicPlane => GradedCycles planeFrame planeBasis p 1
local notation "Boundaries" =>
  fun p : Charge hyperbolicPlane => GradedBoundaries planeFrame planeBasis p 1
local notation "H" => fun p : Charge hyperbolicPlane => GradedCohomology planeFrame planeBasis p 1

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _
local instance (p : Charge hyperbolicPlane) : AddCommGroup (Cycles p) :=
  Submodule.addCommGroup _

private theorem coefficientConjugation_closed {x : ComplexState} (hx : Q x = 0) :
    Q (coefficientConjugation x) = 0 := by
  rw [← coefficientConjugation_Q, hx, map_zero]

/-- Conjugation on the actual relative ghost-one cycles at the same momentum. -/
def coefficientConjugationCycles (p : Charge hyperbolicPlane) : Cycles p →ₗ⋆[ℂ] Cycles p := by
  let K (x : Cycles p) : Cycles p :=
    cycleOf (coefficientConjugation (nativeValue x)) (coefficientConjugation_shell (native_mem x))
      (coefficientConjugation_degree (native_degree x))
      (coefficientConjugation_closed (native_closed x))
  have value (x : Cycles p) : nativeValue (K x) = coefficientConjugation (nativeValue x) :=
    reassoc.symm_apply_apply _
  exact {
    toFun := K
    map_add' x y := nativeValue_injective _ (by simp only [value, native_add, map_add])
    map_smul' z x := nativeValue_injective _ (by
      simp only [value, native_smul, map_smulₛₗ]) }

theorem coefficientConjugationCycles_nativeValue {p : Charge hyperbolicPlane} (x : Cycles p) :
    nativeValue (coefficientConjugationCycles p x) = coefficientConjugation (nativeValue x) :=
  reassoc.symm_apply_apply _

private theorem coefficientConjugation_mem_boundaries {p : Charge hyperbolicPlane} {x : Cycles p}
    (hx : x ∈ Boundaries p) : coefficientConjugationCycles p x ∈ Boundaries p := by
  obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
  let v := reassoc.symm a.val.val
  have hs : reassoc v ∈ relativeShell p := by
    simpa only [v, reassoc.apply_symm_apply] using a.val.property
  have hd : Degree 0 v := by
    simpa only [sub_self] using (degree_shell p _ a.val).mp a.property
  apply boundary_of_native _ (coefficientConjugation v) (coefficientConjugation_shell hs)
    (coefficientConjugation_degree hd)
  rw [coefficientConjugationCycles_nativeValue, native_boundary, coefficientConjugation_Q]

private theorem coefficientConjugation_le_comap (p : Charge hyperbolicPlane) :
    Boundaries p ≤ Submodule.comap (coefficientConjugationCycles p) (Boundaries p) :=
  fun _ hx => Submodule.mem_comap.mpr (coefficientConjugation_mem_boundaries hx)

set_option maxHeartbeats 1500000 in
-- Elaborating the quotient map unfolds the concrete relative cycle and boundary spaces.
/-- Coefficient conjugation on the ghost-one kernel/image quotient at momentum p. -/
def coefficientConjugationCohomology (p : Charge hyperbolicPlane) : H p →ₗ⋆[ℂ] H p :=
  Submodule.mapQ (R := ℂ) (R₂ := ℂ) (M := Cycles p) (M₂ := Cycles p)
    (τ₁₂ := starRingEnd ℂ) (Boundaries p) (Boundaries p) (coefficientConjugationCycles p)
    (coefficientConjugation_le_comap p)

@[simp] theorem coefficientConjugationCohomology_mk {p : Charge hyperbolicPlane} (x : Cycles p) :
    coefficientConjugationCohomology p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (coefficientConjugationCycles p x) := rfl

theorem coefficientConjugationCohomology_involutive (p : Charge hyperbolicPlane) :
    Function.Involutive (coefficientConjugationCohomology p) := by
  intro x
  refine Submodule.Quotient.induction_on (Boundaries p) x fun a => ?_
  simp only [coefficientConjugationCohomology_mk]
  apply congrArg (fun z : Cycles p => (Submodule.Quotient.mk z : H p))
  apply nativeValue_injective
  simp only [coefficientConjugationCycles_nativeValue]
  exact coefficientConjugation_involutive (nativeValue a)

/-- The zero-mode calculation induces covariance of the actual relative quotient bracket. -/
theorem coefficientConjugationCohomology_bracket (p q : Charge hyperbolicPlane)
    (x : H p) (y : H q) :
    coefficientConjugationCohomology (p + q) (bracket p q x y) =
      bracket p q (coefficientConjugationCohomology p x)
        (coefficientConjugationCohomology q y) := by
  refine Submodule.Quotient.induction_on (Boundaries p) x fun a => ?_
  refine Submodule.Quotient.induction_on (Boundaries q) y fun b => ?_
  simp only [bracket_mk, coefficientConjugationCohomology_mk]
  apply congrArg (fun z : Cycles (p + q) => (Submodule.Quotient.mk z : H (p + q)))
  apply nativeValue_injective
  simp only [coefficientConjugationCycles_nativeValue, native_cycleCurrent,
    coefficientConjugation_current]

private def momentumConjugationAddHom : MomentumH1 →+ MomentumH1 :=
  DirectSum.map fun p => (coefficientConjugationCohomology p).toAddMonoidHom

private theorem momentumConjugationAddHom_apply (p : Charge hyperbolicPlane) (x : MomentumH1) :
    momentumConjugationAddHom x p = coefficientConjugationCohomology p (x p) :=
  DirectSum.map_apply _ p x

/-- The momentum sum carries the conjugation of each of its relative cohomology summands. -/
def coefficientConjugationMomentum : MomentumH1 →ₗ⋆[ℂ] MomentumH1 where
  toFun := momentumConjugationAddHom
  map_add' := momentumConjugationAddHom.map_add
  map_smul' z x := by
    apply (DirectSum.ext (ι := Charge hyperbolicPlane) (β := H))
    intro p
    calc
      momentumConjugationAddHom (z • x) p = coefficientConjugationCohomology p (z • x p) :=
        (momentumConjugationAddHom_apply p (z • x)).trans
          (congrArg (coefficientConjugationCohomology p)
            (DirectSum.smul_apply (R := ℂ) (M := H) z x p))
      _ = (starRingEnd ℂ) z • coefficientConjugationCohomology p (x p) :=
        (coefficientConjugationCohomology p).map_smulₛₗ z (x p)
      _ = ((starRingEnd ℂ) z • momentumConjugationAddHom x) p :=
        (congrArg (fun a : H p => (starRingEnd ℂ) z • a)
          (momentumConjugationAddHom_apply p x).symm).trans
          (DirectSum.smul_apply (R := ℂ) (M := H) ((starRingEnd ℂ) z)
            (momentumConjugationAddHom x) p).symm

local notation "incl" => DirectSum.lof ℂ (Charge hyperbolicPlane) H

@[simp] theorem coefficientConjugationMomentum_incl (p : Charge hyperbolicPlane) (x : H p) :
    coefficientConjugationMomentum (incl p x) = incl p (coefficientConjugationCohomology p x) := by
  change DirectSum.map (fun q => (coefficientConjugationCohomology q).toAddMonoidHom)
      (DirectSum.of H p x) = DirectSum.of H p (coefficientConjugationCohomology p x)
  exact DirectSum.map_of (fun q => (coefficientConjugationCohomology q).toAddMonoidHom) p x

theorem coefficientConjugationMomentum_involutive :
    Function.Involutive coefficientConjugationMomentum := by
  intro x
  apply (DirectSum.ext (ι := Charge hyperbolicPlane) (β := H))
  intro p
  have apply_component (y : MomentumH1) :
      coefficientConjugationMomentum y p = coefficientConjugationCohomology p (y p) :=
    momentumConjugationAddHom_apply p y
  exact (apply_component (coefficientConjugationMomentum x)).trans
    ((congrArg (coefficientConjugationCohomology p) (apply_component x)).trans
      (coefficientConjugationCohomology_involutive p (x p)))

theorem coefficientConjugationMomentum_bracket (x y : MomentumH1) :
    coefficientConjugationMomentum (momentumBracket x y) =
      momentumBracket (coefficientConjugationMomentum x) (coefficientConjugationMomentum y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | of p x =>
    change coefficientConjugationMomentum (momentumBracket (incl p x) y) =
      momentumBracket (coefficientConjugationMomentum (incl p x)) (coefficientConjugationMomentum y)
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of q y =>
      change coefficientConjugationMomentum (momentumBracket (incl p x) (incl q y)) =
        momentumBracket (coefficientConjugationMomentum (incl p x))
          (coefficientConjugationMomentum (incl q y))
      simp only [momentumBracket_incl, coefficientConjugationMomentum_incl,
        coefficientConjugationCohomology_bracket]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

end Cohomology

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
