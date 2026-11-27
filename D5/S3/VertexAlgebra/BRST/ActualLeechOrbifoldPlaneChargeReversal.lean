/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPlaneChargeReversal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPlaneChargeReversal
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The hyperbolic-plane lattice involution on the original Leech orbifold BRST complex. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPureC1Bracket
import D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

/-!
The lattice involution acts on the plane factor of the original complex.

proof_shape: chargeReversal_momentum_iff, chargeReversal_originalMode, chargeReversal_Q: content
admission_basis: escape-witness
escape_witness: The literal charge projection selects a single plane sector, and
the lattice involution reverses that sector with its oscillator signs. Mode
equivariance passes termwise through the statewise finite tensor convolutions
and the finite matter/c sum in the original differential.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldCriticalMatter (Matter hyperbolicPlane hyperbolicMatter matter)
open ActualLeechOrbifoldMatter (Orbifold)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open D5.S3.Quantum.Fermionic.BcGhostQuartetCount (c1vac)
open LatticeAllStateField (occurrences)
open LatticeGeneratingFieldLocality (Carrier Charge Index Oscillator)
open LatticeInvolution (theta theta_single theta_involutive sigma sigma_monomial
  stateField_theta)
open LatticeMatterGhostCoupling (State)
open LatticeQuartetContraction (chargeMatter chargeProject tp tp_tmul)
open LatticeSugawaraCurrents (gramComplex)
open RelativeBracket (Momentum current matterMode matterModeTerm matterModeTerm_finite
  matterModeTerm_tmul matterZeroMode current_tmul_c1vac)
open private matter_mode_tmul rightLift_tmul from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private theta_omega_fixed from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner

private abbrev planeTheta : Module.End ℂ (Carrier hyperbolicPlane) :=
  (theta hyperbolicPlane).toLinearMap

private theorem planeTheta_single (p : Charge hyperbolicPlane) (u : Oscillator hyperbolicPlane) :
    planeTheta (Finsupp.single p u) = Finsupp.single (-p) (sigma hyperbolicPlane u) :=
  theta_single hyperbolicPlane p u

/-- The complex-linear lattice involution on the plane factor of the literal matter. -/
def matterChargeReversal : Module.End ℂ Matter :=
  TensorProduct.map LinearMap.id planeTheta

private theorem matterChargeReversal_tmul (v : Orbifold) (u : Carrier hyperbolicPlane) :
    matterChargeReversal (v ⊗ₜ[ℂ] u) = v ⊗ₜ[ℂ] planeTheta u := rfl

/-- Charge reversal on the original BRST carrier, acting by the identity on bc ghosts. -/
def chargeReversal : Module.End ℂ ComplexState :=
  TensorProduct.map matterChargeReversal LinearMap.id

theorem chargeReversal_tmul (v : Matter) (g : Fock) :
    chargeReversal (v ⊗ₜ[ℂ] g) = matterChargeReversal v ⊗ₜ[ℂ] g := rfl

theorem chargeReversal_involutive : Function.Involutive chargeReversal := by
  have hm : matterChargeReversal.comp matterChargeReversal = LinearMap.id := by
    apply TensorProduct.ext'
    intro v u
    simp only [LinearMap.comp_apply, matterChargeReversal_tmul, LinearMap.id_apply,
      show planeTheta (planeTheta u) = u from theta_involutive hyperbolicPlane u]
  have h : chargeReversal.comp chargeReversal = LinearMap.id := by
    apply TensorProduct.ext'
    intro v g
    simp only [LinearMap.comp_apply, chargeReversal_tmul, LinearMap.id_apply,
      show matterChargeReversal (matterChargeReversal v) = v from LinearMap.congr_fun hm v]
  intro x
  exact LinearMap.congr_fun h x

/-- The actual oscillator sign on each monomial in the original plane charge basis. -/
theorem chargeReversal_monomial (v : Orbifold) (p : Charge hyperbolicPlane)
    (e : Index hyperbolicPlane →₀ ℕ) (g : Fock) :
    chargeReversal
        ((v ⊗ₜ[ℂ] Finsupp.single p (MvPolynomial.monomial e 1)) ⊗ₜ[ℂ] g) =
      ((-1 : ℂ) ^ (occurrences hyperbolicPlane e).length) •
        ((v ⊗ₜ[ℂ] Finsupp.single (-p) (MvPolynomial.monomial e 1)) ⊗ₜ[ℂ] g) := by
  rw [chargeReversal_tmul, matterChargeReversal_tmul, planeTheta_single, sigma_monomial,
    ← Finsupp.smul_single, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']

private def planeGhostChargeReversal : Module.End ℂ (State hyperbolicPlane) :=
  TensorProduct.map planeTheta LinearMap.id

private theorem planeGhostChargeReversal_tmul (u : Carrier hyperbolicPlane) (g : Fock) :
    planeGhostChargeReversal (u ⊗ₜ[ℂ] g) = planeTheta u ⊗ₜ[ℂ] g := rfl

private abbrev assocChargeReversal : Module.End ℂ AssocState :=
  rightLift planeGhostChargeReversal

private theorem reassoc_chargeReversal (x : ComplexState) :
    reassoc (chargeReversal x) = assocChargeReversal (reassoc x) := by
  have h : reassoc.toLinearMap.comp chargeReversal =
      assocChargeReversal.comp reassoc.toLinearMap := by
    apply TensorProduct.ext'
    intro v g
    induction v using TensorProduct.inductionOn with
    | tmul w u => rfl
    | add v w hv hw =>
      simp only [TensorProduct.add_tmul, map_add, hv, hw]
  exact LinearMap.congr_fun h x

private theorem planeTheta_chargeMatter (p : Charge hyperbolicPlane)
    (u : Carrier hyperbolicPlane) :
    planeTheta (chargeMatter p u) = chargeMatter (-p) (planeTheta u) := by
  have h : planeTheta.comp (chargeMatter p) = (chargeMatter (-p)).comp planeTheta := by
    apply Finsupp.lhom_ext
    intro q w
    change planeTheta (chargeMatter p (Finsupp.single q w)) =
      chargeMatter (-p) (planeTheta (Finsupp.single q w))
    by_cases hp : q = p
    · subst q
      simp [chargeMatter, planeTheta_single]
    · have hn : -q ≠ -p := fun hneg => hp (neg_inj.mp hneg)
      simp [chargeMatter, planeTheta_single, Ne.symm hp, Ne.symm hn]
  exact LinearMap.congr_fun h u

private theorem planeGhostChargeReversal_chargeProject (p : Charge hyperbolicPlane)
    (y : State hyperbolicPlane) :
    planeGhostChargeReversal (chargeProject p y) =
      chargeProject (-p) (planeGhostChargeReversal y) := by
  have h : planeGhostChargeReversal.comp (chargeProject p) =
      (chargeProject (-p)).comp planeGhostChargeReversal := by
    apply TensorProduct.ext'
    intro u g
    simp only [LinearMap.comp_apply, chargeProject, tp_tmul, Module.End.one_apply,
      planeGhostChargeReversal_tmul, planeTheta_chargeMatter]
  exact LinearMap.congr_fun h y

private theorem assocChargeReversal_chargeProject (p : Charge hyperbolicPlane) (y : AssocState) :
    assocChargeReversal (rightLift (chargeProject p) y) =
      rightLift (chargeProject (-p)) (assocChargeReversal y) := by
  have h : assocChargeReversal.comp (rightLift (chargeProject p)) =
      (rightLift (chargeProject (-p))).comp assocChargeReversal := by
    apply TensorProduct.ext'
    intro v z
    simp only [LinearMap.comp_apply, rightLift_tmul, planeGhostChargeReversal_chargeProject]
  exact LinearMap.congr_fun h y

/-- The original plane projector for p is intertwined with the projector for -p. -/
theorem chargeReversal_momentum_iff (p : Charge hyperbolicPlane) (x : ComplexState) :
    Momentum (-p) (chargeReversal x) ↔ Momentum p x := by
  have hinj : Function.Injective assocChargeReversal := by
    intro a b hab
    apply reassoc.symm.injective
    apply chargeReversal_involutive.injective
    apply reassoc.injective
    simpa only [reassoc_chargeReversal, LinearEquiv.apply_symm_apply] using hab
  unfold Momentum
  rw [reassoc_chargeReversal, ← assocChargeReversal_chargeProject]
  exact ⟨fun h => hinj h, congrArg assocChargeReversal⟩

private theorem planeTheta_mode (n : ℤ) (u v : Carrier hyperbolicPlane) :
    planeTheta (((LatticeAllStateField.Y hyperbolicPlane u)[[n]]) v) =
      ((LatticeAllStateField.Y hyperbolicPlane (planeTheta u))[[n]]) (planeTheta v) :=
  stateField_theta hyperbolicPlane u v n

/-- The literal plane Sugawara modes commute with its lattice involution. -/
theorem theta_plane_sugawara (n : ℤ) (u : Carrier hyperbolicPlane) :
    theta hyperbolicPlane (hyperbolicMatter.mode n u) =
      hyperbolicMatter.mode n (theta hyperbolicPlane u) := by
  let H := gramComplex hyperbolicPlane
  have h := stateField_theta hyperbolicPlane
    (LatticeActualConformalState.omega hyperbolicPlane H) u (n + 1)
  rw [theta_omega_fixed, LatticeActualConformalState.omega_modes] at h
  exact h

/-- Charge reversal commutes with the sum of the actual orbifold and plane modes. -/
theorem matterChargeReversal_virasoro (n : ℤ) (v : Matter) :
    matterChargeReversal (matter.mode n v) = matter.mode n (matterChargeReversal v) := by
  have h : matterChargeReversal.comp (matter.mode n) =
      (matter.mode n).comp matterChargeReversal := by
    apply TensorProduct.ext'
    intro w u
    have hplane : planeTheta (hyperbolicMatter.mode n u) =
        hyperbolicMatter.mode n (planeTheta u) := theta_plane_sugawara n u
    simp only [LinearMap.comp_apply, matter_mode_tmul, map_add, matterChargeReversal_tmul, hplane]
  exact LinearMap.congr_fun h v

private theorem chargeReversal_summand (n : ℤ) (x : ComplexState) :
    chargeReversal (VirasoroBRST.summand matter n x) =
      VirasoroBRST.summand matter n (chargeReversal x) := by
  have h : chargeReversal.comp (VirasoroBRST.summand matter n) =
      (VirasoroBRST.summand matter n).comp chargeReversal := by
    apply TensorProduct.ext'
    intro v g
    simp only [LinearMap.comp_apply, VirasoroBRST.summand, TensorProduct.map_tmul,
      chargeReversal_tmul, matterChargeReversal_virasoro]
  exact LinearMap.congr_fun h x

private theorem chargeReversal_ghostCharge (x : ComplexState) :
    chargeReversal (VirasoroBRST.ghostCharge matter x) =
      VirasoroBRST.ghostCharge matter (chargeReversal x) := by
  have h : chargeReversal.comp (VirasoroBRST.ghostCharge matter) =
      (VirasoroBRST.ghostCharge matter).comp chargeReversal := by
    apply TensorProduct.ext'
    intro v g
    rfl
  exact LinearMap.congr_fun h x

/-- Charge reversal intertwines the original differential via its statewise finite mode sum. -/
theorem chargeReversal_Q (x : ComplexState) : chargeReversal (Q x) = Q (chargeReversal x) := by
  change chargeReversal
      ((∑ᶠ n : ℤ, VirasoroBRST.summand matter n x) + VirasoroBRST.ghostCharge matter x) =
    (∑ᶠ n : ℤ, VirasoroBRST.summand matter n (chargeReversal x)) +
      VirasoroBRST.ghostCharge matter (chargeReversal x)
  rw [map_add, chargeReversal_ghostCharge,
    map_finsum chargeReversal (VirasoroBRST.summand_finite matter x)]
  simp only [chargeReversal_summand]

section PlaneGhostModes

open private term term_tmul term_finite Y_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

private theorem planeGhostChargeReversal_mode (n : ℤ) (s x : State hyperbolicPlane) :
    planeGhostChargeReversal (((LatticeMatterGhostStateField.Y hyperbolicPlane s)[[n]]) x) =
      ((LatticeMatterGhostStateField.Y hyperbolicPlane (planeGhostChargeReversal s))[[n]])
        (planeGhostChargeReversal x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      simp only [Y_modes]
      rw [map_finsum planeGhostChargeReversal
        (term_finite hyperbolicPlane (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) n)]
      apply finsum_congr
      intro k
      simp only [term_tmul, planeGhostChargeReversal_tmul, planeTheta_mode]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

end PlaneGhostModes

section OriginalModes

open private term term_tmul term_finite assocY_modes from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes

private theorem assocChargeReversal_mode (n : ℤ) (s x : AssocState) :
    assocChargeReversal (((assocY s)[[n]]) x) =
      ((assocY (assocChargeReversal s))[[n]]) (assocChargeReversal x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      simp only [assocY_modes]
      rw [map_finsum assocChargeReversal (term_finite (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) n)]
      apply finsum_congr
      intro k
      simp only [rightLift_tmul, term_tmul, planeGhostChargeReversal_mode]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add s t hs ht => simp only [map_add, Pi.add_apply, LinearMap.add_apply, hs, ht]

/-- Charge reversal acts on both inputs of every original superspace mode. -/
theorem chargeReversal_originalMode (n : ℤ) (s x : ComplexState) :
    chargeReversal (originalMode n s x) =
      originalMode n (chargeReversal s) (chargeReversal x) := by
  apply reassoc.injective
  simpa only [reassoc_chargeReversal, reassoc_originalMode] using
    assocChargeReversal_mode n (reassoc s) (reassoc x)

end OriginalModes

/-- Equivariance of the actual matter coefficient used for the pure c(1) bracket. -/
theorem matterChargeReversal_matterMode (n : ℤ) (s x : Matter) :
    matterChargeReversal (matterMode n s x) =
      matterMode n (matterChargeReversal s) (matterChargeReversal x) := by
  induction s using TensorProduct.inductionOn with
  | tmul u a =>
    induction x using TensorProduct.inductionOn with
    | tmul v b =>
      change matterChargeReversal (∑ᶠ k : ℤ, matterModeTerm n k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b)) =
        ∑ᶠ k : ℤ, matterModeTerm n k (matterChargeReversal (u ⊗ₜ[ℂ] a))
          (matterChargeReversal (v ⊗ₜ[ℂ] b))
      rw [map_finsum matterChargeReversal (matterModeTerm_finite n (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b))]
      apply finsum_congr
      intro k
      simp only [matterChargeReversal_tmul, matterModeTerm_tmul, planeTheta_mode]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

/-- On pure c(1) tensors the original current retains the same ghost state. -/
theorem chargeReversal_current_tmul_c1vac (s x : Matter) :
    chargeReversal (current (s ⊗ₜ[ℂ] c1vac) (x ⊗ₜ[ℂ] c1vac)) =
      current (matterChargeReversal s ⊗ₜ[ℂ] c1vac)
        (matterChargeReversal x ⊗ₜ[ℂ] c1vac) := by
  simp only [current_tmul_c1vac, chargeReversal_tmul, matterZeroMode,
    matterChargeReversal_matterMode]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
