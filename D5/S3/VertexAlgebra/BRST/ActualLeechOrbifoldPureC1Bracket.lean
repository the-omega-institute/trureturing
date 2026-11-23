/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPureC1Bracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldPureC1Bracket
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The original derived bracket on pure c(1) tensors is the matter zero mode. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCurrent

/-!
proof_shape: matterZeroMode, current_tmul_c1vac: content
admission_basis: escape-witness
escape_witness: The two actual matter tails bound the convolution on simple
tensors, and finite support extends to all matter tensors. The positive
antighost removal coefficient and the vacuum-field identity reduce the
original current to this convolution.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open LatticeGeneratingFieldLocality (Carrier)
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock vacuum)
open BcGhostQuartetCount (c1vac c1vac_eq)
open private assocY_tmul orb_tail from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private ghost_B_neg_down from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum
open private cut cut_kills right_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

private abbrev orbY :=
  TwistedGround.Orbifold.OriginalOrbifoldField.Y leechData leechUnit leechPosDef
private abbrev planeY := LatticeAllStateField.Y hyperbolicPlane

private def matterZeroTerm (k : ℤ) : Matter →ₗ[ℂ] Module.End ℂ Matter :=
  TensorProduct.map₂
    ((LinearMap.proj k).comp (VertexOperator.ncoeff.comp orbY))
    ((LinearMap.proj (-1 - k)).comp (VertexOperator.ncoeff.comp planeY))

private theorem matterZeroTerm_tmul (k : ℤ) (u v : Orbifold) (a b : Carrier hyperbolicPlane) :
    matterZeroTerm k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) =
      ((orbY u)[[k]]) v ⊗ₜ[ℂ] ((planeY a)[[-1 - k]]) b := rfl

private theorem matterZeroTerm_finite (φ ψ : Matter) :
    Function.HasFiniteSupport (fun k : ℤ => matterZeroTerm k φ ψ) := by
  induction φ using TensorProduct.inductionOn with
  | tmul u a =>
    induction ψ using TensorProduct.inductionOn with
    | tmul v b =>
      obtain ⟨M, hM⟩ := orb_tail u v
      let P := cut (planeY a) b
      apply (Set.finite_Icc (-P) (M - 1)).subset
      intro k hk
      by_contra hout
      have h : k < -P ∨ M - 1 < k := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hout
      apply hk
      dsimp only
      rw [matterZeroTerm_tmul]
      rcases h with h | h
      · have hP : cut (planeY a) b ≤ -1 - k := by
          dsimp [P] at h
          omega
        rw [cut_kills (planeY a) b (-1 - k) hP, TensorProduct.tmul_zero]
      · rw [hM k (by omega), TensorProduct.zero_tmul]
    | add x y hx hy =>
      simpa only [map_add, Pi.add_def] using hx.add hy
  | add x y hx hy =>
    simpa only [map_add, LinearMap.add_apply, Pi.add_def] using hx.add hy

/-- The matter zero mode is the statewise finite convolution of the original
orbifold and hyperbolic-plane fields at total mode zero. -/
def matterZeroMode : Matter →ₗ[ℂ] Module.End ℂ Matter where
  toFun φ := {
    toFun ψ := ∑ᶠ k : ℤ, matterZeroTerm k φ ψ
    map_add' x y := by
      simp only [map_add]
      exact finsum_add_distrib (matterZeroTerm_finite φ x) (matterZeroTerm_finite φ y)
    map_smul' z x := by
      simp only [map_smul, RingHom.id_apply]
      exact (smul_finsum' z (matterZeroTerm_finite φ x)).symm }
  map_add' x y := by
    apply LinearMap.ext
    intro ψ
    change (∑ᶠ k : ℤ, matterZeroTerm k (x + y) ψ) =
      (∑ᶠ k : ℤ, matterZeroTerm k x ψ) + (∑ᶠ k : ℤ, matterZeroTerm k y ψ)
    simp only [map_add, LinearMap.add_apply]
    exact finsum_add_distrib (matterZeroTerm_finite x ψ) (matterZeroTerm_finite y ψ)
  map_smul' z x := by
    apply LinearMap.ext
    intro ψ
    change (∑ᶠ k : ℤ, matterZeroTerm k (z • x) ψ) = z • ∑ᶠ k : ℤ, matterZeroTerm k x ψ
    simp only [map_smul, LinearMap.smul_apply]
    exact (smul_finsum' z (matterZeroTerm_finite x ψ)).symm

/-- In the native relative current the original b(-1) removes c(1) with
coefficient +1, and the ghost vacuum leaves the matter zero mode. -/
theorem current_tmul_c1vac (φ ψ : Matter) :
    current (φ ⊗ₜ[ℂ] c1vac) (ψ ⊗ₜ[ℂ] c1vac) =
      matterZeroMode φ ψ ⊗ₜ[ℂ] c1vac := by
  change originalMode 0 (VirasoroBRST.ghostB matter (-1) (φ ⊗ₜ[ℂ] c1vac))
    (ψ ⊗ₜ[ℂ] c1vac) = _
  have hb : VirasoroBRST.ghostB matter (-1) (φ ⊗ₜ[ℂ] c1vac) = φ ⊗ₜ[ℂ] vacuum := by
    change φ ⊗ₜ[ℂ] BcGhostFock.b (-1) c1vac = _
    rw [c1vac_eq, ghost_B_neg_down]
  rw [hb]
  clear hb
  induction φ using TensorProduct.inductionOn with
  | tmul u a =>
    induction ψ using TensorProduct.inductionOn with
    | tmul v b =>
      have hmap := map_finsum
        (reassoc.toLinearMap.comp ((TensorProduct.mk ℂ Matter Fock).flip c1vac))
        (matterZeroTerm_finite (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b))
      change reassoc (matterZeroMode (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c1vac) =
        ∑ᶠ k : ℤ, reassoc
          (matterZeroTerm k (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] c1vac) at hmap
      apply reassoc.injective
      rw [reassoc_originalMode, hmap]
      simp only [matterZeroTerm_tmul, reassoc, TensorProduct.assoc_tmul, assocY_tmul,
        right_vacuum_modes, TensorProduct.map_tmul, LinearMap.id_apply, zero_sub]
    | add x y hx hy =>
      simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy =>
    simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hx, hy]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeBracket
