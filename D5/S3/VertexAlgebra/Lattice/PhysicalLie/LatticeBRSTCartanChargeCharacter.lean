/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTCartanChargeCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTCartanChargeCharacter
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Intrinsic classification of original physical charge fibers by all actual Cartan adjoints. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
import Batteries.Tactic.OpenPrivate

/-!
SOURCE_ONLY_UNCOMPILED. No native elaboration, kernel, axiom-closure or typed
audit check has been attempted for this source package.

The carrier, class map, charge fiber and Lie bracket are the original supplier
definitions. Both quotient slots still allow primitives in ALL original
State D. Every charge, including zero, is covered. The complex inverse H is
arbitrary subject to BOTH original inverse-Gram equations.

Reuse: NeutralPhysicalCartan.project_physical supplies all FOUR physical
equations for each literal charge projection; ChargeCohomology supplies finite
charge support, reconstruction and actual quotient inclusion/projection;
NeutralPhysicalCartan.cartan_adjoint supplies the forward action, with no
nonzero-charge restriction. No projector/Q/ghost-number commutation is reproved.

Attribution: the original lattice-field suppliers retain Bakalov--Kac,
Carnahan and Kytölä attribution, and the BRST/current suppliers retain
Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman attribution.
Finite sums, complex linear algebra, integer casts and quotient maps use
Mathlib; existing private suppliers are opened with Batteries.Tactic.OpenPrivate.
This file adds the finite physical-component converse and full Cartan-character
separation. It makes no literature-novelty claim and constructs no Weyl
automorphism, Monster realization or completed string theory.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

open private project_physical from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open private chargeProject_mem chargeProject_on_fixed from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
open private bilinear_unit from
  D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTCartanChargeCharacter

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear unitCharge)
open LatticeSugawaraCurrents (gramComplex)
open LatticeMatterGhostCoupling (State)
open LatticeRelativeMassShell (fixedMomentum)
open LatticeQuartetContraction (chargeProject)
open LatticeBRSTCohomologyField (Cohomology cycles classOf)
open LatticeBRSTCohomologyBVSecondOrder (cohomologyCurrent)
open LatticeBRSTPhysicalLie (physicalStates physicalClass physicalImage)
open LatticeBRSTChargeCohomology
  (inclusion projection cycleInclusion cycleProjection chargeSupport sum_chargeProject)
open LatticeBRSTNeutralPhysicalCartan
  (gamma cartanClass cartanPhysicalImage cartan_adjoint)
open LatticeBRSTPhysicalChargeFiber (physicalChargeFiber)

/- The left inverse separates charge vectors. The public theorem below keeps
both inverses because its original quotient and physical bracket require them. -/
private theorem gamma_separates_charges
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (p q : Charge D)
    (h : ∀ v : Fin D.rank → ℂ, gamma D v p = gamma D v q) : p = q := by
  classical
  have hrow (i : Fin D.rank) :
      (bilinear D (unitCharge D i) p : ℂ) =
        (bilinear D (unitCharge D i) q : ℂ) := by
    simpa [gamma, ite_mul] using
      h (fun j => if j = i then (1 : ℂ) else 0)
  have hgram :
      (gramComplex D).mulVec (fun i => (p i : ℂ)) =
        (gramComplex D).mulVec (fun i => (q i : ℂ)) := by
    funext i
    simpa [Matrix.mulVec, dotProduct, gramComplex, bilinear_unit,
      Int.cast_sum, Int.cast_mul] using hrow i
  have hcoordinates :=
    congrArg (fun w : Fin D.rank → ℂ => H.mulVec w) hgram
  simp only [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec] at hcoordinates
  funext i
  exact (Int.cast_injective (α := ℂ)) (congrFun hcoordinates i)

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "Ph" => physicalImage D H h26 hHG hGH
local notation "J" => cohomologyCurrent D H h26 hHG hGH

/- Identification in the EXISTING quotient. The literal projector's action on
a fixed-charge state is reused; no new descent or commutation is asserted. -/
private theorem chargeProjection_physicalClass (p q : Charge D)
    (x : physicalStates D H) (hx : (x : State D) ∈ fixedMomentum D q) :
    inclusion D H h26 hHG hGH p
        (projection D H h26 hHG hGH p (physicalClass D H h26 hHG hGH x)) =
      if q = p then physicalClass D H h26 hHG hGH x else 0 := by
  classical
  let u : cycles D H := ⟨(x : State D), x.property.1⟩
  change classOf D H h26 hHG hGH
      (cycleInclusion D H p (cycleProjection D H p u)) =
    if q = p then classOf D H h26 hHG hGH u else 0
  by_cases hqp : q = p
  · rw [if_pos hqp]
    apply congrArg (classOf D H h26 hHG hGH)
    apply Subtype.ext
    exact (chargeProject_on_fixed D p q (x : State D) hx).trans (if_pos hqp)
  · rw [if_neg hqp]
    have hz : cycleInclusion D H p (cycleProjection D H p u) = 0 := by
      apply Subtype.ext
      exact (chargeProject_on_fixed D p q (x : State D) hx).trans (if_neg hqp)
    rw [hz, map_zero]

/-- A class in the entire original physical Lie image lies in the literal
charge-beta fiber exactly when ALL actual Cartan adjoints have character beta.
This includes beta = 0 and the zero class. No homogeneous representative,
projection invariance premise, finite-dimensionality or root is assumed. -/
theorem mem_physicalChargeFiber_iff_cartan_adjoint (beta : Charge D) (c : Ph) :
    (c : C) ∈ physicalChargeFiber D H h26 hHG hGH beta ↔
      ∀ v : Fin D.rank → ℂ,
        ⁅cartanPhysicalImage D H h26 hHG hGH v, c⁆ = gamma D v beta • c := by
  classical
  constructor
  · intro hc v
    exact cartan_adjoint D H h26 hHG hGH v beta c hc.2
  · intro heigen
    obtain ⟨x, hx⟩ := c.property
    -- Literal physical representatives of every charge component. All four
    -- physical equations are supplied by the existing private theorem.
    let xp (p : Charge D) : physicalStates D H :=
      ⟨chargeProject p (x : State D), project_physical D H hHG hGH p x⟩
    let component (p : Charge D) : Ph :=
      ⟨physicalClass D H h26 hHG hGH (xp p), ⟨xp p, rfl⟩⟩
    have component_range (p : Charge D) :
        ∃ a : LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p,
          inclusion D H h26 hHG hGH p a = (component p).val := by
      let a : LatticeBRSTChargeCohomology.sectorCycles D H p :=
        ⟨⟨chargeProject p (x : State D), chargeProject_mem D p (x : State D)⟩, by
          apply Subtype.ext
          exact (xp p).property.1⟩
      refine ⟨LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p a, ?_⟩
      rw [LatticeBRSTChargeCohomology.inclusion_sectorClassOf]
      rfl
    -- Reconstruction is first proved INSIDE physicalStates by its actual
    -- subtype map, then passed through the existing linear physicalClass.
    have representative_sum :
        (∑ p ∈ chargeSupport D (x : State D), xp p) = x := by
      apply Subtype.ext
      change (physicalStates D H).subtype
        (∑ p ∈ chargeSupport D (x : State D), xp p) = (x : State D)
      rw [map_sum]
      exact sum_chargeProject D (x : State D)
    have component_sum :
        (∑ p ∈ chargeSupport D (x : State D), (component p).val) = (c : C) := by
      change (∑ p ∈ chargeSupport D (x : State D),
        physicalClass D H h26 hHG hGH (xp p)) = (c : C)
      rw [← map_sum, representative_sum, hx]
    let P (p : Charge D) : C →ₗ[ℂ] C :=
      LinearMap.comp (R₁ := ℂ) (R₂ := ℂ) (R₃ := ℂ)
        (M₁ := C)
        (M₂ := LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p)
        (M₃ := C)
        (σ₁₂ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ) (σ₁₃ := RingHom.id ℂ)
        (inclusion D H h26 hHG hGH p) (projection D H h26 hHG hGH p)
    have project_c (p : Charge D) : P p (c : C) = (component p).val := by
      rw [← hx]
      rfl
    have project_component (p q : Charge D) :
        P p (component q).val = if q = p then (component q).val else 0 := by
      exact chargeProjection_physicalClass D H h26 hHG hGH p q (xp q)
        (chargeProject_mem D q (x : State D))
    have component_eigen (v : Fin D.rank → ℂ) (q : Charge D) :
        J (cartanClass D H h26 hHG hGH v) (component q).val =
          gamma D v q • (component q).val := by
      exact congrArg (fun z : Ph => (z : C))
        (cartan_adjoint D H h26 hHG hGH v q (component q) (component_range q))
    -- This is a finite calculation with the original quotient maps, not an
    -- assumption that an arbitrary submodule inherits a global direct sum.
    have project_adjoint (p : Charge D)
        (hp : p ∈ chargeSupport D (x : State D)) (v : Fin D.rank → ℂ) :
        P p (J (cartanClass D H h26 hHG hGH v) (c : C)) =
          gamma D v p • (component p).val := by
      calc
        _ = ∑ q ∈ chargeSupport D (x : State D),
            gamma D v q • P p (component q).val := by
              rw [← component_sum, map_sum, map_sum]
              apply Finset.sum_congr rfl
              intro q _
              rw [component_eigen v q, map_smul]
        _ = gamma D v p • (component p).val := by
              rw [Finset.sum_eq_single p]
              · rw [project_component p p, if_pos rfl]
              · intro q _ hqp
                rw [project_component p q, if_neg hqp, smul_zero]
              · intro hpnot
                exact (hpnot hp).elim
    have component_charge (p : Charge D)
        (hp : p ∈ chargeSupport D (x : State D))
        (hn : (component p).val ≠ 0) : p = beta := by
      apply gamma_separates_charges D H hHG p beta
      intro v
      have heq := congrArg (fun z : Ph => P p (z : C)) (heigen v)
      change P p (J (cartanClass D H h26 hHG hGH v) (c : C)) =
        P p (gamma D v beta • (c : C)) at heq
      rw [project_adjoint p hp v, map_smul, project_c p] at heq
      have hz : (gamma D v p - gamma D v beta) • (component p).val = 0 := by
        rw [sub_smul, heq, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hn)
    -- Every off-beta component is zero. The remaining finite sum belongs to
    -- the literal fiber even when beta is zero or absent from the support.
    rw [← component_sum]
    apply (physicalChargeFiber D H h26 hHG hGH beta).sum_mem
    intro p hp
    by_cases hz : (component p).val = 0
    · rw [hz]
      exact (physicalChargeFiber D H h26 hHG hGH beta).zero_mem
    · have hpb := component_charge p hp hz
      subst p
      exact ⟨(component beta).property, component_range beta⟩

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTCartanChargeCharacter
