/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTAbsoluteGroundCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTAbsoluteGroundCohomology
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Actual fixed-charge absolute ground compressed-energy kernel/image quotient. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTAbsoluteQuartetGround
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Source-only consumer of the unelaborated, terminal-collected supplier
LatticeBRSTAbsoluteQuartetGround, SHA256
cf2a99caa15220120811aaeebb175efe02827f4ad43fe01fef0f09e3ccd7b925.
Its original matter/ghost carriers, G coordinates, both ghost zero modes and
negative c0 occupation sign retain their suppliers' authorship. We consume
only its public coordinate, compressed-energy, cycle and boundary theorems;
we neither open private declarations nor repeat their energy calculation.

The quotient construction follows the pinned LatticeOriginalAbsoluteZeroCohomology
boundaryMap / Boundaries / boundaries_eq_ker / cohomologyEquiv mechanism
(SHA256 e69c56afd1ed1d7a8a5f14eb72d2662e0782a0b69864c965054809f179019ca8).
Mathlib's module quotients and isomorphism theorems retain their Apache 2.0
attribution (Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov).

Here the differential is literally the restriction of P0*c0*totalL0*P0.
No identification with original totalCharge or original all-state Q
cohomology is asserted. Those connections require the independent transfer
and compression proofs. No shell, b0, positivity or nonzero-charge premise
is imposed, and only the two inverse-Gram identities enter the restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBRSTAbsoluteGroundCohomology

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraConformal LatticePositiveEnergy
open LatticeLightConeCoordinates LatticeQuartetContraction
open LatticeMatterGhostCoupling (ghostC)
open LatticeRelativeMassShell (totalL0)
open LatticeRelativeBRSTCohomology.Ground (weight energyTarget)
open LatticeBRSTAbsoluteQuartetGround
  (Poly Exponent G absoluteGround E absolute_ground_coordinates compressed_energy
   compressed_energy_cycle_iff compressed_energy_boundary_iff)
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open MvPolynomial

variable {D : LatticeData} {t : ℕ}

/-- A finite polynomial projection, formed by the existing algebraic basis
functional calculus. Its definition never introduces a power series. -/
def pi (D : LatticeData) (t : ℕ) (p : Charge D) : Module.End ℂ (Poly t) :=
  diagonal (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ)
    (fun nu => if (weight nu : ℤ) + chargeEnergy D p = 1 then 1 else 0)

theorem pi_coefficient (p : Charge D) (f : Poly t) (nu : Exponent t) :
    (pi D t p f).coeff nu =
      if (weight nu : ℤ) + chargeEnergy D p = 1 then f.coeff nu else 0 := by
  have h := diagonal_coefficient (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ)
    (fun nu => if (weight nu : ℤ) + chargeEnergy D p = 1 then 1 else 0) f nu
  change (pi D t p f).coeff nu =
    (if (weight nu : ℤ) + chargeEnergy D p = 1 then 1 else 0) * f.coeff nu at h
  rw [h]
  split_ifs <;> simp

theorem pi_mem (p : Charge D) (f : Poly t) :
    pi D t p f ∈ energyTarget D t p := by
  intro nu hnu
  rw [pi_coefficient, if_neg hnu]

theorem pi_fixed_iff (p : Charge D) (f : Poly t) :
    pi D t p f = f ↔ f ∈ energyTarget D t p := by
  constructor
  · intro hf nu hnu
    have hc := congrArg (fun g : Poly t => g.coeff nu) hf
    rw [pi_coefficient, if_neg hnu] at hc
    exact hc.symm
  · intro hf
    ext nu
    rw [pi_coefficient]
    by_cases hnu : (weight nu : ℤ) + chargeEnergy D p = 1
    · exact if_pos hnu
    · rw [if_neg hnu, hf nu hnu]

theorem range_pi (p : Charge D) :
    LinearMap.range (pi D t p) = energyTarget D t p := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact pi_mem p g
  · intro hf
    exact ⟨f, (pi_fixed_iff p f).mpr hf⟩

private theorem pi_zero_iff (p : Charge D) (f : Poly t) :
    pi D t p f = 0 ↔
      ∀ nu, (weight nu : ℤ) + chargeEnergy D p = 1 → f.coeff nu = 0 := by
  constructor
  · intro hf nu hnu
    have hc := congrArg (fun g : Poly t => g.coeff nu) hf
    have hz : (0 : Poly t).coeff nu = 0 := rfl
    rw [pi_coefficient, if_pos hnu, hz] at hc
    exact hc
  · intro hf
    ext nu
    change (pi D t p f).coeff nu = 0
    rw [pi_coefficient]
    by_cases hnu : (weight nu : ℤ) + chargeEnergy D p = 1
    · rw [if_pos hnu, hf nu hnu]
    · exact if_neg hnu

variable (F : NullFrame D) (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D)

/- At zero, public uniqueness already forces the kernel of G to vanish.
This avoids any reliance on the supplier's private G_injective or G_mem. -/
private theorem G_injective_from_coordinates : Function.Injective (G F B p) := by
  have hz : P0 F B (0 : State D) = 0 ∧ chargeProject p (0 : State D) = 0 := by
    simp
  obtain ⟨fg, hfg, huniq⟩ := (absolute_ground_coordinates F B p 0).mp hz
  have hfg0 : (0 : Poly t × Poly t) = fg :=
    huniq 0 (map_zero (G F B p)).symm
  intro uv wx he
  have hsub : (0 : State D) = G F B p (uv - wx) := by
    rw [map_sub, he, sub_self]
  have hzero : uv - wx = 0 := (huniq (uv - wx) hsub).trans hfg0.symm
  exact sub_eq_zero.mp hzero

private theorem G_mem_from_coordinates (fg : Poly t × Poly t) :
    G F B p fg ∈ absoluteGround F B p := by
  apply (absolute_ground_coordinates F B p (G F B p fg)).mpr
  refine ⟨fg, rfl, ?_⟩
  intro uv huv
  exact G_injective_from_coordinates F B p huv.symm

/-- The literal original-state G, with only its codomain restricted. -/
def groundState : (Poly t × Poly t) →ₗ[ℂ] absoluteGround F B p :=
  (G F B p).codRestrict _ (G_mem_from_coordinates F B p)

private theorem groundState_bijective : Function.Bijective (groundState F B p) := by
  constructor
  · intro fg uv he
    exact G_injective_from_coordinates F B p (congrArg Subtype.val he)
  · intro x
    obtain ⟨fg, hfg, huniq⟩ := (absolute_ground_coordinates F B p (x : State D)).mp
      x.property
    exact ⟨fg, Subtype.ext hfg.symm⟩

/-- Linear unrestricted coordinates, derived from the public unique-coordinate
biconditional on the actual fixed-point submodule. -/
def coordinates : absoluteGround F B p ≃ₗ[ℂ] (Poly t × Poly t) :=
  (show (Poly t × Poly t) ≃ₗ[ℂ] absoluteGround F B p from
    { groundState F B p,
      Equiv.ofBijective (groundState F B p) (groundState_bijective F B p) with }).symm

@[simp] theorem coordinates_groundState (fg : Poly t × Poly t) :
    coordinates F B p (groundState F B p fg) = fg :=
  (coordinates F B p).apply_symm_apply fg

@[simp] theorem groundState_coordinates (x : absoluteGround F B p) :
    groundState F B p (coordinates F B p x) = x :=
  (coordinates F B p).symm_apply_apply x

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

include hHG hGH in
private theorem compressed_energy_mem (x : absoluteGround F B p) :
    (P0 F B * ghostC D 0 * totalL0 D H * P0 F B) (x : State D) ∈
      absoluteGround F B p := by
  have hx : (x : State D) = G F B p (coordinates F B p x) :=
    (congrArg Subtype.val (groundState_coordinates F B p x)).symm
  rw [hx, compressed_energy F B H hHG hGH p]
  exact G_mem_from_coordinates F B p _

/-- The true restriction of the literal ambient compressed-energy operator.
The coordinate action is a subsequent theorem, not its definition. -/
def d : Module.End ℂ (absoluteGround F B p) :=
  (((P0 F B * ghostC D 0 * totalL0 D H * P0 F B).comp
    (absoluteGround F B p).subtype)).codRestrict _
      (compressed_energy_mem F B p H hHG hGH)

theorem d_groundState (fg : Poly t × Poly t) :
    d F B p H hHG hGH (groundState F B p fg) =
      groundState F B p (0, E p fg.1) := by
  apply Subtype.ext
  exact compressed_energy F B H hHG hGH p fg

/-- Actual restricted square zero, proved from the supplied action twice. -/
theorem d_square : d F B p H hHG hGH * d F B p H hHG hGH = 0 := by
  apply LinearMap.ext
  intro x
  rw [← groundState_coordinates F B p x]
  change d F B p H hHG hGH
    (d F B p H hHG hGH (groundState F B p (coordinates F B p x))) = 0
  simp only [d_groundState, map_zero]
  exact (groundState F B p).map_zero

abbrev Cycles : Submodule ℂ (absoluteGround F B p) :=
  LinearMap.ker (d F B p H hHG hGH)

theorem groundState_cycle_iff (fg : Poly t × Poly t) :
    groundState F B p fg ∈ Cycles F B p H hHG hGH ↔
      fg.1 ∈ energyTarget D t p := by
  constructor
  · intro hx
    have hd : d F B p H hHG hGH (groundState F B p fg) = 0 := hx
    exact (compressed_energy_cycle_iff F B H hHG hGH p fg).mp
      (congrArg Subtype.val hd)
  · intro hf
    change d F B p H hHG hGH (groundState F B p fg) = 0
    apply Subtype.ext
    exact (compressed_energy_cycle_iff F B H hHG hGH p fg).mpr hf

/-- Incoming boundary map is the actual restricted d with kernel codomain. -/
def boundaryMap : absoluteGround F B p →ₗ[ℂ] Cycles F B p H hHG hGH :=
  (d F B p H hHG hGH).codRestrict _ (fun x =>
    LinearMap.congr_fun (d_square F B p H hHG hGH) x)

def Boundaries : Submodule ℂ (Cycles F B p H hHG hGH) :=
  LinearMap.range (boundaryMap F B p H hHG hGH)

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

local instance : AddCommGroup (Carrier D) := inferInstance
local instance : AddCommGroup (State D) := inferInstance
local instance : AddCommGroup (absoluteGround F B p) := inferInstance
local instance : AddCommGroup (Cycles F B p H hHG hGH) := inferInstance

/-- The existing mathlib module quotient of the actual kernel by actual images. -/
abbrev Cohomology : Type :=
  Cycles F B p H hHG hGH ⧸ Boundaries F B p H hHG hGH

private theorem cycle_first (x : Cycles F B p H hHG hGH) :
    (coordinates F B p x.1).1 ∈ energyTarget D t p := by
  apply (groundState_cycle_iff F B p H hHG hGH (coordinates F B p x.1)).mp
  rw [groundState_coordinates]
  exact x.property

/-- For an actual cycle with unrestricted G coordinates (f,g), read (f,pi g). -/
def classMap : Cycles F B p H hHG hGH →ₗ[ℂ]
    (energyTarget D t p × energyTarget D t p) where
  toFun x := (⟨(coordinates F B p x.1).1, cycle_first F B p H hHG hGH x⟩,
    ⟨pi D t p (coordinates F B p x.1).2, pi_mem p _⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · change (coordinates F B p (x.1 + y.1)).1 =
        (coordinates F B p x.1).1 + (coordinates F B p y.1).1
      exact congrArg Prod.fst ((coordinates F B p).map_add x.1 y.1)
    · change pi D t p (coordinates F B p (x.1 + y.1)).2 =
        pi D t p (coordinates F B p x.1).2 + pi D t p (coordinates F B p y.1).2
      exact (congrArg (fun fg : Poly t × Poly t => pi D t p fg.2)
        ((coordinates F B p).map_add x.1 y.1)).trans ((pi D t p).map_add _ _)
  map_smul' a x := by
    apply Prod.ext <;> apply Subtype.ext
    · change (coordinates F B p (a • x.1)).1 = a • (coordinates F B p x.1).1
      exact congrArg Prod.fst ((coordinates F B p).map_smul a x.1)
    · change pi D t p (coordinates F B p (a • x.1)).2 =
        a • pi D t p (coordinates F B p x.1).2
      exact (congrArg (fun fg : Poly t × Poly t => pi D t p fg.2)
        ((coordinates F B p).map_smul a x.1)).trans ((pi D t p).map_smul a _)

/-- Canonical representatives are literal original-state G(f,g), retaining c0. -/
def representative : (energyTarget D t p × energyTarget D t p) →ₗ[ℂ]
    Cycles F B p H hHG hGH where
  toFun fg := ⟨groundState F B p ((fg.1 : Poly t), (fg.2 : Poly t)),
    (groundState_cycle_iff F B p H hHG hGH _).mpr fg.1.property⟩
  map_add' x y := by
    apply Subtype.ext
    change groundState F B p
        ((x.1 : Poly t) + (y.1 : Poly t), (x.2 : Poly t) + (y.2 : Poly t)) =
      groundState F B p ((x.1 : Poly t), (x.2 : Poly t)) +
        groundState F B p ((y.1 : Poly t), (y.2 : Poly t))
    exact (groundState F B p).map_add
      ((x.1 : Poly t), (x.2 : Poly t)) ((y.1 : Poly t), (y.2 : Poly t))
  map_smul' a x := by
    apply Subtype.ext
    change groundState F B p (a • (x.1 : Poly t), a • (x.2 : Poly t)) =
      a • groundState F B p ((x.1 : Poly t), (x.2 : Poly t))
    exact (groundState F B p).map_smul a ((x.1 : Poly t), (x.2 : Poly t))

theorem representative_state (fg : energyTarget D t p × energyTarget D t p) :
    ((representative F B p H hHG hGH fg).1 : State D) =
      G F B p ((fg.1 : Poly t), (fg.2 : Poly t)) := rfl

@[simp] theorem classMap_representative (fg : energyTarget D t p × energyTarget D t p) :
    classMap F B p H hHG hGH (representative F B p H hHG hGH fg) = fg := by
  apply Prod.ext <;> apply Subtype.ext
  · change (coordinates F B p
      (groundState F B p ((fg.1 : Poly t), (fg.2 : Poly t)))).1 = (fg.1 : Poly t)
    rw [coordinates_groundState]
  · change pi D t p (coordinates F B p
      (groundState F B p ((fg.1 : Poly t), (fg.2 : Poly t)))).2 = (fg.2 : Poly t)
    rw [coordinates_groundState]
    exact (pi_fixed_iff p (fg.2 : Poly t)).mpr fg.2.property

theorem classMap_surjective : Function.Surjective (classMap F B p H hHG hGH) :=
  fun fg => ⟨representative F B p H hHG hGH fg,
    classMap_representative F B p H hHG hGH fg⟩

private theorem classMap_zero_iff (x : Cycles F B p H hHG hGH) :
    classMap F B p H hHG hGH x = 0 ↔
      (coordinates F B p x.1).1 = 0 ∧
        ∀ nu, (weight nu : ℤ) + chargeEnergy D p = 1 →
          ((coordinates F B p x.1).2).coeff nu = 0 := by
  constructor
  · intro hx
    have hf : (coordinates F B p x.1).1 = 0 :=
      congrArg (fun z : energyTarget D t p × energyTarget D t p => (z.1 : Poly t)) hx
    have hg : pi D t p (coordinates F B p x.1).2 = 0 :=
      congrArg (fun z : energyTarget D t p × energyTarget D t p => (z.2 : Poly t)) hx
    exact ⟨hf, (pi_zero_iff p _).mp hg⟩
  · rintro ⟨hf, hg⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact hf
    · exact (pi_zero_iff p _).mpr hg

/-- Exactness is proved using the public concrete boundary equivalence.
Its reverse direction supplies a genuine finite polynomial uv, hence an
actual preimage groundState uv in the original fixed-point submodule. -/
theorem boundaries_eq_ker : Boundaries F B p H hHG hGH =
    LinearMap.ker (classMap F B p H hHG hGH) := by
  ext x
  change (∃ y, boundaryMap F B p H hHG hGH y = x) ↔
    classMap F B p H hHG hGH x = 0
  rw [classMap_zero_iff]
  let fg := coordinates F B p x.1
  have hx : G F B p fg = (x.1 : State D) :=
    congrArg Subtype.val (groundState_coordinates F B p x.1)
  constructor
  · rintro ⟨y, hy⟩
    apply (compressed_energy_boundary_iff F B H hHG hGH p fg).mp
    refine ⟨coordinates F B p y, ?_⟩
    have hyG : G F B p (coordinates F B p y) = (y : State D) :=
      congrArg Subtype.val (groundState_coordinates F B p y)
    have hy' : (P0 F B * ghostC D 0 * totalL0 D H * P0 F B) (y : State D) =
        (x.1 : State D) :=
      congrArg (fun z : Cycles F B p H hHG hGH => (z.1 : State D)) hy
    rw [hyG]
    exact hy'.trans hx.symm
  · intro hc
    obtain ⟨uv, huv⟩ :=
      (compressed_energy_boundary_iff F B H hHG hGH p fg).mpr hc
    refine ⟨groundState F B p uv, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact huv.trans hx

/-- Canonical actual original-ground cohomology, for EVERY integral charge,
arbitrary null frame and transverse basis, and both inverse-Gram laws only. -/
def cohomologyEquiv : Cohomology F B p H hHG hGH ≃ₗ[ℂ]
    (energyTarget D t p × energyTarget D t p) :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_ker F B p H hHG hGH)).trans
    ((classMap F B p H hHG hGH).quotKerEquivOfSurjective
      (classMap_surjective F B p H hHG hGH))

@[simp] theorem cohomologyEquiv_mk (x : Cycles F B p H hHG hGH) :
    cohomologyEquiv F B p H hHG hGH ((Boundaries F B p H hHG hGH).mkQ x) =
      classMap F B p H hHG hGH x := by
  simp only [cohomologyEquiv, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Readout on the actual unrestricted original-state representative G(f,g). -/
theorem cohomologyEquiv_original (f g : Poly t) (hf : f ∈ energyTarget D t p) :
    cohomologyEquiv F B p H hHG hGH
      ((Boundaries F B p H hHG hGH).mkQ
        ⟨groundState F B p (f,g),
          (groundState_cycle_iff F B p H hHG hGH (f,g)).mpr hf⟩) =
      (⟨f,hf⟩, ⟨pi D t p g, pi_mem p g⟩) := by
  rw [cohomologyEquiv_mk]
  apply Prod.ext <;> apply Subtype.ext
  · change (coordinates F B p (groundState F B p (f,g))).1 = f
    rw [coordinates_groundState]
  · change pi D t p (coordinates F B p (groundState F B p (f,g))).2 = pi D t p g
    rw [coordinates_groundState]

/-- Each actual K-cycle has exactly one energyTarget pair modulo an ACTUAL
K-preimage IN A. The removed vector is not merely declared to be exact. -/
theorem canonical_original_representative (x : Cycles F B p H hHG hGH) :
    ∃! fg : energyTarget D t p × energyTarget D t p,
      ∃ y : absoluteGround F B p,
        (x.1 : State D) - G F B p ((fg.1 : Poly t), (fg.2 : Poly t)) =
          (P0 F B * ghostC D 0 * totalL0 D H * P0 F B) (y : State D) := by
  have hmem : x - representative F B p H hHG hGH (classMap F B p H hHG hGH x) ∈
      Boundaries F B p H hHG hGH := by
    rw [boundaries_eq_ker]
    change classMap F B p H hHG hGH
      (x - representative F B p H hHG hGH (classMap F B p H hHG hGH x)) = 0
    rw [(classMap F B p H hHG hGH).map_sub, classMap_representative, sub_self]
  obtain ⟨y, hy⟩ := hmem
  refine ⟨classMap F B p H hHG hGH x, ⟨y, ?_⟩, ?_⟩
  · exact (congrArg (fun z : Cycles F B p H hHG hGH => (z.1 : State D)) hy).symm
  · rintro fg ⟨z, hz⟩
    have hb : x - representative F B p H hHG hGH fg ∈ Boundaries F B p H hHG hGH := by
      refine ⟨z, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hz.symm
    rw [boundaries_eq_ker] at hb
    have he : classMap F B p H hHG hGH
        (x - representative F B p H hHG hGH fg) = 0 := hb
    rw [(classMap F B p H hHG hGH).map_sub, classMap_representative] at he
    exact (sub_eq_zero.mp he).symm

end D5.S3.VertexAlgebra.LatticeBRSTAbsoluteGroundCohomology
