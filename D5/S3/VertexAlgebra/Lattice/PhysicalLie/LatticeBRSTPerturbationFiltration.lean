/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration
   mirror-E: none(waiver:symbolic-original-q-fixed-energy-filtration)
   anchors: []
   utility: none
   digest: Fixed integral charge, total energy and signed filtration on the original lattice BRST carrier. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTSquare
import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
import Batteries.Tactic.OpenPrivate

/-!
Fixed integral charge and total energy for the literal original-Q carrier.

The signed filtration is the CURRENT `LatticeBRSTModeFiltration.degree`:
`exponentDegree + BcGhostCharge.charge - 1`.  The current full-original
raising theorem supplies the strict step for `(Q-d0)` and `h*(Q-d0)` on the
same `actualBasis`; this file only supplies the fixed-energy sector and its
coefficient characterization. The signed-window and preservation auxiliaries
are preserved with their substantive finite-transfer consumer.  The two exceptional zero-mode
occupations `{1}` and `{1,3}` remain in the window.

Source attribution: immutable supplier input
f8dc18b8c93143d2b804315536f93bb8b2d2eef5ea3ded35d6e4328687cc12a7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge
open LatticeBRSTModeFiltration
open LatticeBRSTFullOriginalRaising
open private basis_expansion chargeProject_basis fixed_charge_coefficients from
  D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
open private charge_sum from D5.S3.Quantum.Fermionic.BcGhostCharge

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)

def groundEnergy (beta : Charge D) : ℂ := (bilinear D beta beta : ℂ) / 2

def totalL0 (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) : Module.End ℂ (State D) :=
  LatticeMatterGhostCoupling.matterMode D H 0 + LatticeMatterGhostCoupling.ghostVirasoro D 0

def oscillatorLevel (m : Exponents t) : ℕ := Finsupp.weight frequencyWeight m

/-- Integer level measured above the actual c(1) vacuum, on every raw ket. -/
def indexLevel (i : StateIndex D t) : ℤ := oscillatorLevel i.1.2 + BcGhostRelativeEnergy.relativeEnergy i.2

theorem totalL0_basis (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : StateIndex D t) :
    totalL0 H (actualBasis F B i) =
      (groundEnergy i.1.1 + (indexLevel i : ℂ) - 1) • actualBasis F B i := by
  rcases i with ⟨⟨beta,m⟩,S⟩
  have hm : MvPolynomial.IsWeightedHomogeneous (oscillatorWeight D)
      ((F.coordinateEquiv B).symm (MvPolynomial.monomial m 1)) (oscillatorLevel m) := by
    apply (F.frequency_grading B _ _).mp
    rw [AlgEquiv.apply_symm_apply]
    apply MvPolynomial.isWeightedHomogeneous_monomial
    rfl
  have he := sugawaraMode_weighted_homogeneous D H hHG hGH beta _ _ hm
  rw [actualBasis_apply]
  simp only [totalL0, LinearMap.add_apply, LatticeMatterGhostCoupling.matterMode, LatticeMatterGhostCoupling.ghostVirasoro,
    sector, TensorProduct.map_tmul, LinearMap.id_apply, he, BcGhostRelativeEnergy.L_zero_ket,
    TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  have hs : ((oscillatorLevel m : ℂ) + (bilinear D beta beta : ℂ) / 2) +
      (BcGhostRelativeEnergy.energy S : ℂ) =
      groundEnergy beta +
        (indexLevel (⟨⟨beta, m⟩, S⟩ : StateIndex D t) : ℂ) - 1 := by
    simp only [groundEnergy, indexLevel, BcGhostRelativeEnergy.relativeEnergy,
      Int.cast_add, Int.cast_natCast, Int.cast_sub, Int.cast_one]
    ring
  rw [← TensorProduct.add_tmul, ← add_smul, hs]

theorem totalL0_diagonal (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    totalL0 (D := D) H = diagonal (actualBasis F B)
      (fun i => groundEnergy i.1.1 + (indexLevel i : ℂ) - 1) := by
  apply (actualBasis F B).ext
  intro i
  rw [totalL0_basis F B H hHG hGH, diagonal_basis]

/-- The literal all-state charge/total-energy sector, at any integer level. -/
def fixedSector (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (beta : Charge D) (level : ℤ) : Submodule ℂ (State D) where
  carrier := {v | chargeProject beta v = v ∧
    totalL0 H v = (groundEnergy beta + (level : ℂ) - 1) • v}
  zero_mem' := by
    constructor <;> simp only [map_zero, smul_zero]
  add_mem' := by
    rintro v w ⟨hv,hvE⟩ ⟨hw,hwE⟩
    constructor
    · rw [map_add, hv, hw]
    · rw [map_add, hvE, hwE, smul_add]
  smul_mem' := by
    rintro a v ⟨hv,hvE⟩
    constructor
    · rw [map_smul, hv]
    · rw [map_smul, hvE, smul_comm]

theorem mem_fixedSector_iff (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (beta : Charge D) (level : ℤ) (v : State D) :
    v ∈ fixedSector H beta level ↔ ∀ i : StateIndex D t,
      (actualBasis F B).repr v i ≠ 0 → i.1.1 = beta ∧ indexLevel i = level := by
  constructor
  · rintro ⟨hc,he⟩ i hi
    have hp : i.1.1 = beta := by
      by_contra hn
      exact hi ((fixed_charge_coefficients F B beta v).mp hc i hn)
    refine ⟨hp, ?_⟩
    have eq := congrArg (fun w => (actualBasis F B).repr w i) he
    rw [totalL0_diagonal F B H hHG hGH, diagonal_coefficient] at eq
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, hp] at eq
    have e := mul_right_cancel₀ hi eq
    have e' : (indexLevel i : ℂ) = (level : ℂ) := by linear_combination e
    exact_mod_cast e'
  · intro hs
    constructor
    · apply (fixed_charge_coefficients F B beta v).mpr
      intro i hp
      by_contra hn
      exact hp (hs i hn).1
    · apply (actualBasis F B).repr.injective
      ext i
      rw [totalL0_diagonal F B H hHG hGH, diagonal_coefficient]
      simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
      by_cases hz : (actualBasis F B).repr v i = 0
      · simp [hz]
      · obtain ⟨hp,he⟩ := hs i hz
        rw [hp, he]

def signedFiltration (beta : Charge D) (level lower : ℤ) : Submodule ℂ (State D) :=
  Submodule.span ℂ (actualBasis F B '' {i : StateIndex D t |
    i.1.1 = beta ∧ indexLevel i = level ∧ lower ≤ degree i})

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
