/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldChiralZeroModeConnection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldChiralZeroModeConnection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The chiral zero-mode anticommutator on the native orbifold relative shell. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
import D5.S3.VertexAlgebra.Lattice.LatticeOriginalAbsoluteZeroCohomology
import Mathlib.LinearAlgebra.Matrix.ToLin
import Batteries.Tactic.OpenPrivate

/-! The chiral zero-mode connection on the actual zero-momentum relative shell. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldChiralZeroModeConnection

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open BcGhostBRST (R)
open OriginalOrbifoldCriticalMatter (Matter State Q matterDatum hyperbolicData)
open OriginalOrbifoldRelativeMassShell (relativeMassShell)
open OriginalOrbifoldRelativeNull
  (ShellIndex bottom middle top shellBasis shellBasis_coe shellVector)

open private shellVector_bottom shellVector_middle shellVector_top from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldRelativeNull
open private R0_empty R0_down R0_top from
  D5.S3.VertexAlgebra.Lattice.LatticeOriginalAbsoluteZeroCohomology

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev c0 : Module.End ℂ State := VirasoroBRST.ghostC matterDatum 0

/-- The anticommutator of the original charge with the original c₀. -/
abbrev chiralAnticommutator : Module.End ℂ State := Q * c0 + c0 * Q

private theorem chiralAnticommutator_tmul (v : Matter) (w : Fock) :
    chiralAnticommutator (v ⊗ₜ[ℂ] w) = v ⊗ₜ[ℂ] R 0 w := by
  change (VirasoroBRST.Q matterDatum * VirasoroBRST.ghostC matterDatum 0 +
    VirasoroBRST.ghostC matterDatum 0 * VirasoroBRST.Q matterDatum) (v ⊗ₜ[ℂ] w) = _
  rw [VirasoroBRST.Q_ward_c]
  simp only [VirasoroBRST.ghostR, TensorProduct.map_tmul, LinearMap.id_apply]

theorem chiralAnticommutator_bottom :
    chiralAnticommutator (shellVector 0 bottom) = (2 : ℂ) • shellVector 0 top := by
  rw [shellVector_bottom, shellVector_top, chiralAnticommutator_tmul, R0_empty,
    TensorProduct.tmul_smul]

theorem chiralAnticommutator_middle (i : Fin 2) :
    chiralAnticommutator (shellVector 0 (middle i)) = 0 := by
  rw [shellVector_middle, chiralAnticommutator_tmul, R0_down, TensorProduct.tmul_zero]

theorem chiralAnticommutator_top :
    chiralAnticommutator (shellVector 0 top) = 0 := by
  rw [shellVector_top, chiralAnticommutator_tmul, R0_top, TensorProduct.tmul_zero]

private abbrev zeroShell : Submodule ℂ State := relativeMassShell 0
abbrev ZeroShell := ↥zeroShell

abbrev zeroBasis : Module.Basis ShellIndex ℂ ZeroShell :=
  shellBasis 0 (LatticePositiveEnergy.chargeEnergy_zero hyperbolicData)

private def raise : Module.End ℂ ZeroShell :=
  zeroBasis.constr ℂ (fun i => if i = bottom then zeroBasis top else 0)

private theorem raise_basis (i : ShellIndex) :
    raise (zeroBasis i) = if i = bottom then zeroBasis top else 0 :=
  zeroBasis.constr_basis ℂ _ i

theorem chiralAnticommutator_restrict :
    chiralAnticommutator.comp zeroShell.subtype = zeroShell.subtype.comp ((2 : ℂ) • raise) := by
  apply zeroBasis.ext
  intro i
  simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.smul_apply,
    Submodule.coe_smul, raise_basis]
  rw [show (zeroBasis i : State) = shellVector 0 i from shellBasis_coe 0 _ i]
  rcases i with ⟨⟩ | (i | ⟨⟩)
  · simpa [bottom, shellBasis_coe] using chiralAnticommutator_bottom
  · simpa [bottom, middle] using chiralAnticommutator_middle i
  · simpa [bottom, top] using chiralAnticommutator_top

/-- The anticommutator on the native zero-momentum shell in its fixed basis. -/
def chiralConnectionMatrix : Matrix ShellIndex ShellIndex ℂ :=
  LinearMap.toMatrix zeroBasis zeroBasis ((2 : ℂ) • raise)

theorem chiralConnectionMatrix_entry (i j : ShellIndex) :
    chiralConnectionMatrix i j = if j = bottom ∧ top = i then 2 else 0 := by
  classical
  rw [chiralConnectionMatrix, LinearMap.toMatrix_apply, LinearMap.smul_apply, raise_basis]
  by_cases hj : j = bottom
  · rw [ite_eq_left hj, map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply]
    by_cases hi : top = i <;>
      simp only [hj, hi, true_and, ite_true, ite_false, smul_eq_mul, mul_one, mul_zero]
  · have hs : (2 : ℂ) • (0 : ZeroShell) = 0 := smul_zero _
    have hj' : ¬ (j = bottom ∧ top = i) := fun h => hj h.1
    rw [ite_eq_right hj, hs, zeroBasis.repr.map_zero, Finsupp.zero_apply, ite_eq_right hj']

#print axioms chiralAnticommutator_bottom
#print axioms chiralAnticommutator_middle
#print axioms chiralAnticommutator_top
#print axioms chiralAnticommutator_restrict
#print axioms chiralConnectionMatrix_entry

end D5.S3.VertexAlgebra.OriginalOrbifoldChiralZeroModeConnection
