/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SpreadNonvacuity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SpreadNonvacuity
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Orthogonality/SevenDimensional/SpreadNonvacuity.claim; result=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SpreadNonvacuity.result; claim=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SpreadNonvacuity.claim
   digest: The original trace spread supplies actual inputs and an actual consumer of unique completion. -/
import D5.S3.Combinatorics.Orthogonality.SevenDimensional.ActualSpreadCompletion
/-! Nonvacuity of the full actual universal theorem. The explicit family
comes from the original F8 trace construction; the universal theorem is
proved separately and is not replaced by this one example. -/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.SevenDimensional.SpreadNonvacuity
open SevenBitGeometry
private def L : Fin 8 → Finset Vector := ![
  {3,12,15,48,51,60,63},
  {6,24,30,65,71,89,95},
  {17,36,53,66,83,102,119},
  {29,39,58,75,86,108,113},
  {9,18,27,96,105,114,123},
  {23,46,57,77,90,99,116},
  {10,33,43,68,78,101,111},
  {5,40,45,80,85,120,125}]
private theorem data : ∀ i, LagrangianData (L i) := by decide +kernel
private theorem intersect_zero : ∀ (i j : Fin 8), i ≠ j → ∀ v : Vector,
    v ∈ insert 0 (L i) → v ∈ insert 0 (L j) → v = 0 := by decide +kernel
private def U (i : Fin 8) : Submodule (ZMod 2) Coordinates :=
  SevenBitCapacity.actualLagrangian (L i) (data i)
private theorem dimensions (i : Fin 8) : Module.finrank (ZMod 2) (U i) = 3 :=
  (SevenBitCapacity.actual_lagrangian_geometry (L i) (data i)).1
private theorem isotropic (i : Fin 8) :
    ∀ u ∈ U i, ∀ v ∈ U i, dotProduct u v = 0 :=
  (SevenBitCapacity.actual_lagrangian_geometry (L i) (data i)).2
private theorem disjoint (i j : Fin 8) (hij : i ≠ j) : Disjoint (U i) (U j) := by
  apply Submodule.disjoint_def.mpr
  rintro w ⟨u,hu,huv⟩ ⟨v,hv,hvw⟩
  have h : u = v := bits_bijective.1 (huv.trans hvw.symm)
  subst v
  have hz := intersect_zero i j hij u hu hv
  simpa only [hz,bits_zero] using huv.symm
/-- The proposed absence of any actual input to the universal theorem. -/
def claim : Prop := ¬ ∃ V : Fin 8 → Submodule (ZMod 2) Coordinates,
  (∀ i, Module.finrank (ZMod 2) (V i) = 3) ∧
  (∀ i, ∀ u ∈ V i, ∀ v ∈ V i, dotProduct u v = 0) ∧
  (∀ i j, i ≠ j → Disjoint (V i) (V j))
/-- Actual full input families exist. -/
theorem result : ¬ claim := by
  intro hn
  exact hn ⟨U,dimensions,isotropic,disjoint⟩
#print axioms result
end D5.S3.Combinatorics.Orthogonality.SevenDimensional.SpreadNonvacuity
