import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut

/-! Exact source reconstructions for the whole-block rounding and scaling laws.
Whole-family intervention and source-selection certificates remain unresolved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut

open _root_.D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Classical


structure SourceData (n : ℕ) where
  graph : SimpleGraph (Fin n)
  decAdj : DecidableRel graph.Adj

abbrev scalingScope := type_of% (@maxCut_blowup)
abbrev roundingScope := type_of% (@exists_block_cut)

abbrev scalingSignature : DependentFamily.Signature where
  Params := ℕ × ℕ
  State p := SourceData p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def scalingActual : DependentFamily.Realization scalingSignature :=
  DependentFamily.realize scalingSignature
    (fun _ p d => by
      letI := d.decAdj
      exact _root_.D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation.maxCut (blowup d.graph p.2))
    (fun e => nomatch e)

def scalingArena : DependentFamily.Arena where
  signature := scalingSignature
  Law R := ∀ {n s : ℕ} (H : SimpleGraph (Fin n)) [d : DecidableRel H.Adj],
    1 ≤ s → R.readout () (n,s) ⟨H,d⟩ = s^2 * _root_.D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation.maxCut H

theorem scaling_source_bridge : scalingScope ↔ scalingArena.Law scalingActual := by
  constructor <;> intro h <;> exact @h

theorem scaling_actual_positive : scalingArena.Law scalingActual :=
  scaling_source_bridge.mp (@maxCut_blowup)

/-- No complete four-slot registration is asserted without the remaining evidence. -/
def scalingCertificate : Option (DependentFamily.Registration scalingArena scalingScope) := none

abbrev roundingSignature : DependentFamily.Signature where
  Params := ℕ × ℕ
  State p := SourceData p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (Fin (p.1*p.2)) → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def roundingActual : DependentFamily.Realization roundingSignature :=
  DependentFamily.realize roundingSignature
    (fun _ p d S => by
      letI := d.decAdj
      exact ((blowup d.graph p.2).edgeFinset.filter (_root_.D5.S3.Combinatorics.Graph.TokenGraph.CutBoundRefutation.crosses S)).card)
    (fun e => nomatch e)

def roundingArena : DependentFamily.Arena where
  signature := roundingSignature
  Law R := ∀ {n s : ℕ} (H : SimpleGraph (Fin n)) [d : DecidableRel H.Adj],
    1 ≤ s → ∀ S : Finset (Fin (n*s)), ∃ T : Finset (Fin n),
      R.readout () (n,s) ⟨H,d⟩ S ≤ R.readout () (n,s) ⟨H,d⟩ (liftCut s T)

theorem rounding_source_bridge : roundingScope ↔ roundingArena.Law roundingActual := by
  constructor <;> intro h <;> exact @h

theorem rounding_actual_positive : roundingArena.Law roundingActual :=
  rounding_source_bridge.mp (@exists_block_cut)

def roundingCertificate : Option (DependentFamily.Registration roundingArena roundingScope) := none

#print axioms scaling_source_bridge
#print axioms scaling_actual_positive
#print axioms rounding_source_bridge
#print axioms rounding_actual_positive

end Reg.D5.S3.Combinatorics.Graph.TokenGraph.BlowupMaxCut
