import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth
open _root_.D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Two actual finite-count readouts over all pairs, including degenerate dimensions. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role _ z =>
    if role then count (cylinder z.1 z.2) else count (grid z.1 z.2))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∃ μ : ℝ, μ ∈ Set.Icc 1 2 ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, 3 ≤ N ∧ ∀ m n : ℕ, N ≤ m → N ≤ n →
      |growth (r.readout false () (m,n)) m n - μ| < ε ∧
      |growth (r.readout true () (m,n)) m n - μ| < ε

/-- This is only the exact reconstruction bridge, not a four-slot registration. -/
theorem source_bridge : JointGrowth ↔ arena.Law actual := Iff.rfl

end Reg.D5.S3.Combinatorics.Graph.Domination.MertensGridGrowth
