/- GID: D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.claim; result=D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.result; claim=D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.claim
   digest: Refutes Conjectures 1 and 2 of Garcia Fernandez, Paletta and Retore, arXiv:2607.02093v1, on the minimum depth of open-boundary integrable quantum circuits: at N = 8 with two -kappa sites the configuration (6, 3) runs in 3 layers against the conjectured 4, and at N = 11 the configuration (8, 4) runs in 4 layers against the conjectured 5. -/

/-
proof_shape: result: bind-only
escape_witness: none; the conclusion follows from the definitions by two explicit layer maps
  checked by `decide`, two applications of `Nat.sInf_le` and `omega`
admission_basis: open-problem-resolution (issue #10379)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.OpenIntegrableCircuitDepthRefutation

/-- A gate of the open circuit: `U j` acts on the sites `j` and `j + 1`, `K1` on site `1`
(the right boundary matrix `K₁^R`), `KN` on site `N` (the left boundary matrix `K̃_N^L`). -/
inductive Gate
  | U (j : ℕ)
  | K1
  | KN
  deriving DecidableEq

/-- The sites a gate acts on, in a chain of `N` sites. -/
def Gate.sites (N : ℕ) : Gate → Finset ℕ
  | Gate.U j => {j, j + 1}
  | Gate.K1 => {1}
  | Gate.KN => {N}

/-- The circuit of Theorems 1 and 2 for the set `S` of sites carrying `-κ`, listed in time
order: the rightmost factor of the operator product acts first. -/
def circuit (N : ℕ) (S : Finset ℕ) : List Gate :=
  let rest := ((List.range' 1 (N - 1)).filter fun j => j ∉ S).reverse.map Gate.U
  if N ∈ S then
    rest ++ [Gate.K1] ++ ((List.range' 1 (N - 1)).filter fun j => j ∈ S).map Gate.U ++ [Gate.KN]
  else
    [Gate.KN] ++ rest ++ [Gate.K1] ++ ((List.range' 1 N).filter fun j => j ∈ S).map Gate.U

/-- The gates `w` fit in `L` layers: a layer map below `L` under which two gates sharing a site
keep their time order. -/
def RunsIn (N : ℕ) (w : List Gate) (L : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < w.length, f i < L) ∧
    ∀ j < w.length, ∀ i < j,
      ((w.getD i Gate.K1).sites N ∩ (w.getD j Gate.K1).sites N).Nonempty → f i < f j

/-- The depth of a circuit: the least number of layers it fits in. -/
noncomputable def depth (N : ℕ) (w : List Gate) : ℕ := sInf {L | RunsIn N w L}

/-- The minimum depth over the configurations with `κ` sites carrying `-κ`. -/
noncomputable def minDepth (N κ : ℕ) : ℕ :=
  sInf {d | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ S.card = κ ∧ depth N (circuit N S) = d}

/-- Conjecture 1 of arXiv:2607.02093v1. -/
def conjectureOne : Prop :=
  ∀ N κ : ℕ, Odd N → 0 < κ → κ ≤ (N - 1) / 2 → minDepth N κ = (N + 3) / 2 - κ

/-- Conjecture 2 of arXiv:2607.02093v1. -/
def conjectureTwo : Prop :=
  ∀ N κ : ℕ, Even N → 0 < κ → κ ≤ N / 2 → minDepth N κ = (N + 4) / 2 - κ

/-- Conjectures 1 and 2 of arXiv:2607.02093v1; the refutation shows that both fail. -/
def claim : Prop := conjectureOne ∨ conjectureTwo

/-- Both conjectures fail: at `N = 8`, `κ₋ = 2` the configuration `(6, 3)` runs in three layers,
and at `N = 11`, `κ₋ = 2` the configuration `(8, 4)` runs in four. -/
theorem result : ¬ claim := by
  have runs8 : RunsIn 8 (circuit 8 {3, 6}) 3 :=
    ⟨fun i => [0, 1, 0, 1, 0, 1, 2, 2, 2].getD i 0, by decide, by decide⟩
  have runs11 : RunsIn 11 (circuit 11 {4, 8}) 4 :=
    ⟨fun i => [0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 3, 3].getD i 0, by decide, by decide⟩
  have min8 : minDepth 8 2 ≤ 3 :=
    le_trans (Nat.sInf_le ⟨{3, 6}, by decide, by decide, rfl⟩) (Nat.sInf_le runs8)
  have min11 : minDepth 11 2 ≤ 4 :=
    le_trans (Nat.sInf_le ⟨{4, 8}, by decide, by decide, rfl⟩) (Nat.sInf_le runs11)
  rintro (h | h)
  · have := h 11 2 ⟨5, rfl⟩ (by omega) (by omega)
    omega
  · have := h 8 2 ⟨4, rfl⟩ (by omega) (by omega)
    omega

end D5.S3.Quantum.Dynamics.OpenIntegrableCircuitDepthRefutation
