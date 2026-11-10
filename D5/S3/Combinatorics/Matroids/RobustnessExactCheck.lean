import D5.S3.Combinatorics.Matroids.LocalSearchRobustness
import Lean
open Set Matroid
open scoped BigOperators
open D5.S3.Combinatorics.Matroids.LocalSearchRobustness
open D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
universe u
example {E : Type u} [Finite E] (M : Matroid E) (w : E → ℝ) (k : ℕ)
    (B : Fin (k+1) → Set E) (hB : ∀ i, M.IsBase (B i))
    (hs : ∀ i : Fin k, (B i.succ \ B i.castSucc).ncard ≤ 1) :
    (∀ i : Fin k, 0 ≤ neighborhoodMax M w ⟨B i.castSucc,hB _⟩ 1 - baseWeight w (B i.succ)) ∧
    ∀ C, M.IsBase C → (C \ B 0).ncard ≤ k →
      baseWeight w C ≤ baseWeight w (B (Fin.last k)) +
        ∑ i : Fin k, (neighborhoodMax M w ⟨B i.castSucc,hB _⟩ 1 - baseWeight w (B i.succ)) := by
  exact local_search_robustness M w k (fun i => ⟨B i,hB i⟩) hs

example (k : ℕ) :
    let M : Matroid Bool := loopyOn {true}
    let w : Bool → ℝ := fun b => if b then -3 else 2
    let B : Fin (k+1) → {D : Set Bool // M.IsBase D} := fun _ => ⟨∅, by simp [M]⟩
    (∀ i : Fin k, 0 ≤ localError M w (B i.castSucc) (B i.succ)) ∧
    ∀ C, M.IsBase C → (C \ (B 0).val).ncard ≤ k →
      baseWeight w C ≤ baseWeight w (B (Fin.last k)).val +
        ∑ i : Fin k, localError M w (B i.castSucc) (B i.succ) := by
  dsimp
  exact local_search_robustness _ _ k _ (by intro i; simp)

open Lean Elab Command
private partial def printWeightPaths (e : Expr) (p : List String) : CommandElabM Unit := do
  if e.isAppOfArity `D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation.baseWeight 3 then
    logInfo m!"WEIGHT_PATH {p}: {e}"
  match e with
  | .forallE _ d b _ => printWeightPaths d (p ++ ["domain"]); printWeightPaths b (p ++ ["body"])
  | .lam _ d b _ => printWeightPaths d (p ++ ["domain"]); printWeightPaths b (p ++ ["body"])
  | .app f a => printWeightPaths f (p ++ ["fn"]); printWeightPaths a (p ++ ["arg"])
  | _ => pure ()
run_cmd do
  for n in [`D5.S3.Combinatorics.Matroids.LocalSearchRobustness.neighborhood_comparison,
      `D5.S3.Combinatorics.Matroids.LocalSearchRobustness.local_search_robustness] do
    logInfo m!"SOURCE {n}"
    printWeightPaths (← getConstInfo n).type []
#print axioms neighborhood_comparison
#print axioms local_search_robustness
