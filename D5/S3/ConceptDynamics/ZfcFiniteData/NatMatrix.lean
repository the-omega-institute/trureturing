/- GID: D5/S3/ConceptDynamics/ZfcFiniteData/NatMatrix
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcFiniteData/NatMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: Vorspiel.Nat.Matrix for first-order set definition elimination. -/
module

public import Mathlib.Data.List.OfFn
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Matrix

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Nat/Matrix.lean, original lines 1-86.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace Nat

open Matrix

def natToVec : ℕ → (n : ℕ) → Option (Fin n → ℕ)
  | 0,     0     => some Matrix.vecEmpty
  | e + 1, n + 1 => Nat.natToVec e.unpair.2 n |>.map (e.unpair.1 :> ·)
  | _,     _     => none

variable {n : ℕ}

@[simp] lemma natToVec_vecToNat (v : Fin n → ℕ) : (vecToNat v).natToVec n = some v := by
  induction n
  · simp [*, Nat.natToVec, vecToNat, Matrix.empty_eq]
  case succ _ ih =>
    suffices v 0 :> v ∘ Fin.succ = v by
      simp only [vecToNat, foldr_succ, natToVec, unpair_pair, Option.map_eq_some_iff]
      use vecTail v
      simpa using! ih (vecTail v)
    exact funext (fun i ↦ i.cases (by simp) (by simp))

lemma lt_of_eq_natToVec {e : ℕ} {v : Fin n → ℕ} (h : e.natToVec n = some v) (i : Fin n) : v i < e := by
  induction' n with n ih generalizing e
  · exact i.elim0
  · cases' e with e
    · simp [natToVec] at h
    · simp only [natToVec, Option.map_eq_some_iff] at h
      rcases h with ⟨v, hnv, rfl⟩
      cases' i using Fin.cases with i
      · simp [Nat.lt_succ_iff, unpair_left_le]
      · simp only [cons_val_succ]
        exact lt_trans (ih hnv i) (Nat.lt_succ_iff.mpr <| unpair_right_le e)

end Nat

end
