/- GID: D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Ordered noncrossing matchings and boundary labels. -/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CupCapBridgeProposal

def insertPort (j k : ℕ) : ℕ := if k < j then k else k + 2

/-- The frontier pairing, before any label model is chosen. -/
structure NCMatching (m : ℕ) where
  partner : Equiv.Perm (Fin m)
  involutive : Function.Involutive partner
  noFixed : ∀ k, partner k ≠ k
  noncrossing : ∀ a b, a < b → b < partner a → partner a < partner b → False

/-- Both side equations are symmetric under exchanging the paired endpoints. -/
def Compatible {L : Type*} {m : ℕ} (M : NCMatching m) (x : Fin (m + 1) → L) : Prop :=
  ∀ a : Fin m,
    x a.castSucc = x (M.partner a).succ ∧
    x a.succ = x (M.partner a).castSucc

def boundaryPotential {L : Type*} {m : ℕ} (q : L → ℝ)
    (M : NCMatching m) (x : Fin (m + 1) → L) : ℝ := by
  classical
  exact if Compatible M x then
    ∏ a : Fin m, if a < M.partner a then q (x a.succ) / q (x a.castSucc) else 1
  else 0

/-- The old index of a surviving shorter endpoint. -/
def skipPair {m : ℕ} (j : Fin (m + 1)) (k : Fin m) : Fin (m + 2) :=
  ⟨insertPort j.val k.val, by
    dsimp [insertPort]
    split_ifs <;> omega⟩

/-- Reconnect the two partners at the consumed endpoints, in old coordinates.
On surviving endpoints this is the partner map to transport back to Fin m. -/
def reconnectPartner {m : ℕ} (M : NCMatching (m + 2))
    (j : Fin (m + 1)) (k : Fin (m + 2)) : Fin (m + 2) :=
  if M.partner k = j.castSucc then M.partner j.succ
  else if M.partner k = j.succ then M.partner j.castSucc
  else M.partner k

/-- Insert the literal a,b,a detour in the shorter gap sequence. -/
def detourLabels {L : Type*} {m : ℕ} (j : Fin (m + 1))
    (x : Fin (m + 1) → L) (b : L) : Fin (m + 3) → L :=
  fun k =>
    if h₀ : k.val ≤ j.val then x ⟨k.val, by omega⟩
    else if k.val = j.val + 1 then b
    else x ⟨k.val - 2, by omega⟩

inductive CapCase where
  | close | siblings | leftNested | rightNested
  deriving DecidableEq

/-- Classification is executable; proving its four precise order descriptions
and constructing the smaller NCMatching remain part of CapFiberGoal. -/
def classifyCap {m : ℕ} (M : NCMatching (m + 2)) (j : Fin (m + 1)) : CapCase :=
  if M.partner j.castSucc = j.succ then .close
  else if (M.partner j.castSucc).val < j.val then
    if (M.partner j.succ).val < j.val then .rightNested else .siblings
  else .leftNested

end CupCapBridgeProposal
