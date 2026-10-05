/- GID: D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DyckValleys/ValleyBargraphBijection
   mirror-E: none(waiver:mu-welker-conjecture-three-nine-proof-core)
   anchors: [D5/S3/Combinatorics/DyckValleys/ValleyBargraphDefs]
   utility: none
   digest: Contracting valleys and expanding bargraph profile horizontal edges are inverse list operations. -/

import D5.S3.Combinatorics.DyckValleys.ValleyBargraphDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DyckValleys.ValleyBargraphBijection

open DyckStep

/-! The boundary of a bargraph is written with `none` for a horizontal edge.
    The two elementary operations below are the algebraic core of the
    Mu--Welker bijection: a horizontal edge expands to the valley `DU`, and
    contraction replaces every valley by one horizontal edge. -/

abbrev ProfileStep := Option DyckStep

def expandStep : ProfileStep → List DyckStep
  | none => [D, U]
  | some s => [s]

def expand : List ProfileStep → List DyckStep
  | [] => []
  | a :: q => expandStep a ++ expand q

def contract : List DyckStep → List ProfileStep
  | [] => []
  | D :: U :: q => none :: contract q
  | a :: q => some a :: contract q

def profileHasNoDU : List ProfileStep → Prop
  | [] => True
  | a :: q =>
      (match q with
      | [] => True
      | b :: _ => ¬ (a = some D ∧ b = some U)) ∧ profileHasNoDU q

@[simp] theorem expand_nil : expand ([] : List ProfileStep) = [] := rfl
@[simp] theorem contract_nil : contract ([] : List DyckStep) = [] := rfl

theorem contract_expand (q : List ProfileStep) (h : profileHasNoDU q) :
    contract (expand q) = q := by
  induction q with
  | nil => rfl
  | cons a q ih =>
      cases a with
      | none =>
          simp_all [expand, expandStep, contract, profileHasNoDU]
      | some s =>
          cases s with
          | U =>
              cases q <;> simp_all [expand, expandStep, contract, profileHasNoDU]
          | D =>
              cases q with
              | nil => simp [expand, expandStep, contract]
              | cons b q =>
                  cases b <;> simp_all [expand, expandStep, contract, profileHasNoDU]

theorem expand_contract : ∀ q : List DyckStep, expand (contract q) = q
  | [] => rfl
  | U :: q => by simp [contract, expand, expandStep, expand_contract q]
  | D :: [] => by simp [contract, expand, expandStep]
  | D :: U :: q => by simp [contract, expand, expandStep, expand_contract q]
  | D :: D :: q => by simp [contract, expand, expandStep, expand_contract (D :: q)]

def valleyCount (q : List DyckStep) : ℕ := (contract q).count none

/-- The usual adjacent-pair definition of a valley, on raw words. -/
def adjacentValleys : List DyckStep → ℕ
  | [] => 0
  | _ :: [] => 0
  | a :: b :: q => (if a = D ∧ b = U then 1 else 0) + adjacentValleys (b :: q)

theorem valleyCount_eq_adjacentValleys (q : List DyckStep) :
    valleyCount q = adjacentValleys q := by
  induction q with
  | nil => rfl
  | cons a q ih =>
      cases q with
      | nil => simp [valleyCount, adjacentValleys, contract]
      | cons b q =>
          cases a with
          | U =>
              cases b with
              | U => simpa [valleyCount, adjacentValleys, contract] using ih
              | D => simpa [valleyCount, adjacentValleys, contract] using ih
          | D =>
              cases b with
              | U =>
                  have hi : (contract q).count none = adjacentValleys (U :: q) := by
                    simpa [valleyCount, contract] using ih
                  simp [valleyCount, adjacentValleys, contract, hi]
                  omega
              | D => simpa [valleyCount, adjacentValleys, contract] using ih

theorem adjacentValleys_eq_zipCount (q : List DyckStep) :
    adjacentValleys q = (q.zip q.tail).count (D, U) := by
  induction q with
  | nil => rfl
  | cons a q ih =>
      cases q with
      | nil => rfl
      | cons b q =>
          cases a <;> cases b <;>
            simp [adjacentValleys, ih, Nat.add_comm]

theorem sourceValleys_eq_valleyCount (p : DyckWord) :
    ValleyBargraphDefs.valleys p = valleyCount p := by
  rw [ValleyBargraphDefs.valleys, valleyCount_eq_adjacentValleys,
    adjacentValleys_eq_zipCount]

theorem valleyCount_expand (q : List ProfileStep)
    (h : profileHasNoDU q) :
    valleyCount (expand q) = q.count none := by
  rw [valleyCount, contract_expand q h]

end D5.S3.Combinatorics.DyckValleys.ValleyBargraphBijection
