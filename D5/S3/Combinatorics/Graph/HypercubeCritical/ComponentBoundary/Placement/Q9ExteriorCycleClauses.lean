import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorTransport
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitCover
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCNF

/-! Read a closed exterior walk with nonzero coordinate gain as a clause
excluding the joint occurrence of all its two-neighbor rows. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9ExteriorCycleClauses

open Finset
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open BalancedCriticalSpectrum (Q)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9ExteriorTransport (Walk Exponent axis GainConsistent)
open Q9SharedContactCNF (Axis Word Variable pos neg)
open Q9FiveAxisOrbitCover (satisfies_of_falsified)
open private adjacentWord adjacentWord_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactCNF

private abbrev occ := Variable.occupied

/-- An oriented exterior row connects its selected neighbors on the entry and exit axes. -/
structure Row where
  mid : Word
  enter : Axis
  exit : Axis

private def Row.first (r : Row) : Word := adjacentWord r.mid r.enter
private def Row.last (r : Row) : Word := adjacentWord r.mid r.exit
private def Row.gain (r : Row) : Exponent := axis r.enter - axis r.exit

private def Row.outsideLiteral (s : Bool) (r : Row) (i : Axis) : Sat.Literal :=
  if i = r.enter ∨ i = r.exit then neg (occ s (adjacentWord r.mid i))
  else pos (occ s (adjacentWord r.mid i))

/-- Falsifying all the literals requires an exterior midpoint with exactly
the two named directions. -/
def Row.literals (s : Bool) (r : Row) : List Sat.Literal :=
  pos (occ s r.mid) :: (List.finRange 9).map (r.outsideLiteral s)

/-- Follow the oriented rows, rejecting a mismatched endpoint or a repeated axis. -/
def follow (start : Word) (gain : Exponent) : List Row → Option (Word × Exponent)
  | [] => some (start, gain)
  | row :: rows =>
    if row.first = start ∧ row.enter ≠ row.exit then
      follow row.last (gain + row.gain) rows
    else none

private theorem follow_walk {C : Finset (Q 9)} {root : Q 9} {rows : List Row}
    (hrows : ∀ r ∈ rows, cubeBitVec 9 r.mid ∉ C ∧
      directions C (cubeBitVec 9 r.mid) = {r.enter, r.exit})
    {start finish : Word} {gain total : Exponent}
    (initial : Walk C root (cubeBitVec 9 start) gain)
    (hfollow : follow start gain rows = some (finish, total)) :
    Walk C root (cubeBitVec 9 finish) total := by
  induction rows generalizing start gain with
  | nil =>
    have h := Option.some.inj hfollow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact initial
  | cons r rows ih =>
    by_cases hstep : r.first = start ∧ r.enter ≠ r.exit
    · rw [follow, if_pos hstep] at hfollow
      have hr := hrows r (List.mem_cons_self)
      have hb := initial
      rw [← hstep.1, Row.first, adjacentWord_spec] at hb
      have hwalk : Walk C root (cubeBitVec 9 r.last) (gain + r.gain) := by
        rw [Row.last, adjacentWord_spec]
        exact Walk.step hb hstep.2 hr.1 hr.2
      exact ih (fun v hv => hrows v (List.mem_cons_of_mem _ hv)) hwalk hfollow
    · simp [follow, hstep] at hfollow

open Classical in
/-- Every cycle clause with a nonzero checked gain is satisfied by the actual support valuation. -/
theorem cycleClause (S : Bool → Finset (Q 9)) (s : Bool)
    (hC : GainConsistent (S s))
    (row : Row) (rest : List Row) (gain : Exponent) (hne : gain ≠ 0)
    (hfollow : follow row.first 0 (row :: rest) = some (row.first, gain))
    (c : List Sat.Literal)
    (hcover : ∀ r ∈ row :: rest, ∀ l ∈ r.literals s, l ∈ c) :
    (Q9TightDistanceTwoCNF.valuation S).satisfies c := by
  apply satisfies_of_falsified
  intro hall
  have hrows (r : Row) (hmem : r ∈ row :: rest) :
      cubeBitVec 9 r.mid ∉ S s ∧ directions (S s) (cubeBitVec 9 r.mid) = {r.enter, r.exit} := by
    refine ⟨?_, ?_⟩
    · have hn := hall (pos (occ s r.mid)) (hcover r hmem _ (List.mem_cons_self))
      exact fun hx => hn ((Q9TightDistanceTwoCNF.valuation_occupied S s r.mid).mpr hx)
    · ext i
      have h := hall (r.outsideLiteral s i) (hcover r hmem _
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)))
      rw [mem_directions, ← adjacentWord_spec]
      by_cases haxis : i = r.enter ∨ i = r.exit
      · rw [Row.outsideLiteral, if_pos haxis] at h
        exact iff_of_true ((Q9TightDistanceTwoCNF.valuation_occupied S s _).mp h) (by simp [haxis])
      · rw [Row.outsideLiteral, if_neg haxis] at h
        exact iff_of_false
          (fun hx => h ((Q9TightDistanceTwoCNF.valuation_occupied S s _).mpr hx)) (by simp [haxis])
  have hstart : cubeBitVec 9 row.first ∈ S s := by
    rw [Row.first, adjacentWord_spec, ← mem_directions, (hrows row List.mem_cons_self).2]
    simp
  have hwalk := follow_walk hrows (Walk.nil (cubeBitVec 9 row.first)) hfollow
  exact hne (hC hstart hwalk (Walk.nil _))

#print axioms cycleClause

end Q9ExteriorCycleClauses
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
