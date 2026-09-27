/- GID: D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.claim; result=D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.result; claim=D5/S0/Certificates/Games/CrimRectairSquareBoundaryRefutation.claim
   digest: Refutes printed CRIM Conjecture 2 at the boundary r=1. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8628)
   Direct frozen dependencies: D5/S0/Certificates/Games/CrimGrundyRefutation
     (grundy, rectair, moves, mex). -/

import D5.S0.Certificates.Games.CrimGrundyRefutation

open D5.S0.Certificates.Games.CrimGrundyRefutation

namespace D5.S0.Certificates.Games.CrimRectairSquareBoundaryRefutation

/-- Conjecture 2 of arXiv:2606.16828v1: the printed Sprague-Grundy formula
for the square rectairs `R^k_{r,r}`. -/
def claim : Prop := ∀ r k : ℕ, k < r →
  grundy (rectair r r k) =
    if r % 2 = 0 ∨ k < r - 1 then 0 else if r = 3 ∨ r = 5 then 1 else 2

example : moves [1] = [[], []] := by decide
example : grundy [] = 0 := by
  rw [grundy, WellFounded.fix_eq]
  decide
example : grundy [2, 1] = 0 := by decide +kernel
example : rectair 3 3 2 = [3, 2, 1] := by decide

/-- Conjecture 2 is false at its boundary `r = 1, k = 0`: `G([1]) = 1`. -/
theorem result : ¬ claim := by
  intro h
  have grundy_eq (p : List ℕ) :
      grundy p = mex ((moves p).map grundy).toFinset := by
    rw [grundy, WellFounded.fix_eq]
    simp
  have empty : grundy [] = 0 := by
    rw [grundy_eq]
    decide
  have predicted : grundy (rectair 1 1 0) = 2 := by
    simpa using h 1 0 (by decide)
  have actual : grundy (rectair 1 1 0) = 1 := by
    change grundy [1] = 1
    rw [grundy_eq]
    rw [show moves [1] = [[], []] by decide]
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      empty]
    decide +kernel
  omega

#print axioms claim
#print axioms result

end D5.S0.Certificates.Games.CrimRectairSquareBoundaryRefutation
