/- GID: D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prove the Koutschan-Krattenthaler-Schlosser determinant identities. -/

/- Formalization classification:
   proof_shape: claim: bind-only; consumer: KoutschanKrattenthalerSchlosserTenEleven.result
   proof_shape: result: bind-only; consumer: none (settling result)
   escape_witness: none
   admission_basis: open-problem-resolution (#19237; Proved)
   Direct frozen dependencies: none (pinned Mathlib only).
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19547
-/

import D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG

namespace D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserTenEleven

open D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG

/-- Equation (10.11): `G_{1,1,0,−2}(n) = −(1/49) G_{2,3,0,−6}(n) = −(2/7) G_{6,4,5,−3}(n−1)
= −(4/5577) G_{7,6,5,−7}(n−1)` for all `n ≥ 3`. -/
def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    G 1 1 0 (-2) n = -(1 / 49) * G 2 3 0 (-6) n ∧
    -(1 / 49) * G 2 3 0 (-6) n = -(2 / 7) * G 6 4 5 (-3) (n - 1) ∧
    -(2 / 7) * G 6 4 5 (-3) (n - 1) = -(4 / 5577) * G 7 6 5 (-7) (n - 1)

theorem result : claim := by
  intro n hn
  have hh := prop_H (n-1)
  have hi := link_HI n (by omega)
  have hj := link_VJ (n-1) (by omega)
  have hk := link_VK (n-1) (by omega)
  have hn1 : n-1+1=n := by omega
  rw [hn1] at hh
  constructor
  · exact hi
  constructor
  · linarith
  · linarith

end D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserTenEleven
