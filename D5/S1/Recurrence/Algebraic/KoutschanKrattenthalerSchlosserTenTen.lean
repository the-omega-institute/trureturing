/- GID: D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Prove the Koutschan-Krattenthaler-Schlosser determinant identities. -/

/- Formalization classification:
   proof_shape: claim: bind-only; consumer: KoutschanKrattenthalerSchlosserTenTen.result
   proof_shape: result: bind-only; consumer: none (settling result)
   escape_witness: none
   admission_basis: open-problem-resolution (#19236; Proved)
   Direct frozen dependencies: none (pinned Mathlib only).
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19547
-/

import D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG

namespace D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserTenTen

open D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserShiftedG

/-- Equation (10.10): `G_{3,0,3,3}(n) = (2/3) G_{0,1,−2,−4}(n+1) = −(1/672) G_{1,3,−2,−8}(n+1)
= (1/63) G_{5,4,3,−5}(n) = (4/1002001) G_{6,6,3,−9}(n) = −(8/5) G_{9,5,8,−2}(n−1)` for all `n ≥ 3`. -/
def claim : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    G 3 0 3 3 n = 2 / 3 * G 0 1 (-2) (-4) (n + 1) ∧
    2 / 3 * G 0 1 (-2) (-4) (n + 1) = -(1 / 672) * G 1 3 (-2) (-8) (n + 1) ∧
    -(1 / 672) * G 1 3 (-2) (-8) (n + 1) = 1 / 63 * G 5 4 3 (-5) n ∧
    1 / 63 * G 5 4 3 (-5) n = 4 / 1002001 * G 6 6 3 (-9) n ∧
    4 / 1002001 * G 6 6 3 (-9) n = -(8 / 5) * G 9 5 8 (-2) (n - 1)

theorem result : claim := by
  intro n hn
  have hp := p_shift_all (n-1)
  have hb := prop_B (n-1)
  have hc := link_BC (n+1) (by omega)
  have hd := link_PD n (by omega)
  have he := link_PE n (by omega)
  have hf := link_TF (n-1) (by omega)
  have hn1 : n-1+1=n := by omega
  have hn2 : n-1+2=n+1 := by exact Eq.symm ((fun {m k n} => Nat.add_left_inj.mpr) (id (Eq.symm hn1)))
  rw [hn1] at hp
  rw [hn2] at hb
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end D5.S1.Recurrence.Algebraic.KoutschanKrattenthalerSchlosserTenTen
