/- GID: D5/S1/Recurrence/Invariants/CassiniFrickeSpecializations
   generality: I
   mirror-B: D5/B/S1/Recurrence/Invariants/CassiniFrickeSpecializations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Log-coordinate Cassini-Fricke values alternate with conserved absolute value. -/

import D5.S1.Recurrence.CassiniFricke

namespace D5.S1.Recurrence.Invariants.CassiniFrickeSpecializations

open D5.S1.Recurrence.CassiniFricke

/-- Substituting `A = -x * phi` and `B = y * psi` into the generic
Cassini-Fricke identity gives the source's signed log-coordinate formula. -/
theorem cassini_fricke_log_coordinate_identity
    (x y : Real) (K : Nat) :
    (-x * Real.goldenRatio ^ (K + 2) + y * Real.goldenConj ^ (K + 2)) ^ 2 -
        (-x * Real.goldenRatio ^ (K + 2) + y * Real.goldenConj ^ (K + 2)) *
          (-x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1)) -
      (-x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1)) ^ 2 =
        5 * x * y * (-1) ^ (K + 1) := by
  have hphiK1 : Real.goldenRatio ^ (K + 1) =
      Real.goldenRatio ^ K * Real.goldenRatio := pow_succ Real.goldenRatio K
  have hpsiK1 : Real.goldenConj ^ (K + 1) =
      Real.goldenConj ^ K * Real.goldenConj := pow_succ Real.goldenConj K
  have hphiK2 : Real.goldenRatio ^ (K + 2) =
      Real.goldenRatio ^ (K + 1) * Real.goldenRatio :=
    pow_succ Real.goldenRatio (K + 1)
  have hpsiK2 : Real.goldenConj ^ (K + 2) =
      Real.goldenConj ^ (K + 1) * Real.goldenConj :=
    pow_succ Real.goldenConj (K + 1)
  calc
    _ = -5 * (-x * Real.goldenRatio) * (y * Real.goldenConj) * (-1) ^ K := by
      rw [hphiK2, hpsiK2, hphiK1, hpsiK1]
      convert cassini_fricke Real.goldenRatio Real.goldenConj
        (-x * Real.goldenRatio) (y * Real.goldenConj) K
        Real.goldenRatio_sq Real.goldenConj_sq
        Real.goldenRatio_add_goldenConj Real.goldenRatio_mul_goldenConj using 1
      all_goals ring
    _ = 5 * x * y * (Real.goldenRatio * Real.goldenConj) * (-1) ^ K := by ring
    _ = 5 * x * y * (-1) ^ (K + 1) := by
      rw [Real.goldenRatio_mul_goldenConj, pow_succ]
      ring

/-- The alternating sign disappears under absolute value, leaving the conserved
magnitude `5 * |x * y|`. -/
theorem cassini_fricke_absolute_conservation
    (x y : Real) (K : Nat) :
    abs ((-x * Real.goldenRatio ^ (K + 2) + y * Real.goldenConj ^ (K + 2)) ^ 2 -
        (-x * Real.goldenRatio ^ (K + 2) + y * Real.goldenConj ^ (K + 2)) *
          (-x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1)) -
      (-x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1)) ^ 2) =
        5 * abs (x * y) := by
  rw [cassini_fricke_log_coordinate_identity x y K]
  simp [abs_mul, abs_pow, mul_assoc]

#print axioms cassini_fricke_log_coordinate_identity
#print axioms cassini_fricke_absolute_conservation

end D5.S1.Recurrence.Invariants.CassiniFrickeSpecializations
