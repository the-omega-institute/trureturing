/- GID: D5/S3/PrimeForms/Crossing/ExactPropagation
   generality: I
   mirror-B: D5/B/S3/PrimeForms/Crossing/ExactPropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive-cone matrices satisfy the exact Dedekind phase propagation law. -/

/- Library-search audit trail (2026-08-16):
   * Local searches for a Rademacher phase or cocycle theorem in `D5` and the
     pinned Mathlib tree found no exact theorem.
   * Exact local hits: `DedekindBhkCertificates.dedekindSum`,
     `DedekindReciprocity.dedekind_reciprocity`, and
     `DedekindReciprocityFiniteSums.sum_mul_mod_permutation`; these frozen APIs
     are imported and applied below.
   * Loogle query `Rademacher phi cocycle` reached the service but returned
     `Unknown identifier Rademacher`; a grep.app query for `RademacherPhi`
     returned HTTP 503, and the attempted LeanSearch endpoint returned HTTP 404.
-/

import D5.S1.Phase.Interference.DedekindReciprocity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open Matrix

namespace D5.S3.PrimeForms.Crossing.ExactPropagation

open D5.S1.Phase.Interference.DedekindBhkCertificates
open D5.S1.Phase.Interference.DedekindReciprocityFiniteSums
open D5.S1.Phase.Interference.DedekindReciprocity

/-- A positive-entry matrix, recorded by its four natural coefficients. -/
structure PositiveMatrix where
  a : Nat
  b : Nat
  c : Nat
  d : Nat

/-- Multiplication in positive matrix coordinates. -/
def PositiveMatrix.mul (A B : PositiveMatrix) : PositiveMatrix where
  a := A.a * B.a + A.b * B.c
  b := A.a * B.b + A.b * B.d
  c := A.c * B.a + A.d * B.c
  d := A.c * B.b + A.d * B.d

/-- The lower-left coefficient of a positive matrix. -/
def lowerLeft (A : PositiveMatrix) : Nat := A.c

/-- The trace in positive matrix coordinates. -/
def matrixTrace (A : PositiveMatrix) : Nat := A.a + A.d

/-- The Rademacher phase formula in the chamber where the lower-left entry is positive. -/
def rademacherPhi (A : PositiveMatrix) : Rat :=
  ((A.a + A.d : Nat) : Rat) / (A.c : Rat) - 12 * dedekindSum A.d A.c

/-- The winding phase in the positive chamber, where the sign correction is exactly `3`. -/
def windingPhase (A : PositiveMatrix) : Rat := rademacherPhi A - 3

/-- The fixed crossing matrix `[[3,1],[2,1]]`. -/
def crossingMatrix : PositiveMatrix := ⟨3, 1, 2, 1⟩

/-- The positive-cone matrix in trace and crossing coordinates. -/
def coneMatrix (T b c : Nat) : PositiveMatrix :=
  ⟨T + c - b, b, c, T + b - c⟩

/-- A determinant-one relation makes the lower row coprime. -/
theorem lower_row_coprime {a b c d : Nat} (hdet : a * d = b * c + 1) :
    d.Coprime c := by
  apply Nat.coprime_of_mul_modEq_one a
  change (d * a) % c = 1 % c
  rw [mul_comm, hdet]
  simp [Nat.add_mod]

/-- Dedekind sums agree on inverse reduced numerators. -/
theorem dedekindSum_inverse {a d c : Nat} (hc : 0 < c)
    (hdc : d.Coprime c) (hinv : d * a % c = 1 % c) :
    dedekindSum d c = dedekindSum a c := by
  have hinv' : a * d ≡ 1 [MOD c] := by
    change (a * d) % c = 1 % c
    simpa [mul_comm] using hinv
  rw [dedekindSum_eq_mod_sum hc hdc,
    dedekindSum_eq_mod_sum hc (Nat.coprime_of_mul_modEq_one d hinv')]
  let f : Nat -> Rat := fun k =>
    ((k : Rat) / (c : Rat) - 1 / 2) *
      ((((k * a) % c : Nat) : Rat) / (c : Rat) - 1 / 2)
  have hperm := sum_mul_mod_permutation hc hdc f
  rw [show (∑ k ∈ Finset.Ico 1 c,
      (((k % c : Nat) : Rat) / (c : Rat) - 1 / 2) *
        ((((k * d) % c : Nat) : Rat) / (c : Rat) - 1 / 2)) =
      ∑ k ∈ Finset.Ico 1 c, f ((k * d) % c) by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt := (Finset.mem_Ico.mp hk).2
        have hprod : (((k * d) % c) * a) % c = k % c := by
          have hreduce : (k * d) % c ≡ k * d [MOD c] := Nat.mod_modEq _ _
          have hcancel : k * (d * a) ≡ k * 1 [MOD c] :=
            Nat.ModEq.mul_left k hinv
          exact (hreduce.mul_right a).trans (by simpa [mul_assoc] using hcancel)
        simp only [f]
        rw [Nat.mod_eq_of_lt hklt, hprod, Nat.mod_eq_of_lt hklt]
        ring,
    hperm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.mod_eq_of_lt (Finset.mem_Ico.mp hk).2]

/-- Right multiplication by the crossing matrix contributes the positive-chamber correction `-3`. -/
theorem rademacherPhi_mul_crossing (A : PositiveMatrix)
    (hc : 0 < A.c) (hd : 0 < A.d) (hdet : A.a * A.d = A.b * A.c + 1) :
    rademacherPhi (A.mul crossingMatrix) =
      rademacherPhi A + rademacherPhi crossingMatrix - 3 := by
  let c' := 3 * A.c + 2 * A.d
  let d' := A.c + A.d
  have hcd : A.c.Coprime A.d := (lower_row_coprime hdet).symm
  have hd' : 0 < d' := by simp [d', hc, hd]
  have hc' : 0 < c' := by simp [c', hc, hd]
  have hdet' : (3 * A.a + 2 * A.b) * d' =
      (A.a + A.b) * c' + 1 := by
    dsimp [c', d']
    nlinarith [hdet]
  have hcop' : c'.Coprime d' := (lower_row_coprime hdet').symm
  have hc_d' : A.c.Coprime d' := by
    simpa [d', Nat.coprime_add_self_right] using hcd
  have hsC : dedekindSum c' d' = dedekindSum A.c d' := by
    rw [<- s_mod c' d']
    congr 1
    have hc_lt : A.c < d' := by dsimp [d']; omega
    calc
      c' % d' = (2 * d' + A.c) % d' := by congr 1; dsimp [c', d']; omega
      _ = A.c % d' := by simp [Nat.add_mod]
      _ = A.c := Nat.mod_eq_of_lt hc_lt
  have hsD : dedekindSum d' A.c = dedekindSum A.d A.c := by
    rw [<- s_mod d' A.c, <- s_mod A.d A.c]
    congr 1
    dsimp [d']
    simp
  have hrec' := dedekind_reciprocity hc' hd' hcop'
  have hrec := dedekind_reciprocity hd' hc hc_d'.symm
  rw [hsC] at hrec'
  rw [hsD] at hrec
  have hs : dedekindSum d' c' = dedekindSum A.d A.c +
      (-(1 / 4) +
        ((c' : Rat) / (d' : Rat) + (d' : Rat) / (c' : Rat) +
          1 / ((c' : Rat) * (d' : Rat))) / 12) -
      (-(1 / 4) +
        ((d' : Rat) / (A.c : Rat) + (A.c : Rat) / (d' : Rat) +
          1 / ((d' : Rat) * (A.c : Rat))) / 12) := by
    linarith [hrec', hrec]
  rw [show rademacherPhi (A.mul crossingMatrix) =
      (((3 * A.a + 2 * A.b + d' : Nat) : Rat) / (c' : Rat) -
        12 * dedekindSum d' c') by
          simp [rademacherPhi, PositiveMatrix.mul, crossingMatrix, c', d',
            mul_comm],
    hs]
  unfold rademacherPhi crossingMatrix
  rw [dedekind_sum_one_two]
  have hcRat : (A.c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  have hd'Rat : (d' : Rat) ≠ 0 := by exact_mod_cast hd'.ne'
  have hc'Rat : (c' : Rat) ≠ 0 := by exact_mod_cast hc'.ne'
  have hdetRat : (A.a : Rat) * A.d = A.b * A.c + 1 := by exact_mod_cast hdet
  dsimp [c', d'] at hd'Rat hc'Rat ⊢
  field_simp [hcRat, hd'Rat, hc'Rat]
  push_cast
  ring_nf at hdetRat ⊢
  nlinarith [hdetRat]

/-- Left multiplication by the crossing matrix has the same positive-chamber correction. -/
theorem rademacherPhi_crossing_mul (A : PositiveMatrix)
    (ha : 0 < A.a) (hc : 0 < A.c) (hd : 0 < A.d)
    (hdet : A.a * A.d = A.b * A.c + 1) :
    rademacherPhi (crossingMatrix.mul A) =
      rademacherPhi crossingMatrix + rademacherPhi A - 3 := by
  let c' := 2 * A.a + A.c
  let d' := 2 * A.b + A.d
  let a' := 3 * A.a + A.c
  have hc' : 0 < c' := by simp [c', ha, hc]
  have hd' : 0 < d' := by
    dsimp [d']
    omega
  have hdet' : a' * d' = (3 * A.b + A.d) * c' + 1 := by
    dsimp [a', c', d']
    nlinarith [hdet]
  have hcop' : d'.Coprime c' := lower_row_coprime hdet'
  have hinv' : d' * a' % c' = 1 % c' := by
    show (d' * a') % c' = 1 % c'
    rw [mul_comm, hdet']
    simp [Nat.add_mod]
  have hsInv' : dedekindSum d' c' = dedekindSum a' c' :=
    dedekindSum_inverse hc' hcop' hinv'
  have hcop : A.d.Coprime A.c := lower_row_coprime hdet
  have hinv : A.d * A.a % A.c = 1 % A.c := by
    show (A.d * A.a) % A.c = 1 % A.c
    rw [mul_comm, hdet]
    simp [Nat.add_mod]
  have hsInv : dedekindSum A.d A.c = dedekindSum A.a A.c :=
    dedekindSum_inverse hc hcop hinv
  have hac : A.a.Coprime A.c := by
    apply Nat.coprime_of_mul_modEq_one A.d
    change (A.a * A.d) % A.c = 1 % A.c
    rw [hdet]
    simp [Nat.add_mod]
  have ha_c' : A.a.Coprime c' := by
    rw [show c' = A.c + 2 * A.a by dsimp [c']; omega,
      Nat.coprime_add_mul_right_right]
    exact hac
  have hsC : dedekindSum c' A.a = dedekindSum A.c A.a := by
    rw [<- s_mod c' A.a, <- s_mod A.c A.a]
    congr 1
    dsimp [c']
    simp [Nat.add_mod]
  have hsA : dedekindSum a' c' = dedekindSum A.a c' := by
    rw [<- s_mod a' c']
    congr 1
    have ha_lt : A.a < c' := by dsimp [c']; omega
    calc
      a' % c' = (c' + A.a) % c' := by congr 1; dsimp [a', c']; omega
      _ = A.a % c' := by simp
      _ = A.a := Nat.mod_eq_of_lt ha_lt
  have hrec' := dedekind_reciprocity hc' ha ha_c'.symm
  have hrec := dedekind_reciprocity hc ha hac.symm
  rw [hsC] at hrec'
  rw [<- hsInv] at hrec
  have hs : dedekindSum d' c' = dedekindSum A.d A.c +
      (-(1 / 4) +
        ((c' : Rat) / (A.a : Rat) + (A.a : Rat) / (c' : Rat) +
          1 / ((c' : Rat) * (A.a : Rat))) / 12) -
      (-(1 / 4) +
        ((A.c : Rat) / (A.a : Rat) + (A.a : Rat) / (A.c : Rat) +
          1 / ((A.c : Rat) * (A.a : Rat))) / 12) := by
    rw [hsInv', hsA]
    linarith [hrec', hrec]
  rw [show rademacherPhi (crossingMatrix.mul A) =
      (((a' + d' : Nat) : Rat) / (c' : Rat) - 12 * dedekindSum d' c') by
        simp [rademacherPhi, PositiveMatrix.mul, crossingMatrix, a', c', d',
          mul_comm],
    hs]
  unfold rademacherPhi crossingMatrix
  rw [dedekind_sum_one_two]
  have haRat : (A.a : Rat) ≠ 0 := by exact_mod_cast ha.ne'
  have hcRat : (A.c : Rat) ≠ 0 := by exact_mod_cast hc.ne'
  have hc'Rat : (c' : Rat) ≠ 0 := by exact_mod_cast hc'.ne'
  have hdetRat : (A.a : Rat) * A.d = A.b * A.c + 1 := by exact_mod_cast hdet
  dsimp [a', c', d'] at hc'Rat ⊢
  field_simp [haRat, hcRat, hc'Rat]
  push_cast
  ring_nf at hdetRat ⊢
  nlinarith [hdetRat]

/-- The fixed crossing matrix has Rademacher phase exactly `2`. -/
theorem rademacherPhi_crossingMatrix : rademacherPhi crossingMatrix = 2 := by
  norm_num [rademacherPhi, crossingMatrix, dedekind_sum_one_two]

/-- Exact propagation on the positive cone. The four lower-left entries are
computed explicitly; the cone equation supplies the stated square-root bound,
which makes both endpoint sign corrections positive. Dedekind reciprocity then
gives two corrections of `-3` and hence the winding phase drops by exactly `2`. -/
theorem exact_propagation_positive_cone (T b c : Nat)
    (hT : 2 ≤ T) (hb : b ≤ c)
    (hquad : b ^ 2 + c ^ 2 + 1 = T ^ 2 + b * c) :
    let gamma := coneMatrix T b c
    let M := crossingMatrix
    lowerLeft gamma = c ∧
      lowerLeft M = 2 ∧
      lowerLeft (gamma.mul M) = c + 2 * T + 2 * b ∧
      lowerLeft (M.mul (gamma.mul M)) = 8 * T + 7 * c ∧
      ((c + 2 * T + 2 * b : Nat) : Real) ≥
        2 * c + 2 * (T - Real.sqrt ((T : Real) ^ 2 - 1)) ∧
      2 * (c : Real) + 2 * (T - Real.sqrt ((T : Real) ^ 2 - 1)) > 0 ∧
      0 < lowerLeft gamma * matrixTrace gamma ∧
      0 < lowerLeft (M.mul (gamma.mul M)) * matrixTrace (M.mul (gamma.mul M)) ∧
      rademacherPhi M = 2 ∧
      rademacherPhi (gamma.mul M) =
        rademacherPhi gamma + rademacherPhi M - 3 ∧
      rademacherPhi (M.mul (gamma.mul M)) =
        rademacherPhi M + rademacherPhi (gamma.mul M) - 3 ∧
      windingPhase (M.mul (gamma.mul M)) = windingPhase gamma - 2 := by
  dsimp only
  have hc : 0 < c := by
    by_contra h
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos h
    have hb0 : b = 0 := by omega
    subst c
    subst b
    norm_num at hquad
    nlinarith
  have hdc : c < T + b := by
    by_contra h
    have hle : T + b ≤ c := by omega
    nlinarith [hquad]
  have ha : 0 < T + c - b := by omega
  have hd : 0 < T + b - c := by omega
  have hdet : (T + c - b) * (T + b - c) = b * c + 1 := by
    apply Nat.cast_injective (R := Int)
    have hb' : b ≤ T + c := by omega
    have hc' : c ≤ T + b := by omega
    rw [Nat.cast_mul, Nat.cast_sub hb', Nat.cast_sub hc']
    have hquadInt :
        (b : Int) ^ 2 + (c : Int) ^ 2 + 1 = (T : Int) ^ 2 + b * c := by
      exact_mod_cast hquad
    push_cast
    nlinarith [hquadInt]
  have hcGammaM :
      lowerLeft ((coneMatrix T b c).mul crossingMatrix) = c + 2 * T + 2 * b := by
    simp [lowerLeft, PositiveMatrix.mul, coneMatrix, crossingMatrix]
    omega
  have hcSandwich :
      lowerLeft (crossingMatrix.mul ((coneMatrix T b c).mul crossingMatrix)) =
        8 * T + 7 * c := by
    simp [lowerLeft, PositiveMatrix.mul, coneMatrix, crossingMatrix]
    omega
  have hquadReal :
      (b : Real) ^ 2 + (c : Real) ^ 2 + 1 = (T : Real) ^ 2 + b * c := by
    exact_mod_cast hquad
  have hrootArg : 0 ≤ (T : Real) ^ 2 - 1 := by
    have hTReal : (2 : Real) ≤ T := by exact_mod_cast hT
    nlinarith
  have hsqrtSq := Real.sq_sqrt hrootArg
  have hbc : 0 ≤ (b : Real) * c := mul_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg c)
  have hdiff : 0 ≤ (c : Real) - b :=
    sub_nonneg.mpr (by exact_mod_cast hb)
  have hdiffSq : ((c : Real) - b) ^ 2 ≤ (T : Real) ^ 2 - 1 := by
    nlinarith [hquadReal]
  have hdiffRoot : (c : Real) - b ≤ Real.sqrt ((T : Real) ^ 2 - 1) := by
    nlinarith [Real.sqrt_nonneg ((T : Real) ^ 2 - 1)]
  have hrootLt : Real.sqrt ((T : Real) ^ 2 - 1) < T := by
    have hTReal : 0 < (T : Real) := by positivity
    nlinarith [Real.sqrt_nonneg ((T : Real) ^ 2 - 1)]
  have hineq : ((c + 2 * T + 2 * b : Nat) : Real) ≥
      2 * c + 2 * (T - Real.sqrt ((T : Real) ^ 2 - 1)) := by
    push_cast
    have hcReal : 0 ≤ (c : Real) := by positivity
    nlinarith [hdiffRoot]
  have hstrict : 2 * (c : Real) +
      2 * (T - Real.sqrt ((T : Real) ^ 2 - 1)) > 0 := by
    positivity
  have htraceGamma : matrixTrace (coneMatrix T b c) = 2 * T := by
    simp [matrixTrace, coneMatrix]
    omega
  have htraceSandwich :
      matrixTrace (crossingMatrix.mul ((coneMatrix T b c).mul crossingMatrix)) =
        14 * T + 12 * c := by
    simp [matrixTrace, PositiveMatrix.mul, coneMatrix, crossingMatrix]
    omega
  have hsignGamma : 0 < lowerLeft (coneMatrix T b c) * matrixTrace (coneMatrix T b c) := by
    rw [htraceGamma]
    simp [lowerLeft, coneMatrix, hc]
    omega
  have hsignSandwich : 0 <
      lowerLeft (crossingMatrix.mul ((coneMatrix T b c).mul crossingMatrix)) *
        matrixTrace (crossingMatrix.mul ((coneMatrix T b c).mul crossingMatrix)) := by
    rw [hcSandwich, htraceSandwich]
    positivity
  have hright := rademacherPhi_mul_crossing (coneMatrix T b c) hc hd hdet
  have haRight : 0 < ((coneMatrix T b c).mul crossingMatrix).a := by
    simp [PositiveMatrix.mul, coneMatrix, crossingMatrix]
    omega
  have hcRight : 0 < ((coneMatrix T b c).mul crossingMatrix).c := by
    change 0 < lowerLeft ((coneMatrix T b c).mul crossingMatrix)
    rw [hcGammaM]
    omega
  have hdRight : 0 < ((coneMatrix T b c).mul crossingMatrix).d := by
    simp [PositiveMatrix.mul, coneMatrix, crossingMatrix]
    omega
  have hdetRight :
      ((coneMatrix T b c).mul crossingMatrix).a *
          ((coneMatrix T b c).mul crossingMatrix).d =
        ((coneMatrix T b c).mul crossingMatrix).b *
          ((coneMatrix T b c).mul crossingMatrix).c + 1 := by
    simp [PositiveMatrix.mul, coneMatrix, crossingMatrix]
    nlinarith [hdet]
  have hleft := rademacherPhi_crossing_mul
    ((coneMatrix T b c).mul crossingMatrix) haRight hcRight hdRight hdetRight
  have hphase :
      windingPhase (crossingMatrix.mul ((coneMatrix T b c).mul crossingMatrix)) =
        windingPhase (coneMatrix T b c) - 2 := by
    unfold windingPhase
    rw [hleft, hright, rademacherPhi_crossingMatrix]
    ring
  exact ⟨rfl, rfl, hcGammaM, hcSandwich, hineq, hstrict, hsignGamma,
    hsignSandwich, rademacherPhi_crossingMatrix, hright, hleft, hphase⟩

/-- The cone hypotheses are inhabited by the fixed crossing matrix itself. -/
example : (1 : Nat) ^ 2 + 2 ^ 2 + 1 = 2 ^ 2 + 1 * 2 := by norm_num

/-- The full propagation theorem applies to the smallest positive-cone witness. -/
example :
    windingPhase (crossingMatrix.mul ((coneMatrix 2 1 2).mul crossingMatrix)) =
      windingPhase (coneMatrix 2 1 2) - 2 := by
  have h := exact_propagation_positive_cone 2 1 2 (by norm_num) (by norm_num) (by norm_num)
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hphase⟩
  exact hphase

#print axioms dedekindSum_inverse
#print axioms rademacherPhi_mul_crossing
#print axioms rademacherPhi_crossing_mul
#print axioms exact_propagation_positive_cone

end D5.S3.PrimeForms.Crossing.ExactPropagation
