/- GID: D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim; result=D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.result; claim=D5/S3/Quantum/Algebra/CoulombBranchPoissonBracketRefutation.claim
   digest: Jacobi and reducedness obstruct the proposed E6 and truck spinor Poisson brackets. -/

import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic

/-! The diagonal spinor brackets force their weight element to vanish in a reduced algebra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation

/-- A complex bilinear, antisymmetric biderivation satisfying the Jacobi identity. -/
def IsPoissonBracket {R : Type*} [CommRing R] [Algebra ℂ R] (br : R → R → R) : Prop :=
  (∀ a b c, br (a + b) c = br a c + br b c) ∧
  (∀ (c : ℂ) a b, br (c • a) b = c • br a b) ∧
  (∀ a b c, br a (b + c) = br a b + br a c) ∧
  (∀ (c : ℂ) a b, br a (c • b) = c • br a b) ∧
  (∀ a b, br a b = -br b a) ∧
  (∀ a b c, br a (b * c) = br a b * c + b * br a c) ∧
  (∀ a b c, br a (br b c) + br b (br c a) + br c (br a b) = 0)

/-- Uniform diagonal mixed spinor brackets, weights, and vanishing equal-charge brackets. -/
def SpinorBrackets {R : Type*} [CommRing R] {N : ℕ}
    (br : R → R → R) (h : R) (sUp sDn : Fin N → R) (e : ℕ) : Prop :=
  (∀ α, br h (sUp α) = sUp α) ∧
  (∀ α, br h (sDn α) = -sDn α) ∧
  (∀ α β, br (sUp α) (sDn β) = if α = β then h ^ e else 0) ∧
  (∀ α β, br (sUp α) (sUp β) = 0) ∧
  (∀ α β, br (sDn α) (sDn β) = 0)

/-- The proposed brackets for every admissible member of the second E6 family. -/
def ConjE6 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ (R : Type) (ringR : CommRing R),
    letI := ringR
    ∃ algR : Algebra ℂ R,
      letI := algR
      IsReduced R ∧ ∃ (br : R → R → R) (h : R) (sUp sDn : Fin (2 ^ (2 * n)) → R),
        IsPoissonBracket br ∧ h ≠ 0 ∧ SpinorBrackets br h sUp sDn (n - 1)

/-- The proposed brackets for every admissible truck rank and positive multiplicity. -/
def ConjTruck : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ σ : ℕ, 1 ≤ σ → ∃ (R : Type) (ringR : CommRing R),
    letI := ringR
    ∃ algR : Algebra ℂ R,
      letI := algR
      IsReduced R ∧ ∃ (br : R → R → R) (h : R) (sUp sDn : Fin (2 ^ (2 * n)) → R),
        IsPoissonBracket br ∧ h ≠ 0 ∧ SpinorBrackets br h sUp sDn (n + σ - 1)

/-- At least one of the two proposed families exists in reduced complex algebras. -/
def claim : Prop := ConjE6 ∨ ConjTruck

private def hamiltonian {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a : R) : Derivation ℂ R R := by
  refine Derivation.mk' {
    toFun := br a
    map_add' := hp.2.2.1 a
    map_smul' := fun c b => hp.2.2.2.1 c a b } ?_
  intro b c
  change br a (b * c) = b • br a c + c • br a b
  rw [hp.2.2.2.2.2.1]
  simp only [smul_eq_mul]
  ring

private lemma bracket_mul_left {R : Type*} [CommRing R] [Algebra ℂ R]
    (br : R → R → R) (hp : IsPoissonBracket br) (a b c : R) :
    br (a * b) c = a * br b c + br a c * b := by
  have ha := hp.2.2.2.2.1
  rw [ha (a * b) c, hp.2.2.2.2.2.1, ha c a, ha c b]
  ring

private lemma bracket_forces_zero {R : Type*} [CommRing R] [Algebra ℂ R] [IsReduced R]
    (br : R → R → R) (hp : IsPoissonBracket br) (e : ℕ) (he : 1 ≤ e)
    (h x y z w : R) (hhx : br h x = x) (hhy : br h y = -y)
    (hxy : br x y = h ^ e) (hzw : br z w = h ^ e)
    (hxw : br x w = 0) (hxz : br x z = 0) : h = 0 := by
  have ha := hp.2.2.2.2.1
  have hz (a : R) : br a 0 = 0 := (hamiltonian br hp a).map_zero
  cases e with
  | zero => exact (Nat.not_succ_le_zero 0 he).elim
  | succ k =>
    have hwx : br w x = 0 := by rw [ha w x, hxw, neg_zero]
    have hxh : br x h = -x := by rw [ha x h, hhx]
    have hj := hp.2.2.2.2.2.2 x z w
    rw [hzw, hwx, hxz, hz z, hz w, add_zero, add_zero,
      (show br x (h ^ (k + 1)) = (k + 1) • (h ^ (k + 1 - 1) * br x h) from
        (hamiltonian br hp x).leibniz_pow h (k + 1)), hxh] at hj
    have hpowx : h ^ k * x = 0 := by
      have hc : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have hscaled : ((k + 1 : ℕ) : ℂ) • (h ^ k * x) = 0 := by
        rw [Nat.cast_smul_eq_nsmul]
        simpa only [Nat.add_sub_cancel, mul_neg, smul_neg, neg_eq_zero] using hj
      exact (smul_eq_zero_iff_right hc).mp hscaled
    have hzero : br (h ^ k * x) y = 0 := by
      rw [hpowx, ha 0 y, hz y, neg_zero]
    rw [bracket_mul_left br hp, hxy, ha (h ^ k) y,
      (show br y (h ^ k) = k • (h ^ (k - 1) * br y h) from
        (hamiltonian br hp y).leibniz_pow h k), ha y h, hhy, neg_neg] at hzero
    simp only [nsmul_eq_mul] at hzero
    have hterm : h * ((k : R) * (h ^ (k - 1) * y)) * x = 0 := by
      cases k with
      | zero => simp only [Nat.cast_zero, zero_mul, mul_zero]
      | succ m =>
        calc
          h * ((↑(m + 1) : R) * (h ^ (m + 1 - 1) * y)) * x =
              (↑(m + 1) : R) * (h ^ (m + 1) * x) * y := by
                simp only [Nat.add_sub_cancel, pow_succ]
                ring
          _ = 0 := by rw [hpowx, mul_zero, zero_mul]
    have hnil : h ^ (2 * (k + 1)) = 0 := by
      calc
        h ^ (2 * (k + 1)) = h * (h ^ k * h ^ (k + 1)) := by
          rw [Nat.mul_comm, pow_mul, pow_two, pow_succ]
          ring
        _ = h * (h ^ k * h ^ (k + 1) + -((k : R) * (h ^ (k - 1) * y)) * x) +
              h * ((k : R) * (h ^ (k - 1) * y)) * x := by ring
        _ = 0 := by rw [hzero, hterm, mul_zero, add_zero]
    exact (show IsNilpotent h from ⟨2 * (k + 1), hnil⟩).eq_zero

private lemma spinor_forces_zero {R : Type*} [CommRing R] [Algebra ℂ R] [IsReduced R]
    {N : ℕ} (hN : 2 ≤ N) (br : R → R → R) (hp : IsPoissonBracket br)
    (h : R) (sUp sDn : Fin N → R) (e : ℕ) (he : 1 ≤ e)
    (hs : SpinorBrackets br h sUp sDn e) : h = 0 := by
  let i : Fin N := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hN⟩
  let j : Fin N := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hN⟩
  have hij : i ≠ j := (Fin.ne_iff_vne i j).mpr Nat.zero_ne_one
  apply bracket_forces_zero br hp e he h (sUp i) (sDn i) (sUp j) (sDn j)
  · exact hs.1 i
  · exact hs.2.1 i
  · rw [hs.2.2.1, ite_eq_left rfl]
  · rw [hs.2.2.1, ite_eq_left rfl]
  · rw [hs.2.2.1, ite_eq_right hij]
  · exact hs.2.2.2.1 i j

private lemma not_conjE6 : ¬ ConjE6 := by
  intro hc
  obtain ⟨R, ringR, algR, hr, br, h, sUp, sDn, hp, hn, hs⟩ := hc 3 (by decide)
  let _ := ringR
  let _ := algR
  let _ := hr
  exact hn (spinor_forces_zero (by decide) br hp h sUp sDn 2 (by decide) hs)

private lemma not_conjTruck : ¬ ConjTruck := by
  intro hc
  obtain ⟨R, ringR, algR, hr, br, h, sUp, sDn, hp, hn, hs⟩ :=
    hc 2 (by decide) 1 (by decide)
  let _ := ringR
  let _ := algR
  let _ := hr
  exact hn (spinor_forces_zero (by decide) br hp h sUp sDn 2 (by decide) hs)

/-- Neither proposed family of spinor brackets exists in reduced complex algebras. -/
theorem result : ¬ claim := by
  intro hc
  rcases hc with hc | hc
  · exact not_conjE6 hc
  · exact not_conjTruck hc

end D5.S3.Quantum.Algebra.CoulombBranchPoissonBracketRefutation
