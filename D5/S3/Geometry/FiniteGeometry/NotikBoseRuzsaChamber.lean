/- GID: D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber
   generality: I
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.claim; result=D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.result; claim=D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.claim
   digest: Shorter real rulers refute both of Notik's chamber analogues. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Bose and Ruzsa chamber assertions

Esther Notik, *Golomb rulers with real marks: the real and integer optima agree up to ten marks*,
arXiv:2611.22656v1, §10, asks for the analogues of the §7 assertion for the Bose and Ruzsa families.
After a cut at a largest cyclic gap, the kept gaps are the coordinates of the reference ruler.
-/

set_option autoImplicit false

namespace D5.S3.Geometry.FiniteGeometry.NotikBoseRuzsaChamber

open scoped BigOperators

/-- The labelled distances are indexed by increasing pairs of mark indices. -/
def Label (n : ℕ) : Type := {p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2}

private instance (n : ℕ) : Fintype (Label n) :=
  inferInstanceAs (Fintype {p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2})

private instance (n : ℕ) : DecidableEq (Label n) :=
  inferInstanceAs (DecidableEq {p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2})

/-- The sum of kept gaps starting at mark `i` and ending at mark `j`. -/
def intervalSum {A : Type} [AddCommMonoid A] {n : ℕ} (g : Fin n → A) (i j : ℕ) : A :=
  ∑ k : Fin n, if i ≤ k.val ∧ k.val < j then g k else 0

/-- The labelled distance from the first mark of the pair to the second. -/
def distance {A : Type} [AddCommMonoid A] {n : ℕ} (g : Fin n → A) (p : Label n) : A :=
  intervalSum g p.val.1.val p.val.2.val

/-- The reference distances are distinct. The candidate has unit separation from zero
and between distances in the reference order. -/
def ChamberOrder {A : Type} [AddCommMonoid A] [One A] [LE A] {n : ℕ}
    (reference : Fin n → ℕ) (g : Fin n → A) : Prop :=
  (∀ p q : Label n, distance reference p = distance reference q → p = q) ∧
    (∀ p : Label n, 1 ≤ distance g p) ∧
    ∀ p q : Label n, distance reference p < distance reference q →
      distance g p + 1 ≤ distance g q

/-- The reference distances are distinct, and the reference is the only shortest point
of its real chamber. The first mark is fixed at zero in gap coordinates. -/
def UniqueShortest {n : ℕ} (g : Fin n → ℕ) : Prop :=
  ChamberOrder g (fun i => (g i : ℝ)) ∧
    ∀ x : Fin n → ℝ, ChamberOrder g x →
      intervalSum x 0 n ≤ ((intervalSum g 0 n : ℕ) : ℝ) → x = fun i => (g i : ℝ)

/-- The cut starts at a member of the cyclic set. The omitted gap has size
`N - intervalSum g 0 n` and is at least as large as every kept gap. -/
def LargestGapCut {N n : ℕ} (residues : Fin N → Prop) (start : Fin N)
    (g : Fin n → ℕ) : Prop :=
  (∀ i : Fin n, 0 < g i) ∧ intervalSum g 0 n < N ∧
    (∀ i : Fin n, g i ≤ N - intervalSum g 0 n) ∧
    ∀ r : Fin N, residues r ↔
      ∃ i : Fin (n + 1), r.val = (start.val + intervalSum g 0 i.val) % N

/-- The exponents on the affine line through the generator, multiplied by `u` modulo
the order of the multiplicative group. -/
def BoseResidue {F K : Type} [Field F] [Field K] [Algebra F K] {N : ℕ}
    (theta : K) (u : ℕ) (r : Fin N) : Prop :=
  ∃ e : Fin N, r.val = (u * e.val) % N ∧
    ∃ a : F, theta ^ e.val = theta + algebraMap F K a

/-- After multiplication by `u`, a Ruzsa residue comes from a CRT solution
with residue `i` modulo `p - 1` and residue `generator ^ i` modulo `p`. -/
def RuzsaResidue {p : ℕ} (generator : ZMod p) (u : ℕ) (r : Fin (p * (p - 1))) : Prop :=
  ∃ s : Fin (p * (p - 1)), ∃ i : Fin (p - 1),
    r.val = (u * s.val) % (p * (p - 1)) ∧ s.val % (p - 1) = i.val ∧
      (s.val : ZMod p) = generator ^ i.val

/-- The Bose assertion over every finite base field and quadratic extension. -/
def Bose : Prop :=
  ∀ (q : ℕ) (F K : Type) [Field F] [Field K] [Algebra F K] [Finite F],
    Nat.card F = q → Nat.card K = q ^ 2 →
    ∀ (theta : K) (u : ℕ), orderOf theta = q ^ 2 - 1 →
      u.Coprime (q ^ 2 - 1) →
      ∀ (start : Fin (q ^ 2 - 1)) (g : Fin (q - 1) → ℕ),
        LargestGapCut (BoseResidue (F := F) theta u) start g → UniqueShortest g

/-- The Ruzsa assertion over every prime modulus and choice of primitive root. -/
def Ruzsa : Prop :=
  ∀ (p : ℕ), p.Prime →
    ∀ (generator : ZMod p) (u : ℕ), orderOf generator = p - 1 →
      u.Coprime (p * (p - 1)) →
      ∀ (start : Fin (p * (p - 1))) (g : Fin (p - 2) → ℕ),
        LargestGapCut (RuzsaResidue generator u) start g → UniqueShortest g

/-- The disjunction of the two universal assertions in Notik's §10. -/
def claim : Prop := Bose ∨ Ruzsa

private theorem intervalSum_ratCast {n : ℕ} (g : Fin n → ℚ) (i j : ℕ) :
    intervalSum (fun k => (g k : ℝ)) i j = ((intervalSum g i j : ℚ) : ℝ) := by
  unfold intervalSum
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp_all

private theorem not_uniqueShortest_of_rat {n : ℕ} (g : Fin n → ℕ) (x : Fin n → ℚ)
    (hx : ChamberOrder g x) (hshort : intervalSum x 0 n < ((intervalSum g 0 n : ℕ) : ℚ)) :
    ¬ UniqueShortest g := by
  intro h
  have hreal : ChamberOrder g (fun i => (x i : ℝ)) := by
    rcases hx with ⟨hdistinct, hpositive, hseparation⟩
    refine ⟨hdistinct, ?_, ?_⟩
    · intro p
      rw [distance, intervalSum_ratCast]
      exact_mod_cast hpositive p
    · intro p q hpq
      simp only [distance, intervalSum_ratCast]
      exact_mod_cast hseparation p q hpq
  have hlt : intervalSum (fun i => (x i : ℝ)) 0 n < ((intervalSum g 0 n : ℕ) : ℝ) := by
    rw [intervalSum_ratCast]
    exact_mod_cast hshort
  have heq := h.2 _ hreal hlt.le
  rw [heq] at hlt
  have hcast : intervalSum (fun i => (g i : ℝ)) 0 n = ((intervalSum g 0 n : ℕ) : ℝ) := by
    unfold intervalSum
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    split <;> simp_all
  exact (lt_irrefl _) (hcast ▸ hlt)

private def ruzsaGaps : Fin 3 → ℕ := ![2, 1, 6]

private def ruzsaShorter : Fin 3 → ℚ := ![2, 1, 5]

private theorem ruzsaCut : LargestGapCut (RuzsaResidue (2 : ZMod 5) 1) 14 ruzsaGaps := by
  unfold LargestGapCut RuzsaResidue
  decide

private theorem ruzsa_false : ¬ Ruzsa := by
  intro h
  have horder : orderOf (2 : ZMod 5) = 5 - 1 := by
    apply (orderOf_eq_iff (by decide)).2
    refine ⟨by decide, ?_⟩
    intro m hm hlt
    interval_cases m <;> decide
  refine not_uniqueShortest_of_rat ruzsaGaps ruzsaShorter ?_ ?_
    (h 5 (by decide) 2 1 horder (by decide) 14 ruzsaGaps ruzsaCut)
  · unfold ChamberOrder
    decide +kernel
  · decide +kernel


open Polynomial

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private noncomputable def bosePolynomial : (ZMod 7)[X] := X ^ 2 + C 4

private theorem bosePolynomial_degree : bosePolynomial.natDegree = 2 := by
  unfold bosePolynomial
  compute_degree
  exact one_ne_zero

private theorem bosePolynomial_monic : bosePolynomial.Monic := by
  unfold bosePolynomial
  exact monic_X_pow_add_C _ (by decide)

private theorem bosePolynomial_irreducible : Irreducible bosePolynomial := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [bosePolynomial_degree]
    decide
  · have noRoot : ∀ a : ZMod 7, a ^ 2 + 4 ≠ 0 := by decide
    intro a
    simpa [IsRoot, bosePolynomial] using noRoot a

private abbrev BoseField := AdjoinRoot bosePolynomial

private instance : Fact (Irreducible bosePolynomial) := ⟨bosePolynomial_irreducible⟩

private theorem boseField_card : Nat.card BoseField = 7 ^ 2 := by
  let := bosePolynomial_monic.finite_adjoinRoot
  rw [Module.natCard_eq_pow_finrank (K := ZMod 7),
    (AdjoinRoot.powerBasis' bosePolynomial_monic).finrank, AdjoinRoot.powerBasis'_dim,
    bosePolynomial_degree, Nat.card_zmod]

private noncomputable def beta : BoseField := AdjoinRoot.root bosePolynomial

private noncomputable def theta : BoseField := 1 + beta

private theorem beta_sq : beta ^ 2 = algebraMap (ZMod 7) BoseField 3 := by
  have h : beta ^ 2 + algebraMap (ZMod 7) BoseField 4 = 0 := by
    have hroot := AdjoinRoot.eval₂_root bosePolynomial
    change (X ^ 2 + C 4 : (ZMod 7)[X]).eval₂ (AdjoinRoot.of bosePolynomial) beta = 0 at hroot
    simpa only [eval₂_add, eval₂_X_pow, eval₂_C, AdjoinRoot.algebraMap_eq] using hroot
  calc
    beta ^ 2 = -algebraMap (ZMod 7) BoseField 4 := eq_neg_of_add_eq_zero_left h
    _ = _ := by rw [← map_neg]; congr 1

private noncomputable def coordinate (a b : ZMod 7) : BoseField :=
  algebraMap (ZMod 7) BoseField a + algebraMap (ZMod 7) BoseField b * beta

private theorem coordinate_mul_theta (a b : ZMod 7) :
    coordinate a b * theta = coordinate (a + 3 * b) (a + b) := by
  unfold coordinate theta
  let f := algebraMap (ZMod 7) BoseField
  change (f a + f b * beta) * (1 + beta) = f (a + 3 * b) + f (a + b) * beta
  calc
    _ = f a + f b * beta ^ 2 + (f a + f b) * beta := by ring
    _ = _ := by rw [beta_sq]; simp only [map_add, map_mul]; ring

private def coefficients : ℕ → ZMod 7 × ZMod 7
  | 0 => (1, 0)
  | n + 1 =>
    let (a, b) := coefficients n
    (a + 3 * b, a + b)

private theorem theta_pow (m : ℕ) :
    theta ^ m = coordinate (coefficients m).1 (coefficients m).2 := by
  induction m with
  | zero => simp [coefficients, coordinate]
  | succ m ih =>
    rw [pow_succ, ih, coordinate_mul_theta]
    rfl

private theorem theta_pow_eq (m : ℕ) (a b : ZMod 7) (h : coefficients m = (a, b)) :
    theta ^ m = coordinate a b := by
  rw [theta_pow, h]

private theorem theta_order : orderOf theta = 48 := by
  have h48 : theta ^ 48 = 1 := by
    rw [theta_pow_eq 48 1 0 (by decide)]
    simp [coordinate]
  have h16 : theta ^ 16 ≠ 1 := by
    rw [theta_pow_eq 16 4 0 (by decide)]
    simp only [coordinate, map_zero, zero_mul, add_zero]
    intro heq
    apply (show (4 : ZMod 7) ≠ 1 by decide)
    exact (algebraMap (ZMod 7) BoseField).injective (heq.trans (map_one _).symm)
  have h24 : theta ^ 24 ≠ 1 := by
    rw [theta_pow_eq 24 6 0 (by decide)]
    simp only [coordinate, map_zero, zero_mul, add_zero]
    intro heq
    apply (show (6 : ZMod 7) ≠ 1 by decide)
    exact (algebraMap (ZMod 7) BoseField).injective (heq.trans (map_one _).symm)
  have hdvd := orderOf_dvd_of_pow_eq_one h48
  have h16' : ¬ orderOf theta ∣ 16 := fun h => h16 (orderOf_dvd_iff_pow_eq_one.mp h)
  have h24' : ¬ orderOf theta ∣ 24 := fun h => h24 (orderOf_dvd_iff_pow_eq_one.mp h)
  have divisors : ∀ d : Fin 49, d.val ∣ 48 → ¬ d.val ∣ 16 → ¬ d.val ∣ 24 → d.val = 48 := by
    decide
  exact divisors ⟨orderOf theta, Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hdvd)⟩
    hdvd h16' h24'

/-- The exponent for each point `theta + a` on the affine line. -/
private def lineExponent (a : ZMod 7) : Fin 48 :=
  (![1, 18, 21, 27, 6, 31, 20] : Fin 7 → Fin 48) ((ZMod.finEquiv 7).symm a)

private theorem lineExponent_spec (a : ZMod 7) :
    theta ^ (lineExponent a).val = theta + algebraMap (ZMod 7) BoseField a := by
  have coordinates : ∀ a : ZMod 7, coefficients (lineExponent a).val = (1 + a, 1) := by
    decide
  rw [theta_pow_eq _ _ _ (coordinates a)]
  simp [coordinate, theta, add_right_comm]

private theorem boseResidue_iff (r : Fin 48) :
    BoseResidue (F := ZMod 7) theta 5 r ↔
      ∃ a : ZMod 7, r.val = (5 * (lineExponent a).val) % 48 := by
  constructor
  · rintro ⟨e, hr, a, ha⟩
    have heq : e.val = (lineExponent a).val := by
      have hfin : IsOfFinOrder theta := isOfFinOrder_iff_pow_eq_one.mpr
        ⟨48, by decide, by simpa only [theta_order] using pow_orderOf_eq_one theta⟩
      have he := hfin.pow_inj_mod.mp (ha.trans (lineExponent_spec a).symm)
      simpa [theta_order, Nat.mod_eq_of_lt e.isLt, Nat.mod_eq_of_lt (lineExponent a).isLt]
        using he
    exact ⟨a, hr.trans (congrArg (fun i => 5 * i % 48) heq)⟩
  · rintro ⟨a, ha⟩
    exact ⟨lineExponent a, ha, a, lineExponent_spec a⟩

private def boseGaps : Fin 6 → ℕ := ![9, 3, 10, 1, 4, 2]

private def boseShorter : Fin 6 → ℚ := ![17 / 2, 3, 19 / 2, 1, 4, 2]

private theorem boseCut :
    LargestGapCut (BoseResidue (F := ZMod 7) theta 5) (30 : Fin 48) boseGaps := by
  unfold LargestGapCut
  simp only [boseResidue_iff]
  decide

set_option maxHeartbeats 800000 in
private theorem bose_false : ¬ Bose := by
  intro h
  refine not_uniqueShortest_of_rat boseGaps boseShorter ?_ ?_
    (h 7 (ZMod 7) BoseField (Nat.card_zmod 7) boseField_card theta 5 theta_order
      (by decide) (30 : Fin 48) boseGaps boseCut)
  · unfold ChamberOrder
    decide +kernel
  · decide +kernel

/-- Each universal assertion has a strictly shorter ruler in the chamber of an
exact largest-gap cut. -/
theorem result : ¬ claim := by
  rintro (hbose | hruzsa)
  · exact bose_false hbose
  · exact ruzsa_false hruzsa

end D5.S3.Geometry.FiniteGeometry.NotikBoseRuzsaChamber
