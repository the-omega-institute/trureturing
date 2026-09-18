/- GID: D5/S3/ArithSums/AgohAlternatingNumeratorRefutation
   generality: I
   mirror-B: D5/B/S3/ArithSums/AgohAlternatingNumeratorRefutation
   mirror-E: none(waiver:universal-algebraic-proof)
   anchors: [mathlib/module/Mathlib.FieldTheory.RatFunc.Basic, mathlib/module/Mathlib.RingTheory.Polynomial.Vieta]
   utility: none
   digest: A repeated real root does not obstruct the all-order alternating reduced-numerator factor. -/

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Pi
import D5.S3.ConceptDynamics.InformationEscape.AgohCoefficientReadoutTemplate
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial Finset
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.AgohCoefficientReadoutTemplate
open LeanInformationAudit

namespace D5.S3.ArithSums.AgohAlternatingNumeratorRefutation

noncomputable section

/-- The literal alternating rational function in Equation (3.1). -/
def Q (f : ℝ[X]) (n : ℕ) : RatFunc ℝ :=
  ∑ i ∈ range (n + 1), ((-1 : RatFunc ℝ) ^ i * (n.choose i : RatFunc ℝ)) /
    algebraMap ℝ[X] (RatFunc ℝ) (f.comp (X ^ i))

def NumeratorProperty (f : ℝ[X]) : Prop :=
  ∀ n : ℕ, (X - C (1 : ℝ)) ^ n ∣ (Q f n).num

def IsMonomial (f : ℝ[X]) : Prop :=
  ∃ (d : ℕ) (a : ℝ), a ≠ 0 ∧ f = monomial d a

def SimpleRootsAwayFromOne (f : ℝ[X]) : Prop :=
  ∀ a : ℝ, f.IsRoot a → f.rootMultiplicity a = 1 ∧ a ≠ 1

/-- The full printed conjecture, with its all-n property inside the equivalence. -/
def fullClaim : Prop :=
  ∀ f : ℝ[X], f ≠ 0 → f.Splits →
    (NumeratorProperty f ↔ IsMonomial f ∨ SimpleRootsAwayFromOne f)

private def factors (f : ℝ[X]) (i : ℕ) : ℝ[X] := f.comp (X ^ i)

private def commonDenominator (f : ℝ[X]) (n : ℕ) : ℝ[X] :=
  ∏ i ∈ range (n + 1), factors f i

private def commonNumerator (f : ℝ[X]) (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range (n + 1), (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
    ∏ j ∈ (range (n + 1)).erase i, factors f j

-- A coefficient telescoping identity implements indexed deletion, not value erasure.
private theorem deletion_telescope {R : Type} [CommRing R]
    (a : R) (q : R[X]) (n : ℕ) :
    (∑ k ∈ range (n + 1), (-a) ^ k * ((X + C a) * q).coeff (k + 1)) =
      q.coeff 0 + a * (-a) ^ n * q.coeff (n + 1) := by
  have recurrence (k : ℕ) : ((X + C a) * q).coeff (k + 1) =
      q.coeff k + a * q.coeff (k + 1) := by
    rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]
  induction n with
  | zero => simp [recurrence]
  | succ n ih =>
    rw [sum_range_succ, ih, recurrence, pow_succ]
    ring

private theorem indexed_deletion (n i : ℕ) (hi : i ∈ range (n + 1))
    (t : ℕ → ℝ[X]) :
    (∏ j ∈ (range (n + 1)).erase i, t j) =
      ∑ k ∈ range (n + 1), (-t i) ^ k *
        ((∏ j ∈ range (n + 1), (X + C (t j))) : (ℝ[X])[X]).coeff (k + 1) := by
  let s := (range (n + 1)).erase i
  let q : (ℝ[X])[X] := ∏ j ∈ s, (X + C (t j))
  have hcard : s.card = n := by simp [s, card_erase_of_mem hi]
  have hdegree : q.natDegree ≤ n := by
    calc
      q.natDegree ≤ ∑ j ∈ s, ((X + C (t j)) : (ℝ[X])[X]).natDegree := natDegree_prod_le _ _
      _ = n := by simp [hcard]
  have htop : q.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hprod : (∏ j ∈ range (n + 1), (X + C (t j))) = (X + C (t i)) * q := by
    exact (mul_prod_erase (range (n + 1)) (fun j => X + C (t j)) hi).symm
  rw [hprod, deletion_telescope, htop, mul_zero, add_zero]
  rw [coeff_zero_eq_eval_zero]
  simp [q, s, eval_prod]

private theorem finite_difference (p : ℝ[X]) (n : ℕ) :
    (∑ i ∈ range (n + 1), (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
      p.comp (X ^ i)) =
    ∑ r ∈ p.support, C (p.coeff r) * (1 - X ^ r) ^ n := by
  simp_rw [comp_eq_sum_left, Polynomial.sum_def, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  have binomial :
      (∑ i ∈ range (n + 1), (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
        (X ^ i) ^ r) = (1 - X ^ r) ^ n := by
    have h := add_pow (- (X ^ r : ℝ[X])) 1 n
    simp only [one_pow, mul_one] at h
    rw [show -(X ^ r : ℝ[X]) + 1 = 1 - X ^ r by ring] at h
    rw [h]
    apply sum_congr rfl
    intro i hi
    rw [neg_pow (X ^ r : ℝ[X]) i]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm i r]
    ring
  rw [← binomial, mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

private theorem common_numerator_divisible (f : ℝ[X]) (n : ℕ) :
    (X - C (1 : ℝ)) ^ n ∣ commonNumerator f n := by
  have difference_dvd (p : ℝ[X]) :
      (X - C (1 : ℝ)) ^ n ∣
        ∑ i ∈ range (n + 1), (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
          p.comp (X ^ i) := by
    rw [finite_difference]
    apply Finset.dvd_sum
    intro r hr
    apply dvd_mul_of_dvd_right
    apply pow_dvd_pow_of_dvd
    apply (dvd_iff_isRoot).mpr
    simp [IsRoot]
  let e : ℕ → ℝ[X] := fun k =>
    ((range (n + 1)).val.map (factors f)).esymm (n - k)
  have symmetric_coefficient (k : ℕ) (hk : k ∈ range (n + 1)) :
      ((∏ j ∈ range (n + 1), (X + C (factors f j))) : (ℝ[X])[X]).coeff (k + 1) =
        e k := by
    have bound : k + 1 ≤ (range (n + 1)).val.card := by
      simp only [card_val, card_range]
      have := mem_range.mp hk
      omega
    have h := Multiset.prod_X_add_C_coeff' (range (n + 1)).val (factors f) bound
    simpa only [Finset.prod, card_val, card_range, Nat.add_sub_add_right, e] using h
  have expansion : commonNumerator f n =
      ∑ k ∈ range (n + 1), (-1 : ℝ[X]) ^ k * e k *
        ∑ i ∈ range (n + 1), (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
          (f ^ k).comp (X ^ i) := by
    unfold commonNumerator
    calc
      _ = ∑ i ∈ range (n + 1), ∑ k ∈ range (n + 1),
          (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
            ((-factors f i) ^ k * e k) := by
        apply sum_congr rfl
        intro i hi
        rw [indexed_deletion n i hi, mul_sum]
        apply sum_congr rfl
        intro k hk
        rw [symmetric_coefficient k hk]
      _ = _ := ?_
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [neg_pow (factors f i) k]
    simp only [pow_comp, factors]
    ring
  rw [expansion]
  apply Finset.dvd_sum
  intro k hk
  exact dvd_mul_of_dvd_right (difference_dvd (f ^ k)) _

private theorem reduced_numerator_divisible (f : ℝ[X]) (hf : f.eval 1 = 1) :
    NumeratorProperty f := by
  intro n
  have factor_eval (i : ℕ) : (factors f i).eval 1 = 1 := by
    simpa [factors, eval_comp] using hf
  have ht (i : ℕ) : factors f i ≠ 0 := by
    intro h
    have := factor_eval i
    rw [h, eval_zero] at this
    exact zero_ne_one this
  have evalD : (commonDenominator f n).eval 1 = 1 := by
    simp [commonDenominator, eval_prod, factor_eval]
  have hD : commonDenominator f n ≠ 0 := by
    intro h
    rw [h, eval_zero] at evalD
    exact zero_ne_one evalD
  have fraction : Q f n =
      algebraMap ℝ[X] (RatFunc ℝ) (commonNumerator f n) /
        algebraMap ℝ[X] (RatFunc ℝ) (commonDenominator f n) := by
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero hD)).mpr
    unfold Q commonNumerator
    rw [sum_mul, map_sum]
    apply sum_congr rfl
    intro i hi
    have delete : commonDenominator f n = factors f i *
        ∏ j ∈ (range (n + 1)).erase i, factors f j :=
      (mul_prod_erase (range (n + 1)) (factors f) hi).symm
    rw [delete]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, factors]
    have hti : algebraMap ℝ[X] (RatFunc ℝ) (f.comp (X ^ i)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (ht i)
    field_simp [hti]
  have actual_num := (RatFunc.num_mul_eq_mul_denom_iff hD).mpr fraction
  have coprime : IsCoprime (X - C (1 : ℝ)) (commonDenominator f n) := by
    obtain ⟨g, hg⟩ := (X_sub_C_dvd_sub_C_eval :
      X - C (1 : ℝ) ∣ commonDenominator f n - C ((commonDenominator f n).eval 1))
    rw [evalD, C_1] at hg
    refine ⟨-g, 1, ?_⟩
    rw [one_mul]
    calc
      -g * (X - C 1) + commonDenominator f n =
          commonDenominator f n - (X - C 1) * g := by ring
      _ = 1 := by rw [C_1, ← hg]; ring
  apply (coprime.pow_left (m := n)).dvd_of_dvd_mul_right
  rw [actual_num]
  exact dvd_mul_of_dvd_left (common_numerator_divisible f n) _

abbrev CoefficientWord := Fin 3 → Fin 9

def actualWord : CoefficientWord := fun i =>
  if i.val = 0 then 8 else if i.val = 1 then 0 else 5

def decodeCode (code : Fin 9) : ℝ := (code.val : ℝ) - 4

def polynomialOfWord (word : CoefficientWord) : ℝ[X] :=
  ∑ i : Fin 3, C (decodeCode (word i)) * X ^ i.val

structure CounterexampleCertificate (word : CoefficientWord) : Prop where
  nonzero : polynomialOfWord word ≠ 0
  splits : (polynomialOfWord word).Splits
  nonconstant : ¬ ∃ a : ℝ, polynomialOfWord word = C a
  valueAtOne : (polynomialOfWord word).eval 1 = 1
  allOrders : NumeratorProperty (polynomialOfWord word)
  notMonomial : ¬ IsMonomial (polynomialOfWord word)
  notSimple : ¬ SimpleRootsAwayFromOne (polynomialOfWord word)

private theorem actual_certificate : CounterexampleCertificate actualWord := by
  have poly : polynomialOfWord actualWord = (X - C (2 : ℝ)) ^ 2 := by
    rw [polynomialOfWord, Fin.sum_univ_three]
    norm_num [actualWord, decodeCode]
    simp only [C_ofNat]
    ring
  have coefficients :
      (polynomialOfWord actualWord).coeff 0 = 4 ∧
      (polynomialOfWord actualWord).coeff 1 = -4 := by
    rw [polynomialOfWord, Fin.sum_univ_three]
    norm_num [actualWord, decodeCode, coeff_add, coeff_C_mul_X_pow]
  have eval_one : (polynomialOfWord actualWord).eval 1 = 1 := by
    rw [poly]
    norm_num
  refine ⟨?_, ?_, ?_, eval_one, reduced_numerator_divisible _ eval_one, ?_, ?_⟩
  · rw [poly]
    exact pow_ne_zero _ (X_sub_C_ne_zero 2)
  · rw [poly]
    exact (Splits.X_sub_C 2).pow 2
  · rintro ⟨a, ha⟩
    have h := coefficients.2
    rw [ha, coeff_C] at h
    norm_num at h
  · rintro ⟨d, a, ha, hpoly⟩
    have hzero := coefficients.1
    have hone := coefficients.2
    rw [hpoly, coeff_monomial] at hzero hone
    by_cases hd : d = 0
    · subst d
      norm_num at hone
    · simp [hd] at hzero
  · intro simple
    have root : (polynomialOfWord actualWord).IsRoot 2 := by
      rw [poly]
      norm_num [IsRoot]
    have h := (simple 2 root).1
    rw [poly, rootMultiplicity_X_sub_C_pow] at h
    norm_num at h

/-- The complete conjecture is false, retaining the actual coefficient word. -/
theorem result : (let counterexample := actualWord; Not fullClaim) := by
  change ¬ fullClaim
  intro claim
  have certificate := actual_certificate
  have h := (claim (polynomialOfWord actualWord) certificate.nonzero certificate.splits).mp
    certificate.allOrders
  exact h.elim certificate.notMonomial certificate.notSimple

def coefficientArena : PrimitiveLawArena where
  toArena := Arena.ofFintype CoefficientWord
  signature := coefficientSignature CoefficientWord
  Law realization :=
    let readWord : CoefficientWord := fun index => realization.readout index actualWord
    readWord = actualWord ∧ CounterexampleCertificate readWord

local instance : DecidableEq CoefficientWord := inferInstance
local instance : DecidableEq coefficientArena.State := coefficientArena.toArena.stateDecidableEq

def actualRealization :=
  coefficientRealization (S := CoefficientWord)
    (fun (word : CoefficientWord) (index : Fin 3) => word index)

private def bumpCode (code : Fin 9) : Fin 9 :=
  ⟨(code.val + 1) % 9, Nat.mod_lt _ (by omega)⟩

private theorem bumpCode_ne (code : Fin 9) : bumpCode code ≠ code := by
  fin_cases code <;> decide

private def alteredRealization (changed : Fin 3) :
    PrimitiveRealization coefficientArena.signature :=
  coefficientRealization fun word index =>
    if index = changed then bumpCode (word index) else word index

private theorem coefficient_law : coefficientArena.Law actualRealization := by
  exact ⟨rfl, actual_certificate⟩

private theorem altered_not_law (changed : Fin 3) :
    ¬ coefficientArena.Law (alteredRealization changed) := by
  rintro ⟨equality, _⟩
  have atChanged := congrFun equality changed
  apply bumpCode_ne (actualWord changed)
  simpa [alteredRealization, coefficientRealization, coefficientSignature] using atChanged

private theorem coefficient_bridge : LegacyPrimitiveRealization coefficientArena
    (let counterexample := actualWord; Not fullClaim) actualRealization := by
  constructor
  constructor
  · intro _
    exact coefficient_law
  · rintro ⟨_, certificate⟩
    intro claim
    have h := (claim _ certificate.nonzero certificate.splits).mp certificate.allOrders
    exact h.elim certificate.notMonomial certificate.notSimple

private theorem coefficient_variation : FiniteLawVariation coefficientArena := by
  exact ⟨actualRealization, alteredRealization 0, coefficient_law, altered_not_law 0⟩

private theorem coefficient_sensitivity : FiniteSlotSensitivity coefficientArena := by
  classical
  constructor
  · intro i
    refine ⟨actualRealization, alteredRealization i, ?_, ?_, ?_⟩
    · intro j hne
      change Fin 3 at i j
      funext word
      change CoefficientWord at word
      change word j = if j = i then bumpCode (word j) else word j
      split
      · next h => exact (hne h).elim
      · rfl
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => altered_not_law i, fun _ => coefficient_law⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem result in coefficientArena
  readout via (@coefficientRealization CoefficientWord (fun word index => word index))
  primitives actualRealization.toPrimitiveBundle realization coefficient_bridge
  variation coefficient_variation sensitivity coefficient_sensitivity
  escape from (actualWord) escape continues (open)

end
end D5.S3.ArithSums.AgohAlternatingNumeratorRefutation
