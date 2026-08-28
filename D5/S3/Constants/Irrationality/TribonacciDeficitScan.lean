/- GID: D5/S3/Constants/Irrationality/TribonacciDeficitScan
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/TribonacciDeficitScan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The source-normalized Tribonacci deficit has an exact nonintegral finite spectrum. -/

import D5.S0.Tower.Champions.DecimalBounds
import D5.S0.Tower.Champions.CodingFingerprint
import D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
import D5.S0.Tower.Tribonacci.Representation
import D5.S3.Constants.Irrationality.TribonacciIrrationality

/- Library-search audit trail (2026-08-26):
   * Repository object searches found the canonical no-`111` representation in
     `Tribonacci.Representation`, the Binet coefficient in `Tribonacci.Binet`,
     and exact rational cubic arithmetic in `TribonacciPeriodicGenerator`.
     Those declarations are imported and used directly below.
   * The normalization is not reconstructed from a decimal: the exact bridge
     `tribonacci_binet_normalization_bridge` in `CodingFingerprint` identifies
     the source's shifted coefficient with the frozen Binet coefficient.
   * The pinned Mathlib search found generic algebraic-integer trace results
     (`Algebra.isIntegral_trace`, `IsIntegrallyClosed.isIntegral_iff`, and
     `trace_eq_sum_roots`) but no Tribonacci object.  They do not discharge the
     finite single-real-embedding certificate here, so the existing exact cubic
     code is the thinner dependency.
   * GitHub code search required authentication, GitHub's HTML search required
     sign-in, and DuckDuckGo returned a bot challenge.  Reservoir was reachable
     but exposed no reusable code-level Tribonacci result. -/

namespace D5.S3.Constants.Irrationality.TribonacciDeficitScan

set_option maxRecDepth 500000

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.Binet
open D5.S0.Tower.Tribonacci.Representation
open D5.S0.Tower.DBonacciGeneral.TribonacciPeriodicGenerator
open D5.S3.Constants.Irrationality.TribonacciIrrationality

local notation "t" => tribonacciConstant

/-! ### Canonical indexing and the source-normalized Binet face -/

/-- The frozen Tribonacci weights eventually dominate their own index. -/
theorem nat_lt_tribonacci_diagonal (n : Nat) : n < tribonacci (n + 3) := by
  induction n with
  | zero => norm_num [tribonacci]
  | succ n ih =>
      have hrec := tribonacci_add_three (n + 1)
      have hpos := tribonacci_level_pos n
      simp only [Nat.add_assoc, Nat.reduceAdd] at hrec ⊢
      omega

/-- The canonical no-`111` name of a natural number, at a layer large enough
to represent that number. -/
noncomputable def tribonacciCanonicalName (n : Nat) : TribonacciName (n + 1) :=
  encode (n + 1) ⟨n, by simpa only [Nat.add_assoc, Nat.reduceAdd] using
    nat_lt_tribonacci_diagonal n⟩

@[simp] theorem decode_tribonacciCanonicalName (n : Nat) :
    decode (tribonacciCanonicalName n) = n := by
  rw [tribonacciCanonicalName, decode_encode]

/-- The digit polynomial of an admissible name, evaluated at the Perron root. -/
noncomputable def tribonacciDigitPolynomial {Q : Nat} (name : TribonacciName Q) : Real :=
  ∑ i : Fin Q, if name.1 i then t ^ i.1 else 0

/-- The Binet leading-term value of a name in the source's indexing convention.
The first occupied digit contributes `a * t^3`, where `a` is the coefficient
of `t^n` in the frozen Tribonacci sequence. -/
noncomputable def tribonacciBinetNameValue {Q : Nat} (name : TribonacciName Q) : Real :=
  tribonacciBinetCoefficient * t ^ 3 * tribonacciDigitPolynomial name

/-- The factored definition is the source's shifted Binet coefficient times
`t^2`, using the existing normalization bridge rather than a second proof. -/
theorem tribonacciBinetNameValue_eq_source_normalization {Q : Nat}
    (name : TribonacciName Q) :
    tribonacciBinetNameValue name =
      (t ^ 2 / (3 * t ^ 2 - 2 * t - 1)) * t ^ 2 *
        tribonacciDigitPolynomial name := by
  rw [tribonacciBinetNameValue,
    D5.S0.Tower.Champions.CodingFingerprint.tribonacci_binet_normalization_bridge]
  ring

/-- The factored definition is exactly the sum of the occupied Binet main terms. -/
theorem tribonacciBinetNameValue_eq_sum {Q : Nat} (name : TribonacciName Q) :
    tribonacciBinetNameValue name =
      ∑ i : Fin Q, if name.1 i then tribonacciBinetCoefficient * t ^ (i.1 + 3) else 0 := by
  rw [tribonacciBinetNameValue, tribonacciDigitPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split
  · rw [pow_add]
    ring
  · ring

/-- The source-normalized Binet reading of a natural number. -/
noncomputable def tribonacciBetaReal (n : Nat) : Real :=
  tribonacciBinetNameValue (tribonacciCanonicalName n)

/-- The addition deficit on the expanding Tribonacci face. -/
noncomputable def tribonacciDeficit (v₁ v₂ : Nat) : Real :=
  tribonacciBetaReal v₁ + tribonacciBetaReal v₂ - tribonacciBetaReal (v₁ + v₂)

/-! ### Exact cubic code for the same Binet face -/

/-- Exact code for the source normalization `a * t^3`. -/
def tribonacciBinetScaleCode : TribonacciCubicCode :=
  ⟨3 / 22, 5 / 22, 5 / 11⟩

/-- Powers of the Perron root in the existing exact cubic code. -/
def tribonacciCodePow : Nat → TribonacciCubicCode
  | 0 => tribonacciCodeOne
  | n + 1 => tribonacciCodeMul (tribonacciCodePow n) tribonacciCodeRoot

/-- The computable greedy digit polynomial at a fixed name layer. -/
def tribonacciGreedyCode : Nat → Nat → TribonacciCubicCode
  | 0, _ => tribonacciCodeZero
  | Q + 1, n =>
      if tribonacci (Q + 2) ≤ n then
        tribonacciCodeAdd (tribonacciGreedyCode Q (n - tribonacci (Q + 2)))
          (tribonacciCodePow Q)
      else
        tribonacciGreedyCode Q n

/-- Exact deficit code at a common representation layer. -/
def tribonacciDeficitCodeAt (Q v₁ v₂ : Nat) : TribonacciCubicCode :=
  tribonacciCodeMul tribonacciBinetScaleCode
    (tribonacciCodeSub
      (tribonacciCodeAdd (tribonacciGreedyCode Q v₁) (tribonacciGreedyCode Q v₂))
      (tribonacciGreedyCode Q (v₁ + v₂)))

theorem tribonacci_code_pow_value (n : Nat) :
    tribonacciCodeValue (tribonacciCodePow n) = t ^ n := by
  induction n with
  | zero => norm_num [tribonacciCodePow, tribonacciCodeValue, tribonacciCodeOne]
  | succ n ih =>
      rw [tribonacciCodePow, tribonacci_code_value_mul, ih]
      norm_num [tribonacciCodeValue, tribonacciCodeRoot, pow_succ]

/-- The rational triple for the source normalization evaluates to `a * t^3`. -/
theorem tribonacci_binet_scale_code_value :
    tribonacciCodeValue tribonacciBinetScaleCode = tribonacciBinetCoefficient * t ^ 3 := by
  have hden : t ^ 2 + 2 * t + 3 ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hcubic := tribonacciConstant_cubic
  have hfour : t ^ 4 = 2 * t ^ 2 + 2 * t + 1 := by
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ = t * (t ^ 2 + t + 1) := by rw [hcubic]
      _ = 2 * t ^ 2 + 2 * t + 1 := by nlinarith [hcubic]
  have hfive : t ^ 5 = 4 * t ^ 2 + 3 * t + 2 := by
    calc
      t ^ 5 = t * t ^ 4 := by ring
      _ = t * (2 * t ^ 2 + 2 * t + 1) := by rw [hfour]
      _ = 4 * t ^ 2 + 3 * t + 2 := by nlinarith [hcubic]
  calc
    tribonacciCodeValue tribonacciBinetScaleCode =
        (3 + 5 * t + 10 * t ^ 2) / 22 := by
      norm_num [tribonacciCodeValue, tribonacciBinetScaleCode]
      ring
    _ = tribonacciBinetCoefficient * t ^ 3 := by
      rw [tribonacciBinetCoefficient]
      rw [show t ^ 2 / (t ^ 2 + 2 * t + 3) * t ^ 3 =
          t ^ 5 / (t ^ 2 + 2 * t + 3) by ring, hfive]
      rw [div_eq_div_iff (by norm_num : (22 : Real) ≠ 0) hden]
      linear_combination 25 * hcubic + 10 * hfour

theorem tribonacci_digit_polynomial_snoc {Q : Nat} (name : TribonacciName (Q + 1)) :
    tribonacciDigitPolynomial name = tribonacciDigitPolynomial (initName name) +
      if name.1 (Fin.last Q) then t ^ Q else 0 := by
  rw [tribonacciDigitPolynomial, tribonacciDigitPolynomial, Fin.sum_univ_castSucc]
  rfl

/-- The computable greedy code is the digit polynomial of the canonical
representation supplied by `Representation.encode`. -/
theorem tribonacci_greedy_code_value_encode (Q : Nat)
    (n : Fin (tribonacci (Q + 2))) :
    tribonacciCodeValue (tribonacciGreedyCode Q n.1) =
      tribonacciDigitPolynomial (encode Q n) := by
  induction Q with
  | zero =>
      simp [tribonacciGreedyCode, tribonacciDigitPolynomial, tribonacciCodeValue,
        tribonacciCodeZero]
  | succ Q ih =>
      let name := encode (Q + 1) n
      by_cases htop : tribonacci (Q + 2) ≤ n.1
      · have hlast : name.1 (Fin.last Q) = true := by
          exact (encode_last_eq_true_iff Q n).2 htop
        have hlast' : (encode (Q + 1) n).1 (Fin.last Q) = true := hlast
        have hdecode : decode (initName name) = n.1 - tribonacci (Q + 2) := by
          have hsplit := decode_snoc name
          rw [show decode name = n.1 by exact decode_encode (Q + 1) n, hlast] at hsplit
          simp only [if_true] at hsplit
          omega
        let lower : Fin (tribonacci (Q + 2)) :=
          ⟨n.1 - tribonacci (Q + 2), by
            rw [← hdecode]
            exact decode_lt_tribonacci Q (initName name)⟩
        have hinit : initName name = encode Q lower := by
          apply decode_injective Q
          rw [decode_encode]
          exact hdecode
        have hinit' : initName (encode (Q + 1) n) = encode Q lower := by
          exact hinit
        rw [tribonacciGreedyCode, if_pos htop, tribonacci_code_value_add,
          ih lower, tribonacci_code_pow_value, tribonacci_digit_polynomial_snoc,
          hinit']
        simp [hlast']
      · have hlast : name.1 (Fin.last Q) = false := by
          cases hvalue : name.1 (Fin.last Q) with
          | false => rfl
          | true =>
              exfalso
              exact htop ((encode_last_eq_true_iff Q n).1 hvalue)
        have hlast' : (encode (Q + 1) n).1 (Fin.last Q) = false := hlast
        have hnlow : n.1 < tribonacci (Q + 2) := Nat.lt_of_not_ge htop
        let lower : Fin (tribonacci (Q + 2)) := ⟨n.1, hnlow⟩
        have hdecode : decode (initName name) = n.1 := by
          have hsplit := decode_snoc name
          rw [show decode name = n.1 by exact decode_encode (Q + 1) n, hlast] at hsplit
          simpa using hsplit.symm
        have hinit : initName name = encode Q lower := by
          apply decode_injective Q
          rw [decode_encode]
          exact hdecode
        have hinit' : initName (encode (Q + 1) n) = encode Q lower := by
          exact hinit
        rw [tribonacciGreedyCode, if_neg htop, ih lower,
          tribonacci_digit_polynomial_snoc, hinit']
        simp [hlast']

/-- At every valid layer, the exact cubic code is the Binet leading-term value
of the encoded name. -/
theorem tribonacci_binet_name_value_eq_code (Q : Nat)
    (n : Fin (tribonacci (Q + 2))) :
    tribonacciBinetNameValue (encode Q n) =
      tribonacciCodeValue
        (tribonacciCodeMul tribonacciBinetScaleCode (tribonacciGreedyCode Q n.1)) := by
  rw [tribonacciBinetNameValue, tribonacci_code_value_mul,
    tribonacci_binet_scale_code_value, tribonacci_greedy_code_value_encode]

theorem tribonacci_step_strict (Q : Nat) :
    tribonacci (Q + 2) < tribonacci (Q + 3) := by
  cases Q with
  | zero => norm_num [tribonacci]
  | succ Q =>
      have hrec := tribonacci_add_three (Q + 1)
      have hpos := tribonacci_level_pos Q
      simp only [Nat.add_assoc, Nat.reduceAdd] at hrec ⊢
      omega

theorem tribonacci_layer_mono (Q extra : Nat) :
    tribonacci (Q + 2) ≤ tribonacci (Q + extra + 2) := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      exact ih.trans (by
        have := tribonacci_step_strict (Q + extra)
        simpa only [Nat.add_assoc, Nat.reduceAdd] using this.le)

theorem tribonacci_greedy_code_extend (Q extra n : Nat)
    (hn : n < tribonacci (Q + 2)) :
    tribonacciGreedyCode (Q + extra) n = tribonacciGreedyCode Q n := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [show Q + (extra + 1) = (Q + extra) + 1 by omega, tribonacciGreedyCode,
        if_neg]
      · exact ih
      · exact not_le.mpr (lt_of_lt_of_le hn (tribonacci_layer_mono Q extra))

theorem tribonacci_greedy_code_eq_of_le {Q R n : Nat} (hQR : Q ≤ R)
    (hn : n < tribonacci (Q + 2)) :
    tribonacciGreedyCode R n = tribonacciGreedyCode Q n := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hQR
  exact tribonacci_greedy_code_extend Q extra n hn

/-- On the scan range, the dynamic canonical layer and fixed layer ten have the
same digit polynomial. -/
theorem tribonacci_scan_code_stable {n : Nat} (hn : n ≤ 400) :
    tribonacciGreedyCode (n + 1) n = tribonacciGreedyCode 10 n := by
  by_cases hsmall : n + 1 ≤ 10
  · symm
    apply tribonacci_greedy_code_eq_of_le hsmall
    simpa only [Nat.add_assoc, Nat.reduceAdd] using nat_lt_tribonacci_diagonal n
  · apply tribonacci_greedy_code_eq_of_le (by omega)
    norm_num [tribonacci]
    omega

/-- The global Binet reading is represented by the fixed layer-ten code on the
entire scan range. -/
theorem tribonacci_beta_real_eq_scan_code {n : Nat} (hn : n ≤ 400) :
    tribonacciBetaReal n = tribonacciCodeValue
      (tribonacciCodeMul tribonacciBinetScaleCode (tribonacciGreedyCode 10 n)) := by
  rw [tribonacciBetaReal, tribonacciCanonicalName,
    tribonacci_binet_name_value_eq_code, tribonacci_scan_code_stable hn]

/-! ### Exact nonintegrality and finite scan certificate -/

/-- Integer coefficients in the basis `1, t, t^2`.  Scan computation stays in
this denominator-free basis; the bridge below maps it to the repository's
rational `TribonacciCubicCode`. -/
structure TribonacciIntegralCode where
  rational : Int
  linear : Int
  quadratic : Int
  deriving DecidableEq

def tribonacciIntegralCodeZero : TribonacciIntegralCode := ⟨0, 0, 0⟩

def tribonacciIntegralCodeOne : TribonacciIntegralCode := ⟨1, 0, 0⟩

def tribonacciIntegralCodeRoot : TribonacciIntegralCode := ⟨0, 1, 0⟩

def tribonacciIntegralCodeAdd
    (x y : TribonacciIntegralCode) : TribonacciIntegralCode :=
  ⟨x.rational + y.rational, x.linear + y.linear, x.quadratic + y.quadratic⟩

def tribonacciIntegralCodeNeg (x : TribonacciIntegralCode) : TribonacciIntegralCode :=
  ⟨-x.rational, -x.linear, -x.quadratic⟩

def tribonacciIntegralCodeSub
    (x y : TribonacciIntegralCode) : TribonacciIntegralCode :=
  tribonacciIntegralCodeAdd x (tribonacciIntegralCodeNeg y)

/-- Multiplication reduced by `t^3 = t^2 + t + 1`, over integer coefficients. -/
def tribonacciIntegralCodeMul
    (x y : TribonacciIntegralCode) : TribonacciIntegralCode :=
  let r0 := x.rational * y.rational
  let r1 := x.rational * y.linear + x.linear * y.rational
  let r2 := x.rational * y.quadratic + x.linear * y.linear + x.quadratic * y.rational
  let r3 := x.linear * y.quadratic + x.quadratic * y.linear
  let r4 := x.quadratic * y.quadratic
  ⟨r0 + r3 + r4, r1 + r3 + 2 * r4, r2 + r3 + 2 * r4⟩

def tribonacciIntegralCodePow : Nat → TribonacciIntegralCode
  | 0 => tribonacciIntegralCodeOne
  | n + 1 => tribonacciIntegralCodeMul
      (tribonacciIntegralCodePow n) tribonacciIntegralCodeRoot

def tribonacciIntegralGreedyCode : Nat → Nat → TribonacciIntegralCode
  | 0, _ => tribonacciIntegralCodeZero
  | Q + 1, n =>
      if tribonacci (Q + 2) ≤ n then
        tribonacciIntegralCodeAdd
          (tribonacciIntegralGreedyCode Q (n - tribonacci (Q + 2)))
          (tribonacciIntegralCodePow Q)
      else
        tribonacciIntegralGreedyCode Q n

def tribonacciIntegralDeficitAt (Q v₁ v₂ : Nat) : TribonacciIntegralCode :=
  tribonacciIntegralCodeSub
    (tribonacciIntegralCodeAdd
      (tribonacciIntegralGreedyCode Q v₁) (tribonacciIntegralGreedyCode Q v₂))
    (tribonacciIntegralGreedyCode Q (v₁ + v₂))

def tribonacciIntegralCodeToCubic (x : TribonacciIntegralCode) : TribonacciCubicCode :=
  ⟨x.rational, x.linear, x.quadratic⟩

theorem tribonacci_integral_code_to_cubic_add (x y : TribonacciIntegralCode) :
    tribonacciIntegralCodeToCubic (tribonacciIntegralCodeAdd x y) =
      tribonacciCodeAdd (tribonacciIntegralCodeToCubic x)
        (tribonacciIntegralCodeToCubic y) := by
  ext <;> simp [tribonacciIntegralCodeToCubic, tribonacciIntegralCodeAdd,
    tribonacciCodeAdd]

theorem tribonacci_integral_code_to_cubic_neg (x : TribonacciIntegralCode) :
    tribonacciIntegralCodeToCubic (tribonacciIntegralCodeNeg x) =
      tribonacciCodeNeg (tribonacciIntegralCodeToCubic x) := by
  ext <;> simp [tribonacciIntegralCodeToCubic, tribonacciIntegralCodeNeg,
    tribonacciCodeNeg]

theorem tribonacci_integral_code_to_cubic_sub (x y : TribonacciIntegralCode) :
    tribonacciIntegralCodeToCubic (tribonacciIntegralCodeSub x y) =
      tribonacciCodeSub (tribonacciIntegralCodeToCubic x)
        (tribonacciIntegralCodeToCubic y) := by
  rw [tribonacciIntegralCodeSub, tribonacciCodeSub,
    tribonacci_integral_code_to_cubic_add, tribonacci_integral_code_to_cubic_neg]

theorem tribonacci_integral_code_to_cubic_mul (x y : TribonacciIntegralCode) :
    tribonacciIntegralCodeToCubic (tribonacciIntegralCodeMul x y) =
      tribonacciCodeMul (tribonacciIntegralCodeToCubic x)
        (tribonacciIntegralCodeToCubic y) := by
  ext <;> simp [tribonacciIntegralCodeToCubic, tribonacciIntegralCodeMul,
    tribonacciCodeMul]

theorem tribonacci_integral_code_pow_to_cubic (n : Nat) :
    tribonacciIntegralCodeToCubic (tribonacciIntegralCodePow n) =
      tribonacciCodePow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [tribonacciIntegralCodePow, tribonacciCodePow,
        tribonacci_integral_code_to_cubic_mul, ih]
      rfl

theorem tribonacci_integral_greedy_code_to_cubic (Q n : Nat) :
    tribonacciIntegralCodeToCubic (tribonacciIntegralGreedyCode Q n) =
      tribonacciGreedyCode Q n := by
  induction Q generalizing n with
  | zero => rfl
  | succ Q ih =>
      simp only [tribonacciIntegralGreedyCode, tribonacciGreedyCode]
      split
      · rw [tribonacci_integral_code_to_cubic_add, ih,
          tribonacci_integral_code_pow_to_cubic]
      · exact ih _

theorem tribonacci_integral_deficit_to_cubic (Q v₁ v₂ : Nat) :
    tribonacciIntegralCodeToCubic (tribonacciIntegralDeficitAt Q v₁ v₂) =
      tribonacciCodeSub
        (tribonacciCodeAdd (tribonacciGreedyCode Q v₁) (tribonacciGreedyCode Q v₂))
        (tribonacciGreedyCode Q (v₁ + v₂)) := by
  rw [tribonacciIntegralDeficitAt, tribonacci_integral_code_to_cubic_sub,
    tribonacci_integral_code_to_cubic_add,
    tribonacci_integral_greedy_code_to_cubic,
    tribonacci_integral_greedy_code_to_cubic,
    tribonacci_integral_greedy_code_to_cubic]

/-- The ten weights and reduced powers used by the fixed scan layer. -/
def tribonacciIntegralGreedyTable10 : List (Nat × TribonacciIntegralCode) :=
  [
    (274, ⟨24, 37, 44⟩),
    (149, ⟨13, 20, 24⟩),
    (81, ⟨7, 11, 13⟩),
    (44, ⟨4, 6, 7⟩),
    (24, ⟨2, 3, 4⟩),
    (13, ⟨1, 2, 2⟩),
    (7, ⟨1, 1, 1⟩),
    (4, ⟨0, 0, 1⟩),
    (2, ⟨0, 1, 0⟩),
    (1, ⟨1, 0, 0⟩)
  ]

def tribonacciIntegralGreedyFromTable :
    List (Nat × TribonacciIntegralCode) → Nat → TribonacciIntegralCode
  | [], _ => tribonacciIntegralCodeZero
  | (weight, code) :: rest, n =>
      if weight ≤ n then
        tribonacciIntegralCodeAdd
          (tribonacciIntegralGreedyFromTable rest (n - weight)) code
      else
        tribonacciIntegralGreedyFromTable rest n

/-- A scan evaluator with the fixed powers precomputed. -/
def tribonacciIntegralGreedyCode10 (n : Nat) : TribonacciIntegralCode :=
  tribonacciIntegralGreedyFromTable tribonacciIntegralGreedyTable10 n

/-- The extra reduction budget normalizes the ten symbolic branches once.  The
table evaluator is definitionally the generic layer-ten evaluator after
the ten frozen Tribonacci weights and powers are normalized. -/
theorem tribonacci_integral_greedy_code_10_eq (n : Nat) :
    tribonacciIntegralGreedyCode10 n = tribonacciIntegralGreedyCode 10 n := by
  rfl

def tribonacciIntegralDeficit10 (v₁ v₂ : Nat) : TribonacciIntegralCode :=
  tribonacciIntegralCodeSub
    (tribonacciIntegralCodeAdd
      (tribonacciIntegralGreedyCode10 v₁) (tribonacciIntegralGreedyCode10 v₂))
    (tribonacciIntegralGreedyCode10 (v₁ + v₂))

theorem tribonacci_integral_deficit_10_eq (v₁ v₂ : Nat) :
    tribonacciIntegralDeficit10 v₁ v₂ =
      tribonacciIntegralDeficitAt 10 v₁ v₂ := by
  simp [tribonacciIntegralDeficit10, tribonacciIntegralDeficitAt,
    tribonacci_integral_greedy_code_10_eq]

/-- Numerators after multiplying an integral digit deficit by
`(3 + 5*t + 10*t^2) / 22`. -/
def tribonacciScaledNumerator (x : TribonacciIntegralCode) : TribonacciIntegralCode :=
  ⟨3 * x.rational + 10 * x.linear + 15 * x.quadratic,
    5 * x.rational + 13 * x.linear + 25 * x.quadratic,
    10 * x.rational + 15 * x.linear + 28 * x.quadratic⟩

def tribonacciNumeratorToCubic (x : TribonacciIntegralCode) : TribonacciCubicCode :=
  ⟨x.rational / 22, x.linear / 22, x.quadratic / 22⟩

/-- The denominator-free scan code is exactly the existing rational cubic
deficit code. -/
theorem tribonacci_deficit_code_eq_numerator (Q v₁ v₂ : Nat) :
    tribonacciDeficitCodeAt Q v₁ v₂ =
      tribonacciNumeratorToCubic
        (tribonacciScaledNumerator (tribonacciIntegralDeficitAt Q v₁ v₂)) := by
  unfold tribonacciDeficitCodeAt
  rw [← tribonacci_integral_deficit_to_cubic]
  ext <;>
    norm_num [tribonacciBinetScaleCode, tribonacciCodeMul,
      tribonacciIntegralCodeToCubic, tribonacciScaledNumerator,
      tribonacciNumeratorToCubic] <;>
    ring

/-- The Tribonacci cubic has no rational root. -/
theorem no_rational_tribonacci_root (q : Rat) :
    (q : Real) ^ 3 ≠ (q : Real) ^ 2 + (q : Real) + 1 := by
  intro hroot
  have hden := cubic_rational_root_is_integer q hroot
  have hnum : (q.num : Rat) = q := Rat.coe_int_num_of_den_eq_one hden
  have hrootRat : (q.num : Rat) ^ 3 = (q.num : Rat) ^ 2 + q.num + 1 := by
    rw [hnum]
    exact_mod_cast hroot
  have hunit : q.num * (q.num ^ 2 - q.num - 1) = 1 := by
    exact_mod_cast (show (q.num : Rat) * (q.num ^ 2 - q.num - 1) = 1 by
      nlinarith [hrootRat])
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h
  · rw [h] at hrootRat
    norm_num at hrootRat
  · rw [h] at hrootRat
    norm_num at hrootRat

/-- A cubic code with a genuine quadratic coordinate cannot evaluate to an
integer at the Tribonacci root. -/
theorem tribonacci_code_value_not_integer_of_quadratic_ne_zero
    (x : TribonacciCubicCode) (hquadratic : x.quadratic ≠ 0) :
    ¬ ∃ z : Int, tribonacciCodeValue x = (z : Real) := by
  rintro ⟨z, hz⟩
  let c : Rat := x.quadratic
  let b : Rat := x.linear
  let d : Rat := x.rational - z
  have hc : c ≠ 0 := hquadratic
  have hquad : (c : Real) * t ^ 2 + (b : Real) * t + (d : Real) = 0 := by
    simp only [c, b, d, tribonacciCodeValue] at hz ⊢
    push_cast
    linarith
  have hcubicZero : t ^ 3 - t ^ 2 - t - 1 = 0 := by
    nlinarith [tribonacciConstant_cubic]
  have hshift : ((c + b : Rat) : Real) * t ^ 2 +
      ((c + d : Rat) : Real) * t + (c : Real) = 0 := by
    push_cast
    linear_combination t * hquad - (c : Real) * hcubicZero
  have hshift' : ((c : Real) + (b : Real)) * t ^ 2 +
      ((c : Real) + (d : Real)) * t + (c : Real) = 0 := by
    simpa only [Rat.cast_add] using hshift
  let linearCoefficient : Rat := c ^ 2 + c * d - b * c - b ^ 2
  let constantCoefficient : Rat := c ^ 2 - d * (c + b)
  have hlinear : (linearCoefficient : Real) * t + (constantCoefficient : Real) = 0 := by
    simp only [linearCoefficient, constantCoefficient]
    push_cast
    calc
      ((c : Real) ^ 2 + (c : Real) * (d : Real) -
            (b : Real) * (c : Real) - (b : Real) ^ 2) * t +
          ((c : Real) ^ 2 - (d : Real) * ((c : Real) + (b : Real))) =
        (c : Real) *
            (((c : Real) + (b : Real)) * t ^ 2 +
              ((c : Real) + (d : Real)) * t + (c : Real)) -
          ((c : Real) + (b : Real)) *
            ((c : Real) * t ^ 2 + (b : Real) * t + (d : Real)) := by ring
      _ = 0 := by rw [hshift', hquad]; ring
  by_cases hcoefficient : linearCoefficient = 0
  · have hconstant : constantCoefficient = 0 := by
      rw [hcoefficient, Rat.cast_zero, zero_mul, zero_add] at hlinear
      exact_mod_cast hlinear
    let q : Rat := (c + b) / c
    have hqroot : q ^ 3 = q ^ 2 + q + 1 := by
      have hlinearRat : c ^ 2 + c * d - b * c - b ^ 2 = 0 := by
        exact hcoefficient
      have hconstantRat : c ^ 2 - d * (c + b) = 0 := by
        exact hconstant
      dsimp [q]
      field_simp [hc]
      linear_combination -((c + b) * hlinearRat + c * hconstantRat)
    exact no_rational_tribonacci_root q (by exact_mod_cast hqroot)
  · have htRational : t = ((-constantCoefficient / linearCoefficient : Rat) : Real) := by
      rw [Rat.cast_div, Rat.cast_neg]
      apply (eq_div_iff (by exact_mod_cast hcoefficient)).2
      nlinarith [hlinear]
    exact tribonacciConstant_irrational.ne_rat
      (-constantCoefficient / linearCoefficient) htRational

/-- The exact triangular scan window `1 ≤ v₁ ≤ v₂ ≤ 200`. -/
def tribonacciScanPairs : Finset (Nat × Nat) :=
  ((Finset.range 201).product (Finset.range 201)).filter fun pair =>
    1 ≤ pair.1 ∧ pair.1 ≤ pair.2

theorem mem_tribonacciScanPairs_iff {pair : Nat × Nat} :
    pair ∈ tribonacciScanPairs ↔
      1 ≤ pair.1 ∧ pair.1 ≤ pair.2 ∧ pair.2 ≤ 200 := by
  rw [tribonacciScanPairs, Finset.mem_filter]
  constructor
  · intro h
    have hproduct := Finset.mem_product.mp h.1
    have hfirst := Finset.mem_range.mp hproduct.1
    have hsecond := Finset.mem_range.mp hproduct.2
    omega
  · intro h
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩,
      h.1, h.2.1⟩ <;> omega

/-- The scan's nonintegral pairs, decided by the exact quadratic coordinate. -/
def tribonacciNonintegralScanPairs : Finset (Nat × Nat) :=
  tribonacciScanPairs.filter fun pair =>
    (tribonacciScaledNumerator
      (tribonacciIntegralDeficit10 pair.1 pair.2)).quadratic ≠ 0

/-- The denominator-free form of the exact eight-point spectrum. -/
def tribonacciScanNumeratorSpectrum : Finset TribonacciIntegralCode :=
  {
    ⟨-9, -4, 3⟩,
    ⟨-5, -1, -2⟩,
    ⟨-4, -3, 5⟩,
    ⟨-1, 2, -7⟩,
    tribonacciIntegralCodeZero,
    ⟨1, -2, 7⟩,
    ⟨4, 3, -5⟩,
    ⟨5, 1, 2⟩
  }

/-- The eight exact values occurring in the scan, including zero. -/
def tribonacciScanSpectrum : Finset TribonacciCubicCode :=
  {
    ⟨-9 / 22, -2 / 11, 3 / 22⟩,
    ⟨-5 / 22, -1 / 22, -1 / 11⟩,
    ⟨-2 / 11, -3 / 22, 5 / 22⟩,
    ⟨-1 / 22, 1 / 11, -7 / 22⟩,
    tribonacciCodeZero,
    ⟨1 / 22, -1 / 11, 7 / 22⟩,
    ⟨2 / 11, 3 / 22, -5 / 22⟩,
    ⟨5 / 22, 1 / 22, 1 / 11⟩
  }

theorem tribonacci_scan_pair_count : tribonacciScanPairs.card = 20100 := by
  decide

/-- Number of nonintegral codes in the row with fixed first coordinate. -/
def tribonacciNonintegralRowCount (v₁ : Nat) : Nat :=
  ((Finset.Icc v₁ 200).filter fun v₂ =>
    (tribonacciScaledNumerator
      (tribonacciIntegralDeficit10 v₁ v₂)).quadratic ≠ 0).card

/-- Fiberwise counting rewrites the filtered triangular scan as a sum of row
counts. -/
theorem tribonacci_nonintegral_scan_card_eq_row_sum :
    tribonacciNonintegralScanPairs.card =
      ∑ v₁ ∈ Finset.Icc 1 200, tribonacciNonintegralRowCount v₁ := by
  classical
  have hmaps : (tribonacciNonintegralScanPairs : Set (Nat × Nat)).MapsTo
      Prod.fst (Finset.Icc 1 200) := by
    intro pair hpair
    have hfilter := Finset.mem_filter.mp hpair
    have hscan := mem_tribonacciScanPairs_iff.mp hfilter.1
    exact Finset.mem_Icc.mpr ⟨hscan.1, by omega⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro v₁ hv₁
  unfold tribonacciNonintegralRowCount
  refine Finset.card_bij (fun pair _ => pair.2) ?_ ?_ ?_
  · intro pair hpair
    have hfiber := Finset.mem_filter.mp hpair
    have hnonintegral := Finset.mem_filter.mp hfiber.1
    have hscan := mem_tribonacciScanPairs_iff.mp hnonintegral.1
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor <;> omega
    · simpa [hfiber.2] using hnonintegral.2
  · intro pair₁ hpair₁ pair₂ hpair₂ heq
    have hfirst₁ := (Finset.mem_filter.mp hpair₁).2
    have hfirst₂ := (Finset.mem_filter.mp hpair₂).2
    apply Prod.ext
    · omega
    · exact heq
  · intro v₂ hv₂
    have hrow := Finset.mem_filter.mp hv₂
    have hbounds := Finset.mem_Icc.mp hrow.1
    refine ⟨(v₁, v₂), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply mem_tribonacciScanPairs_iff.mpr
        exact ⟨(Finset.mem_Icc.mp hv₁).1, hbounds.1, hbounds.2⟩
      · exact hrow.2
    · rfl

end D5.S3.Constants.Irrationality.TribonacciDeficitScan
