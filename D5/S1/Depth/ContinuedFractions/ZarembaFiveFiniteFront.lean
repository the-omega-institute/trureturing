/- GID: D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A kernel-decided table certifies Zaremba's bound five through denominator 1024. -/

import Mathlib

namespace D5.S1.Depth.ContinuedFractions.ZarembaFiveFiniteFront

/-- Fuelled Euclidean quotient trace. Each nonterminal step replaces the divisor `q`
by the strictly smaller remainder `a % q`. -/
def cfDigitsAux : Nat -> Nat -> Nat -> List Nat
  | 0, _, _ => []
  | fuel + 1, a, q =>
      if q = 0 then [] else a / q :: cfDigitsAux fuel q (a % q)

/-- Euclidean quotients for the regular continued fraction of `a / q`.
For `0 < a < q`, the initial quotient is the harmless integer digit zero.
The fuel `q + 1` exceeds the initial divisor, while every later divisor is a
strictly smaller remainder. -/
def cfDigits (a q : Nat) : List Nat :=
  cfDigitsAux (q + 1) a q

private theorem cfDigits_zero (a : Nat) : cfDigits a 0 = [] := by
  rfl

private theorem cfDigits_step (a q : Nat) (hq : 0 < q) :
    cfDigits a q = a / q :: cfDigitsAux q q (a % q) := by
  simp [cfDigits, cfDigitsAux, Nat.ne_of_gt hq]

private theorem cfDigits_remainder_lt (a q : Nat) (hq : 0 < q) : a % q < q :=
  Nat.mod_lt _ hq

def ZarembaWitness (A a q : Nat) : Prop :=
  Nat.Coprime a q ∧
    0 < a ∧
    a < q ∧
    ∀ d ∈ cfDigits a q, d ≤ A

instance (A a q : Nat) : Decidable (ZarembaWitness A a q) := by
  unfold ZarembaWitness
  infer_instance

private def digitsBounded (A : Nat) (digits : List Nat) : Bool :=
  digits.all fun d => decide (d ≤ A)

def zarembaCheck (A a q : Nat) : Bool :=
  decide (Nat.Coprime a q) &&
    decide (0 < a) &&
    decide (a < q) &&
    digitsBounded A (cfDigits a q)

private theorem zarembaCheck_sound {A a q : Nat}
    (h : zarembaCheck A a q = true) : ZarembaWitness A a q := by
  simp [zarembaCheck, digitsBounded] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem bool_all_true_of_mem {alpha : Type} (p : alpha -> Bool)
    {xs : List alpha} (h : xs.all p = true) {x : alpha} (hx : x ∈ xs) :
    p x = true := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact ih h.2 hx

def zarembaFiveWitnessTable : List Nat := [
  0, 0, 1, 1, 1, 1, 5, 2, 3, 2, 3, 2, 5, 3, 3, 4,
  3, 3, 5, 4, 9, 4, 5, 4, 5, 7, 5, 5, 5, 5, 7, 7,
  7, 7, 9, 6, 11, 7, 7, 7, 7, 9, 11, 8, 13, 8, 11, 9,
  11, 9, 9, 11, 9, 10, 17, 12, 13, 10, 11, 11, 11, 11, 11, 11,
  11, 12, 25, 12, 13, 13, 13, 15, 17, 13, 13, 13, 13, 16, 17, 14,
  17, 14, 17, 16, 19, 16, 15, 16, 17, 16, 17, 16, 17, 16, 33, 17,
  17, 17, 17, 17, 19, 18, 19, 18, 27, 22, 19, 19, 23, 19, 19, 19,
  31, 21, 25, 22, 25, 20, 21, 22, 23, 21, 21, 22, 23, 23, 55, 22,
  23, 23, 27, 23, 23, 23, 23, 26, 25, 24, 31, 24, 27, 25, 31, 25,
  31, 26, 25, 41, 31, 26, 29, 26, 27, 29, 27, 32, 29, 27, 27, 35,
  33, 29, 29, 28, 31, 29, 29, 30, 29, 29, 39, 37, 31, 30, 31, 31,
  41, 31, 37, 31, 41, 31, 41, 32, 33, 32, 35, 32, 33, 34, 41, 33,
  37, 33, 35, 34, 37, 35, 37, 34, 53, 37, 35, 36, 35, 36, 37, 38,
  37, 37, 59, 37, 37, 44, 37, 37, 41, 38, 39, 38, 39, 38, 41, 39,
  43, 43, 47, 39, 41, 40, 41, 40, 49, 40, 41, 41, 49, 41, 57, 42,
  41, 42, 43, 53, 45, 43, 43, 44, 43, 43, 43, 44, 47, 45, 45, 46,
  45, 44, 49, 46, 49, 47, 45, 45, 47, 46, 51, 49, 47, 46, 59, 47,
  47, 47, 49, 47, 49, 48, 51, 49, 61, 49, 67, 49, 53, 49, 51, 50,
  53, 50, 51, 50, 51, 52, 53, 51, 53, 56, 51, 53, 71, 52, 53, 52,
  53, 54, 53, 53, 53, 55, 53, 57, 97, 55, 55, 68, 57, 55, 55, 56,
  57, 56, 57, 56, 61, 57, 57, 56, 59, 57, 59, 57, 57, 59, 69, 64,
  59, 58, 59, 58, 59, 61, 61, 59, 61, 59, 73, 60, 61, 60, 61, 67,
  61, 61, 73, 61, 67, 61, 69, 62, 101, 62, 75, 65, 67, 63, 65, 63,
  63, 64, 71, 65, 65, 64, 67, 71, 65, 70, 65, 70, 71, 67, 71, 68,
  67, 69, 67, 68, 67, 68, 67, 70, 67, 70, 69, 68, 71, 68, 69, 71,
  71, 69, 83, 69, 71, 71, 71, 70, 73, 70, 71, 71, 73, 72, 91, 71,
  79, 79, 79, 73, 89, 72, 73, 76, 73, 73, 79, 73, 75, 76, 91, 74,
  77, 74, 75, 76, 75, 75, 77, 75, 81, 82, 77, 76, 77, 78, 77, 80,
  85, 80, 77, 78, 79, 79, 87, 81, 79, 79, 85, 79, 79, 80, 79, 80,
  83, 86, 89, 81, 83, 81, 89, 85, 81, 81, 83, 82, 83, 85, 89, 82,
  83, 86, 83, 101, 85, 83, 85, 85, 87, 86, 87, 86, 85, 86, 85, 89,
  91, 88, 113, 87, 89, 86, 89, 86, 95, 88, 87, 88, 87, 87, 89, 88,
  95, 89, 89, 88, 107, 89, 89, 91, 89, 89, 91, 90, 93, 92, 91, 91,
  95, 91, 91, 92, 93, 92, 95, 92, 93, 100, 99, 100, 97, 95, 93, 98,
  93, 97, 97, 96, 97, 94, 119, 96, 95, 95, 103, 97, 95, 103, 115, 96,
  97, 97, 97, 100, 97, 97, 105, 101, 99, 100, 109, 98, 103, 100, 111, 99,
  101, 99, 99, 100, 103, 100, 101, 101, 101, 101, 103, 104, 101, 102, 101, 101,
  105, 102, 103, 104, 111, 104, 105, 103, 103, 105, 103, 106, 107, 106, 109, 105,
  105, 109, 129, 107, 107, 105, 105, 113, 111, 106, 107, 106, 111, 109, 115, 107,
  109, 107, 107, 113, 109, 109, 109, 108, 111, 109, 109, 109, 113, 109, 109, 110,
  111, 110, 121, 111, 135, 113, 111, 111, 113, 117, 121, 113, 125, 116, 113, 112,
  115, 113, 125, 114, 113, 113, 123, 118, 115, 122, 115, 114, 115, 116, 119, 116,
  115, 115, 117, 118, 121, 119, 119, 116, 121, 118, 117, 118, 127, 126, 123, 118,
  119, 118, 121, 119, 119, 125, 121, 119, 119, 120, 129, 122, 123, 121, 131, 121,
  123, 121, 123, 121, 121, 122, 123, 122, 123, 122, 127, 124, 123, 124, 129, 128,
  133, 124, 127, 125, 125, 127, 125, 125, 127, 127, 141, 125, 127, 127, 129, 127,
  131, 126, 127, 128, 127, 136, 141, 132, 161, 128, 129, 131, 131, 128, 131, 129,
  131, 130, 129, 129, 131, 132, 139, 130, 137, 130, 131, 131, 137, 131, 131, 132,
  133, 132, 137, 137, 135, 135, 133, 133, 145, 139, 135, 134, 137, 134, 135, 134,
  135, 136, 149, 136, 147, 145, 137, 136, 137, 137, 143, 139, 137, 138, 137, 140,
  137, 139, 137, 140, 139, 139, 145, 148, 141, 139, 139, 140, 151, 139, 145, 141,
  145, 145, 143, 142, 141, 141, 155, 148, 141, 178, 145, 143, 143, 142, 147, 142,
  145, 143, 161, 143, 145, 143, 155, 147, 181, 144, 145, 145, 145, 146, 193, 145,
  145, 146, 149, 146, 149, 148, 149, 149, 157, 148, 163, 147, 149, 151, 153, 153,
  161, 148, 151, 152, 149, 150, 149, 150, 149, 151, 151, 153, 157, 151, 151, 151,
  151, 154, 151, 151, 155, 152, 153, 156, 155, 152, 163, 158, 159, 155, 155, 154,
  155, 154, 155, 156, 157, 154, 171, 160, 159, 161, 155, 155, 157, 161, 159, 158,
  157, 156, 157, 157, 159, 157, 157, 157, 163, 158, 171, 162, 193, 162, 165, 160,
  161, 159, 197, 167, 161, 163, 163, 162, 161, 161, 165, 163, 161, 161, 161, 162,
  165, 169, 181, 164, 163, 163, 163, 166, 163, 164, 163, 167, 165, 172, 177, 164,
  173, 165, 167, 167, 169, 166, 167, 166, 179, 172, 167, 166, 167, 170, 169, 167,
  167, 168, 169, 168, 181, 170, 169, 168, 169, 169, 171, 172, 173, 171, 191, 176,
  173, 170, 179, 172, 179, 173, 175, 172, 171, 171, 175, 175, 181, 172, 179, 173,
  173, 175, 173, 173, 177, 174, 187, 176, 177, 175, 189, 175, 179, 178, 177, 188,
  175,
]

def zarembaFiveNumerator (q : Nat) : Nat :=
  zarembaFiveWitnessTable.getD q 0

set_option maxRecDepth 100000 in
private theorem zarembaFiveWitnessTable_length : zarembaFiveWitnessTable.length = 1025 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks every row of the 1025-entry witness table.
private theorem zarembaFiveCertificate :
    (List.range 1025).all
      (fun q => decide (q < 2) || zarembaCheck 5 (zarembaFiveNumerator q) q) = true := by
  decide

private theorem zaremba_five_upto (q : Nat) (h2 : 2 ≤ q) (hQ : q ≤ 1024) :
    ∃ a, ZarembaWitness 5 a q := by
  have hq : q < 1025 := by omega
  have hrow := bool_all_true_of_mem
    (fun n => decide (n < 2) || zarembaCheck 5 (zarembaFiveNumerator n) n)
    zarembaFiveCertificate (List.mem_range.mpr hq)
  have hnot : ¬q < 2 := by omega
  simp [hnot] at hrow
  exact ⟨zarembaFiveNumerator q, zarembaCheck_sound hrow⟩

private theorem zarembaWitness_one_two : ZarembaWitness 5 1 2 := by
  decide

private theorem zaremba_five_54_minimal :
    ZarembaWitness 5 17 54 ∧
      ∀ a : Fin 17, ¬ZarembaWitness 5 a.val 54 := by
  decide

private theorem seventeen_fifty_four_digits : cfDigits 17 54 = [0, 3, 5, 1, 2] := by
  decide

private theorem one_six_digits : cfDigits 1 6 = [0, 6] := by
  decide

private theorem zarembaCheck_rejects_one_six : zarembaCheck 5 1 6 = false := by
  decide

/-- The fuelled quotient trace follows the Euclidean quotient/remainder step, its
remainder decreases strictly, and a successful Boolean check produces a witness. -/
theorem cfDigits_checker_sound :
    (forall a q : Nat, 0 < q ->
      cfDigits a q = a / q :: cfDigitsAux q q (a % q)) /\
    (forall a q : Nat, 0 < q -> a % q < q) /\
    (forall A a q : Nat, zarembaCheck A a q = true ->
      ZarembaWitness A a q) := by
  exact ⟨
    fun a q hq => cfDigits_step a q hq,
    fun a q hq => cfDigits_remainder_lt a q hq,
    fun A a q h => zarembaCheck_sound h⟩

/-- Every denominator from two through 1024 has a numerator whose continued-fraction
digits are at most five, together with the atom's positive, minimal, exact-trace, and
negative checker certificates. -/
theorem zaremba_five_upto_certified :
    (forall q : Nat, 2 <= q -> q <= 1024 ->
      exists a, ZarembaWitness 5 a q) /\
    ZarembaWitness 5 1 2 /\
    (ZarembaWitness 5 17 54 /\
      forall a : Fin 17, ¬ ZarembaWitness 5 a.val 54) /\
    cfDigits 17 54 = [0, 3, 5, 1, 2] /\
    (cfDigits 1 6 = [0, 6] /\ zarembaCheck 5 1 6 = false) := by
  exact ⟨
    zaremba_five_upto,
    zarembaWitness_one_two,
    zaremba_five_54_minimal,
    seventeen_fifty_four_digits,
    one_six_digits,
    zarembaCheck_rejects_one_six⟩

example : cfDigits 1 2 = [0, 2] := by decide
example : 0 < (2 : Nat) := by decide
example : zarembaCheck 5 1 2 = true := by decide
example : ZarembaWitness 5 1 2 := by decide
example : 2 <= (2 : Nat) /\ 2 <= 1024 := by decide
example : cfDigits 1 6 = [0, 6] := by decide
example : zarembaCheck 5 1 6 = false := by decide
example : Nonempty Nat := ⟨0⟩
example : Nonempty (Fin 17) := ⟨0⟩

#print axioms cfDigits_checker_sound
#print axioms zaremba_five_upto_certified

end D5.S1.Depth.ContinuedFractions.ZarembaFiveFiniteFront
