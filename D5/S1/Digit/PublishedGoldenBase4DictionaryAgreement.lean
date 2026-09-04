/- GID: D5/S1/Digit/PublishedGoldenBase4DictionaryAgreement
   generality: I
   mirror-B: D5/B/S1/Digit/PublishedGoldenBase4DictionaryAgreement
   mirror-E: none(waiver:published-dictionary-evidence)
   anchors: [mathlib/module/Mathlib.Tactic.NativeDecide]
   digest: The published 201-record base-four golden-ratio dictionary agrees with the exact repository oracle after isolating its zero anchor and 200 power records. -/

import D5.S1.Digit.GoldenBase4AutomataOracle
import D5.S1.Deficit.ZeckendorfDisplacementReading
import Mathlib.Tactic.NativeDecide
import Mathlib.Tactic.Omega

/- Library-search and source audit trail (2026-09-04):
   * `GoldenBase4AutomataOracle` already owns the canonical MSD-first
     Zeckendorf words and the noncomputable floor-difference specification.
   * `ZeckendorfDisplacementReading` supplies a computable exact Beatty-floor
     reading, so this node introduces no floating-point arithmetic.
   * The compact data parts are a lossless `(output, width, binary-code)`
     transcription of `aaronbarnoff/tcs_digits`,
     `DFA-Inductor/myFiles/dict/dict_phi_b4_200.txt`, Git blob
     `cebad54295a07797e33a5ce32a5bae51572fafbf`, byte length `116101`.
     An independent exact-integer generator reproduced that Git blob before
     the compact data was emitted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.PublishedGoldenBase4DictionaryAgreement

open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Deficit.ZeckendorfDisplacementReading

/-- A lossless compact encoding of one published dictionary row. `width`
retains the leading-bit information omitted by the natural-number code. -/
structure EncodedRecord where
  output : Nat
  width : Nat
  code : Nat
  deriving DecidableEq, Inhabited, Repr

private def dataPart0 : String :=
  include_str ".." / ".." / ".." / "Evidence" / "D5" / "S1" / "Digit" /
    "PublishedGoldenBase4Dictionary" / "part0.txt"

private def dataPart1 : String :=
  include_str ".." / ".." / ".." / "Evidence" / "D5" / "S1" / "Digit" /
    "PublishedGoldenBase4Dictionary" / "part1.txt"

private def dataPart2 : String :=
  include_str ".." / ".." / ".." / "Evidence" / "D5" / "S1" / "Digit" /
    "PublishedGoldenBase4Dictionary" / "part2.txt"

private def dataPart3 : String :=
  include_str ".." / ".." / ".." / "Evidence" / "D5" / "S1" / "Digit" /
    "PublishedGoldenBase4Dictionary" / "part3.txt"

/-- Compact source text reconstructed from the four repository evidence parts. -/
def compactSource : String :=
  dataPart0 ++ dataPart1 ++ dataPart2 ++ dataPart3

/-- Whitespace-separated natural-number parser used by the compact evidence
format. -/
def parseNatTokens (text : String) : Option (List Nat) :=
  ((text.splitToList (·.isWhitespace)).filter (fun token => !token.isEmpty)).mapM
    String.toNat?

/-- Group a flat sequence into `(output, width, code)` records. -/
def parseRecords : List Nat → Option (List EncodedRecord)
  | [] => some []
  | output :: width :: code :: rest => do
      let tail ← parseRecords rest
      pure ({ output := output, width := width, code := code } :: tail)
  | _ => none

/-- Parsed compact transcription of the published dictionary. -/
def parsedRecords : Option (List EncodedRecord) := do
  let tokens ← parseNatTokens compactSource
  parseRecords tokens

/-- Total array view. The separate `published_parse_succeeds` theorem prevents
the default branch from hiding malformed evidence. -/
def publishedRecords : Array EncodedRecord :=
  (parsedRecords.getD []).toArray

/-- Author-repository Git blob pinned by the evidence manifest. -/
def sourceGitBlobSha : String :=
  "cebad54295a07797e33a5ce32a5bae51572fafbf"

/-- Exact byte length of the pinned author-repository blob. -/
def sourceByteLength : Nat := 116101

/-- The published header declares 201 rows over a binary alphabet. -/
def publishedDeclaredRecordCount : Nat := 201
def publishedDeclaredAlphabetSize : Nat := 2

/-- Decode a fixed-width natural-number code in most-significant-bit-first
order. -/
def decodeBinaryWord (width code : Nat) : List (Fin 2) :=
  (List.range width).map fun index =>
    if code.testBit (width - 1 - index) then 1 else 0

/-- The distinguished zero row at offset zero. -/
def zeroAnchor : EncodedRecord := publishedRecords[0]!

/-- Power sample `i` occurs at offset `i + 1`, after the zero anchor. -/
def powerRecord (i : Fin 200) : EncodedRecord :=
  publishedRecords[i.val + 1]!

/-- A computable exact formula for `floor (n * phi)` when `n` is positive. -/
def positiveGoldenFloor (n : Nat) : Nat :=
  displacementDecode (n - 1) + 1

/-- Computable integer form of the `i`th base-four digit. -/
def executableBase4DigitInt (i : Nat) : Int :=
  (positiveGoldenFloor (4 ^ (i + 1)) : Int) -
    4 * (positiveGoldenFloor (4 ^ i) : Int)

/-- Computable natural-number form of the `i`th base-four digit. -/
def executableBase4Digit (i : Nat) : Nat :=
  (executableBase4DigitInt i).toNat

/-- The positive Beatty-floor implementation is extensionally equal to the
real-floor specification. -/
theorem positiveGoldenFloor_eq_floor (n : Nat) (positive : 0 < n) :
    (positiveGoldenFloor n : Int) =
      ⌊(n : Real) * Real.goldenRatio⌋ := by
  have one_le : 1 ≤ n := positive
  have cast_sub_add :
      (((n - 1 : Nat) : Real) + 1) = (n : Real) := by
    exact_mod_cast Nat.sub_add_cancel one_le
  unfold positiveGoldenFloor
  simp only [Nat.cast_add, Nat.cast_one]
  rw [displacement_decode_eq_beatty_floor, cast_sub_add]
  omega

/-- The executable digit agrees with the exact floor-difference integer. -/
theorem executableBase4DigitInt_eq_oracle (i : Nat) :
    executableBase4DigitInt i = base4DigitInt i := by
  have power_pos (j : Nat) : 0 < 4 ^ j := Nat.pow_pos (by decide)
  have current :
      (positiveGoldenFloor (4 ^ i) : Int) = base4Floor i := by
    simpa [base4Floor, Nat.cast_pow] using
      positiveGoldenFloor_eq_floor (4 ^ i) (power_pos i)
  have next :
      (positiveGoldenFloor (4 ^ (i + 1)) : Int) =
        base4Floor (i + 1) := by
    simpa [base4Floor, Nat.cast_pow] using
      positiveGoldenFloor_eq_floor (4 ^ (i + 1)) (power_pos (i + 1))
  unfold executableBase4DigitInt base4DigitInt
  rw [current, next]

/-- The executable digit agrees with the repository's `Fin 4` oracle. -/
@[simp] theorem executableBase4Digit_eq_oracle (i : Nat) :
    executableBase4Digit i = (base4GoldenDigit i).val := by
  unfold executableBase4Digit
  rw [executableBase4DigitInt_eq_oracle]
  exact (base4GoldenDigit_val i).symm

/-- Parsing all compact evidence parts succeeds. -/
theorem published_parse_succeeds : parsedRecords.isSome = true := by
  native_decide

/-- The compact transcription has exactly the count declared by the source
header. -/
theorem published_record_count :
    publishedRecords.size = publishedDeclaredRecordCount := by
  native_decide

/-- The first published row is the distinguished zero-input anchor. -/
theorem published_zero_anchor :
    zeroAnchor = { output := 0, width := 1, code := 0 } := by
  native_decide

/-- Kernel-checked computation verifies all 200 rows against the computable
word and digit oracles. -/
theorem published_power_records_match_executable :
    ∀ i : Fin 200,
      let record := powerRecord i
      record.output = executableBase4Digit i.val ∧
        record.width = (base4PowerWord i.val).length ∧
          decodeBinaryWord record.width record.code =
            base4PowerWord i.val := by
  native_decide

/-- Hence each published power row agrees with the exact real-floor digit
specification and canonical MSD-first Zeckendorf word. -/
theorem published_power_records_match_oracle (i : Fin 200) :
    let record := powerRecord i
    record.output = (base4GoldenDigit i.val).val ∧
      record.width = (base4PowerWord i.val).length ∧
        decodeBinaryWord record.width record.code =
          base4PowerWord i.val := by
  obtain ⟨output, width, word⟩ :=
    published_power_records_match_executable i
  exact ⟨output.trans (executableBase4Digit_eq_oracle i.val),
    width, word⟩

#print axioms positiveGoldenFloor_eq_floor
#print axioms executableBase4DigitInt_eq_oracle
#print axioms published_power_records_match_oracle

end D5.S1.Digit.PublishedGoldenBase4DictionaryAgreement
