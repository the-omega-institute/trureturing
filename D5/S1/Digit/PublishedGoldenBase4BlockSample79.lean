/- GID: D5/S1/Digit/PublishedGoldenBase4BlockSample79
   generality: I
   mirror-B: D5/B/S1/Digit/PublishedGoldenBase4BlockSample79
   mirror-E: none(waiver:published-block-sample-instance)
   anchors: []
   utility: none
   digest: The first 79 canonical Zeckendorf encodings of powers of four admit kernel-checked first-return block codes, and finite machine fitting is equivalent to fitting the transported recurrent skeleton sample. -/

import D5.S0.Automata.BinaryZeckendorfBlockSkeleton
import D5.S1.Digit.GoldenBase4AutomataOracle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.PublishedGoldenBase4BlockSample79

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.BinaryZeckendorfBlockSkeleton
open D5.S1.Digit.GoldenBase4AutomataOracle

noncomputable section

/-- The published lower-bound computation uses power indices `0, ..., 78`.
The distinguished zero-input record is represented separately by the anchored
machine semantics. -/
def publishedPowerExtent : Nat := 79

/-- A finite family of first-return block codes carrying four-valued labels. -/
structure BlockLabeledSample (Index : Type*) where
  code : Index -> BlockCode
  label : Index -> Fin 4

/-- Harmless fallback used only to totalize the executable decoder. The
`decoded_power_code_eq_some` theorem proves that the fallback is never selected
on any of the 79 published power inputs. -/
def defaultBlockCode : BlockCode where
  blocks := []
  terminal := .recurrent

/-- Executable first-return decoding of the `i`th canonical power word. -/
def decodedPowerCode (i : Fin publishedPowerExtent) : Option BlockCode :=
  decode (base4PowerWord i.val)

/-- Total block-code view guarded by `decoded_power_code_eq_some`. -/
def powerBlockCode (i : Fin publishedPowerExtent) : BlockCode :=
  (decodedPowerCode i).getD defaultBlockCode

/-- Kernel-checked finite computation verifies that every one of the first 79
canonical power words is accepted by the first-return decoder. -/
theorem decoded_power_code_eq_some :
    forall i : Fin publishedPowerExtent,
      decodedPowerCode i = some (powerBlockCode i) := by
  intro index
  let number := 4 ^ index.val
  have : IsTrans Nat (fun first second => second + 2 ≤ first) :=
    ⟨by intro first middle last firstBound secondBound; omega⟩
  have : Std.Symm (fun first second : Nat => second + 2 ≤ first ∨ first + 2 ≤ second) :=
    ⟨fun first second bound => bound.symm⟩
  have separated : (D5.S0.Conventions.wdigits number ++ [0]).Pairwise
      (fun first second => second + 2 ≤ first) :=
    List.isChain_iff_pairwise.mp (D5.S0.Conventions.wdigits_isCanonical number)
  have unordered := separated.imp
    (fun {first second} bound =>
      (Or.inl bound : second + 2 ≤ first ∨ first + 2 ≤ second))
  have nonadjacent (rawIndex : Nat)
      (upper : rawIndex + 3 ∈ D5.S0.Conventions.wdigits number) :
      rawIndex + 2 ∉ D5.S0.Conventions.wdigits number := by
    intro lower
    have gap := unordered.forall (a := rawIndex + 2) (b := rawIndex + 3)
      (by simp [lower]) (by simp [upper]) (by omega)
    omega
  have wordSucc (length : Nat) :
      (List.range (length + 1)).reverse.map (zeckendorfBit number) =
        zeckendorfBit number length ::
          (List.range length).reverse.map (zeckendorfBit number) := by
    simp [List.range_succ]
  have legal : ∀ length : Nat, ∃ code : BlockCode,
      expandCode code = (List.range length).reverse.map (zeckendorfBit number) := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length inductionHypothesis =>
        cases length with
        | zero => exact ⟨⟨[], .recurrent⟩, rfl⟩
        | succ length =>
            rw [wordSucc]
            by_cases zero : zeckendorfBit number length = 0
            · obtain ⟨code, expanded⟩ := inductionHypothesis length (by omega)
              refine ⟨⟨.zero :: code.blocks, code.terminal⟩, ?_⟩
              change 0 :: expandCode code = _
              rw [expanded, zero]
            · have one : zeckendorfBit number length = 1 := by
                have bound := (zeckendorfBit number length).isLt
                apply Fin.ext
                have nonzero : (zeckendorfBit number length).val ≠ 0 := by
                  intro equal
                  exact zero (Fin.ext equal)
                simp only [Fin.val_one]
                omega
              cases length with
              | zero =>
                  refine ⟨⟨[], .transient⟩, ?_⟩
                  simp [expandCode, expand, one]
              | succ length =>
                  have upper : length + 3 ∈ D5.S0.Conventions.wdigits number := by
                    simpa [zeckendorfBit, Nat.add_assoc] using one
                  have nextZero : zeckendorfBit number length = 0 := by
                    simp [zeckendorfBit, nonadjacent length upper]
                  obtain ⟨code, expanded⟩ := inductionHypothesis length (by omega)
                  refine ⟨⟨.oneZero :: code.blocks, code.terminal⟩, ?_⟩
                  change 1 :: 0 :: expandCode code = _
                  rw [expanded, one, wordSucc, nextZero]
  obtain ⟨code, expanded⟩ := legal (zeckendorfWordLength number)
  have decoded : decodedPowerCode index = some code := by
    change decode ((List.range (zeckendorfWordLength number)).reverse.map
      (zeckendorfBit number)) = some code
    rw [← expanded]
    exact decode_expand code
  simp [powerBlockCode, decoded]

/-- Kernel-checked finite computation verifies lossless expansion of every
published power block code. -/
theorem expand_power_block_code :
    forall i : Fin publishedPowerExtent,
      expandCode (powerBlockCode i) = base4PowerWord i.val := by
  have sound : ∀ length : Nat, ∀ word : List (Fin 2), word.length = length →
      ∀ code : BlockCode, decode word = some code → expandCode code = word := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length inductionHypothesis =>
        intro word wordLength code decoded
        cases word with
        | nil =>
            simp only [decode, Option.some.injEq] at decoded
            subst code
            rfl
        | cons digit rest =>
            cases rest with
            | nil =>
                fin_cases digit <;> simp [decode] at decoded <;>
                  subst code <;> rfl
            | cons next tail =>
                by_cases zero : digit = 0
                · subst digit
                  simp only [decode, ↓reduceIte, Option.map_eq_some_iff] at decoded
                  obtain ⟨restCode, restDecoded, rfl⟩ := decoded
                  have expanded := inductionHypothesis (next :: tail).length
                    (by simp only [List.length_cons] at wordLength ⊢; omega)
                    (next :: tail) rfl restCode restDecoded
                  exact congrArg (fun rest => (0 : Fin 2) :: rest) expanded
                · have one : digit = 1 := by fin_cases digit <;> simp_all
                  subst digit
                  by_cases nextZero : next = 0
                  · subst next
                    simp only [decode, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
                      Option.map_eq_some_iff] at decoded
                    obtain ⟨tailCode, tailDecoded, rfl⟩ := decoded
                    have expanded := inductionHypothesis tail.length
                      (by simp only [List.length_cons] at wordLength; omega)
                      tail rfl tailCode tailDecoded
                    exact congrArg (fun rest => (1 : Fin 2) :: 0 :: rest) expanded
                  · simp [decode, nextZero] at decoded
  intro index
  exact sound _ (base4PowerWord index.val) rfl (powerBlockCode index)
    (decoded_power_code_eq_some index)

/-- The exact 79-record power sample in first-return coordinates. Its labels
reuse the repository's real-floor golden-ratio digit oracle. -/
def publishedBlockSample79 :
    BlockLabeledSample (Fin publishedPowerExtent) where
  code := powerBlockCode
  label := fun i => base4GoldenDigit i.val

@[simp] theorem publishedBlockSample79_code
    (i : Fin publishedPowerExtent) :
    publishedBlockSample79.code i = powerBlockCode i := rfl

@[simp] theorem publishedBlockSample79_label
    (i : Fin publishedPowerExtent) :
    publishedBlockSample79.label i = base4GoldenDigit i.val := rfl

/-- The stored code is exactly the result of parsing the original power word. -/
theorem publishedBlockSample79_decode
    (i : Fin publishedPowerExtent) :
    decode (base4PowerWord i.val) =
      some (publishedBlockSample79.code i) := by
  simpa [decodedPowerCode] using decoded_power_code_eq_some i

/-- Expanding a transported record recovers the unique arithmetic input word. -/
@[simp] theorem publishedBlockSample79_expand
    (i : Fin publishedPowerExtent) :
    expandCode (publishedBlockSample79.code i) =
      base4PowerWord i.val := by
  simpa using expand_power_block_code i

/-- The zero-input anchor is deliberately outside the 79 power records. -/
def publishedZeroAnchorCode : BlockCode where
  blocks := [ReturnBlock.zero]
  terminal := .recurrent

/-- The anchor block expands to the one-symbol input used by the published
machine convention. -/
@[simp] theorem publishedZeroAnchorCode_expand :
    expandCode publishedZeroAnchorCode = [(0 : Fin 2)] := rfl

/-- Distinguished output attached to the zero-input anchor. -/
def publishedZeroAnchorOutput : Fin 4 := 0

/-- Every transported power record is accepted by the binary Zeckendorf base
automaton, ending in the channel recorded by its block code. -/
theorem publishedBlockSample79_base_accepts
    (i : Fin publishedPowerExtent) :
    binaryZeckendorfBase.eval (base4PowerWord i.val) =
      some (terminalBaseState (publishedBlockSample79.code i).terminal) := by
  rw [← publishedBlockSample79_expand i]
  exact binaryBase_eval_expandCode (publishedBlockSample79.code i)

/-- A typed partial DFAO fits the 79 exact power records. -/
def MachineFitsPowerSample79
    {State : Type*}
    (machine : TypedPartialDFAO binaryZeckendorfBase (Fin 4) State) : Prop :=
  forall i : Fin publishedPowerExtent,
    machine.evalOutput (base4PowerWord i.val) =
      some (base4GoldenDigit i.val)

/-- A recurrent skeleton fits the same records after first-return transport. -/
def SkeletonFitsBlockSample79
    {ZeroState : Type*}
    (skeleton : Skeleton (Fin 4) ZeroState) : Prop :=
  forall i : Fin publishedPowerExtent,
    skeleton.eval (publishedBlockSample79.code i) =
      some (publishedBlockSample79.label i)

/-- Extraction commutes pointwise with the 79-record coordinate transport. -/
theorem extractSkeleton_eval_publishedBlockSample79
    {State : Type*}
    (machine : TypedPartialDFAO binaryZeckendorfBase (Fin 4) State)
    (i : Fin publishedPowerExtent) :
    (extractSkeleton machine).eval (publishedBlockSample79.code i) =
      machine.evalOutput (base4PowerWord i.val) := by
  calc
    (extractSkeleton machine).eval (publishedBlockSample79.code i) =
        machine.evalOutput
          (expandCode (publishedBlockSample79.code i)) :=
      eval_extractSkeleton_start machine (publishedBlockSample79.code i)
    _ = machine.evalOutput (base4PowerWord i.val) := by
      rw [publishedBlockSample79_expand]

/-- Fitting the original power words implies fitting the transported block
sample with the extracted recurrent skeleton. -/
theorem extractSkeleton_fits_publishedBlockSample79
    {State : Type*}
    (machine : TypedPartialDFAO binaryZeckendorfBase (Fin 4) State)
    (fits : MachineFitsPowerSample79 machine) :
    SkeletonFitsBlockSample79 (extractSkeleton machine) := by
  intro i
  calc
    (extractSkeleton machine).eval (publishedBlockSample79.code i) =
        machine.evalOutput (base4PowerWord i.val) :=
      extractSkeleton_eval_publishedBlockSample79 machine i
    _ = some (base4GoldenDigit i.val) := fits i
    _ = some (publishedBlockSample79.label i) := by rfl

/-- The transported block sample is semantically equivalent to the original
79 power records for every typed partial DFAO. -/
theorem machineFitsPowerSample79_iff_extractSkeletonFits
    {State : Type*}
    (machine : TypedPartialDFAO binaryZeckendorfBase (Fin 4) State) :
    MachineFitsPowerSample79 machine <->
      SkeletonFitsBlockSample79 (extractSkeleton machine) := by
  constructor
  · exact extractSkeleton_fits_publishedBlockSample79 machine
  · intro fits i
    calc
      machine.evalOutput (base4PowerWord i.val) =
          (extractSkeleton machine).eval
            (publishedBlockSample79.code i) :=
        (extractSkeleton_eval_publishedBlockSample79 machine i).symm
      _ = some (publishedBlockSample79.label i) := fits i
      _ = some (base4GoldenDigit i.val) := by rfl

/-- Conversely, any skeleton realization of the block sample yields a canonical
typed partial DFAO realizing the original 79 power words. -/
theorem canonicalMachine_fits_powerSample79
    {ZeroState : Type*}
    (skeleton : Skeleton (Fin 4) ZeroState)
    (fits : SkeletonFitsBlockSample79 skeleton) :
    MachineFitsPowerSample79 (canonicalMachine skeleton) := by
  intro i
  calc
    (canonicalMachine skeleton).evalOutput (base4PowerWord i.val) =
        (canonicalMachine skeleton).evalOutput
          (expandCode (publishedBlockSample79.code i)) := by
      rw [publishedBlockSample79_expand]
    _ = skeleton.eval (publishedBlockSample79.code i) :=
      eval_canonicalMachine skeleton (publishedBlockSample79.code i)
    _ = some (publishedBlockSample79.label i) := fits i
    _ = some (base4GoldenDigit i.val) := by rfl

#print axioms decoded_power_code_eq_some
#print axioms expand_power_block_code
#print axioms machineFitsPowerSample79_iff_extractSkeletonFits
#print axioms canonicalMachine_fits_powerSample79

end

end D5.S1.Digit.PublishedGoldenBase4BlockSample79
