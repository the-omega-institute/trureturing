/- Candidate only: not installed, elaborated, kernel checked or cost accepted.
   Receipt correctness is a proof. Candidate selection has no trust contract. -/
import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.CertifiedLocalTransitionMemo

universe u v
variable {Key : Type u} {Output : Type v}

/-- A transparent input/output pair carries a kernel proof for that exact input.
The proof can be opaque while the output remains a reducible literal. -/
structure Receipt (actual : Key → Output) where
  input : Key
  output : Output
  correct : output = actual input

/-- Any selector may propose a certified entry, including a hash bucket, trie,
dictionary or a selector returning the wrong entry. Reuse requires complete Key
equality. A missing or mismatched entry evaluates the original function. -/
def memoStep [DecidableEq Key] (actual : Key → Output)
    (lookup : Key → Option (Receipt actual)) (input : Key) : Output :=
  match lookup input with
  | none => actual input
  | some receipt =>
    if receipt.input = input then receipt.output else actual input

/-- No completeness, injectivity, ordering or honesty premise on lookup. -/
theorem memoStep_eq [DecidableEq Key] (actual : Key → Output)
    (lookup : Key → Option (Receipt actual)) (input : Key) :
    memoStep actual lookup input = actual input := by
  cases selected : lookup input with
  | none => simp only [memoStep, selected]
  | some receipt =>
    by_cases same : receipt.input = input
    · simpa only [memoStep, selected, if_pos same] using
        receipt.correct.trans (congrArg actual same)
    · simp only [memoStep, selected, if_neg same]

/-- Function equality transports any existing consumer without changing it. -/
theorem memoStep_fun_eq [DecidableEq Key] (actual : Key → Output)
    (lookup : Key → Option (Receipt actual)) : memoStep actual lookup = actual :=
  funext (memoStep_eq actual lookup)

#print axioms memoStep_eq
#print axioms memoStep_fun_eq

end D5.S0.Certificates.CertifiedLocalTransitionMemo
