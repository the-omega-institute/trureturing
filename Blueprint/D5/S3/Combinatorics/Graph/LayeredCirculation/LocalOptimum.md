# LocalOptimum

## Abstract

For every n at least five and every real position-dependent five-pattern test, the actual normalized complete-overlap local-law maximum is attained and equals the largest of the one-, two-, and three-turn max-plus trace averages. The transition matrix has exactly the five legal labeled entries; semiring zero means no path. The monodromy is the chronological product of the n heterogeneous matrices. This theorem concerns real local laws and mathematical maxima; it does not assert physical implementation, arbitrary-real computation, or a complexity bound.

Generic declarations use these source contexts:

**Definition 1.1 (MaxPlus).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.MaxPlus`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.MaxPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: abbrev MaxPlus := Tropical (WithTop (OrderDual ℝ))

**Definition 1.2 (maxScore).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxScore`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def maxScore (x : MaxPlus) : WithBot ℝ := Tropical.untrop x

**Definition 1.3 (realEntry).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.realEntry`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.realEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def realEntry (x : ℝ) : MaxPlus := Tropical.trop ((OrderDual.toDual x : OrderDual ℝ) : WithTop (OrderDual ℝ))

**Definition 1.4 (transition).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.transition`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.transition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def transition {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (i : ZMod n) : Matrix (Fin 3) (Fin 3) MaxPlus := ![![realEntry (f i 0), realEntry (f i 3), 0], ![0, 0, realEntry (f i 2)], ![realEntry (f i 1), realEntry (f i 4), 0]]

**Definition 1.5 (orderedProduct).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.orderedProduct`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.orderedProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def orderedProduct {n : ℕ} (f : ZMod n → Fin 5 → ℝ) (i : ZMod n) : ℕ → Matrix (Fin 3) (Fin 3) MaxPlus | 0 => 1 | k+1 => orderedProduct f i k * transition f (i+k)

**Definition 1.6 (monodromy).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.monodromy`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.monodromy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def monodromy {n : ℕ} (f : ZMod n → Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) MaxPlus := orderedProduct f 0 n

**Definition 1.7 (maxTrace).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxTrace`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def maxTrace (M : Matrix (Fin 3) (Fin 3) MaxPlus) : WithBot ℝ := maxScore (Matrix.trace M)

**Definition 1.8 (traceValue).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.traceValue`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.traceValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def traceValue (M : Matrix (Fin 3) (Fin 3) MaxPlus) : ℝ := (maxTrace M).unbotD 0

**Definition 1.9 (shortCycleOptimum).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.shortCycleOptimum`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.shortCycleOptimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def shortCycleOptimum {n : ℕ} (f : ZMod n → Fin 5 → ℝ) : ℝ := max (traceValue (monodromy f)) (max (traceValue (monodromy f ^ 2) / 2) (traceValue (monodromy f ^ 3) / 3))

**Definition 1.10 (LegalCyclicWord).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.LegalCyclicWord`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.LegalCyclicWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def LegalCyclicWord {L : ℕ} (u : ZMod L → Bool) : Prop := ∀ j, ¬(u j=true ∧ u (j+1)=true)

**Definition 1.11 (patternCode).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.patternCode`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.patternCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def patternCode : Bool × Bool × Bool → Fin 5 | (false,false,false) => 0 | (true,false,false) => 1 | (false,true,false) => 2 | (false,false,true) => 3 | (true,false,true) => 4 | _ => 0

**Definition 1.12 (window).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.window`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def window {L : ℕ} (u : ZMod L → Bool) (j : ZMod L) : Bool × Bool × Bool := (u j,u (j+1),u (j+2))

**Definition 1.13 (wordScore).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.wordScore`

*Formalization.* `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.wordScore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: def wordScore {n L : ℕ} (f : ZMod n → Fin 5 → ℝ) (u : ZMod L → Bool) : ℝ := ∑ j : Fin L, f (j.val : ZMod n) (patternCode (window u (j.val : ZMod L)))

**Theorem 1.14 (whole theorem18 1).**

Lean statement: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.whole_theorem18_1`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.whole_theorem18_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source telescope, in the module declared generic contexts: theorem whole_theorem18_1 (n : ℕ) (hn : 5 ≤ n) (f : ZMod n → Fin 5 → ℝ) : letI : NeZero n := ⟨by omega⟩ IsGreatest {v : ℝ | ∃ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p ∧ localScore f p=v} (max (traceValue (monodromy f)) (max (traceValue (monodromy f ^ 2)/2) (traceValue (monodromy f ^ 3)/3))) ∧ IsCompact {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p} ∧ {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p}.Nonempty ∧ (∀ p : ZMod n → Fin 5 → ℝ, (IsLocalLaw p ↔ (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ=1) ∧ IsCirculation p)) ∧ (∀ p : ZMod n → Fin 5 → ℝ, IsLocalLaw p → HasPositiveCycleDecomposition p) ∧ (∀ p : ZMod n → Fin 5 → ℝ, (∀ i σ, 0 ≤ p i σ) → IsCirculation p → p ≠ 0 → HasPositiveCycleErasure p) ∧ (∀ m : ℕ, 1 ≤ m → IsGreatest {v : ℝ | ∃ u : ZMod (m*n) → Bool, LegalCyclicWord u ∧ wordScore f u=v} (traceValue (monodromy f ^ m))) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a), w.length=m*n → IsLocalLaw (walkLaw w) ∧ localScore f (walkLaw w)=Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w/m ∧ localScore f (walkLaw w) ≤ shortCycleOptimum f The conjunction includes literal IsGreatest semantics, compactness and nonemptiness, exact local-law/circulation equivalence, positive real cycle decomposition, minimum-edge positive-support erasure, an attained trace identity for every legal periodic word length m*n with m at least one, and the lawful normalized traversal-count construction and average-score bound for every closed walk of that length, including arbitrary repetitions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.LegalCyclicWord`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.MaxPlus`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxScore`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.maxTrace`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.monodromy`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.orderedProduct`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.patternCode`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.realEntry`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.shortCycleOptimum`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.traceValue`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.transition`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.whole_theorem18_1`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.window`
- Truth anchor: `D5/S3/Combinatorics/Graph/LayeredCirculation/LocalOptimum.wordScore`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow](LayeredFlow.md)
