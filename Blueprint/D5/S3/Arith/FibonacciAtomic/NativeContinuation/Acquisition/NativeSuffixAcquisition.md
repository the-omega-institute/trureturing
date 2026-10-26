# Original native suffix acquisition

## Abstract

Original native suffix acquisition.

Each allowed set is an explicit subset of the original five-letter Window type. The incoming guard checks the high bit against the preceding seam; the next seam is the low bit. All original zero windows and all positions remain present.

The disjoint prefix partition counts words, including different letters sharing a successor. Its induction bounds every suffix count by five to the remaining length. Reconstruction follows the first positive child and therefore cannot select a zero-completion branch.

The correctness conclusion ranges over every finite L, every A : Fin L -> Finset Window, every B : Finset Bool and both initial seams. The acquired word is a NativeHistory from natural coordinates (0,0), and native_execution identifies its actual rawMachine 0 run and final permitted seam.

These are exact natural-number algorithm and native-execution statements. No finite-control binary implementation or bit-time bound is asserted. Bounds on arithmetic values alone do not account for integer operations, storage access, control or output work.

**Definition 1.1 (Two stored seam counts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.Row`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.Row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Row is the natural-number pair whose first component belongs to seam false and second component to seam true.

**Definition 1.2 (Reading a seam count).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.entry`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.entry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r : Row and s : Bool, entry r s is r.2 when s is true and r.1 when s is false.

**Definition 1.3 (Terminal permission).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.terminal`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every B : Finset Bool, terminal B contains the two indicators of membership in B. Empty and full permissions and both seams are included.

**Definition 1.4 (One restricted backward step).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.advance`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every a : Finset Window and r : Row, advance a r sums entry r (first b) once per b in a that passes the original incoming guard. The guard is not (s=true and last b=true); the successor is first b. Distinct letters with the same successor contribute separately.

**Definition 1.5 (The complete backward table).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.table`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every B and list as of finite allowed sets, table B as stores all current-to-terminal rows. The empty restriction list gives exactly one terminal row; a nonempty list prepends advance a applied to the previously computed tail head.

**Definition 1.6 (Current row).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.counts`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.counts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every B and as, counts B as is the head of table B as. The terminal row is the default, although the table is always nonempty.

**Definition 1.7 (Distinct successful words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.completions`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.completions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every B, as and seam s, completions B as s is a finite set of original Window lists. The empty word occurs precisely when s is permitted by B. Otherwise each guarded allowed letter is prefixed to every completion from its actual successor. This finite set specifies cardinality and is not enumerated by table or reconstruct.

**Definition 1.8 (Positional restrictions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.Allowed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.Allowed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Allowed as w matches the two lists position by position and requires each letter to belong to its own allowed set. Both empty lists satisfy it; different lengths do not.

**Definition 1.9 (Fixed reconstruction order).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.modes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.modes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original letters are ordered zero, low, middle, high, ends. Window-internal printed bits retain their original low, middle, high order. The window list itself is read high to low.

**Definition 1.10 (First positive child).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.pick`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.pick` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every allowed set a, child row r and old seam s, pick a r s scans modes and returns the first allowed letter passing the original guard with strictly positive child count. It returns none if no such letter exists.

**Definition 1.11 (Reconstruction using acquired child rows).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.reconstruct`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every B, as, row list and seam s, reconstruct reads the next stored child row, calls pick and recurses on the remaining rows and restrictions. With no remaining windows it returns the empty word precisely when the final seam belongs to B. A missing child row fails.

**Definition 1.12 (Table and word together).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.acquire`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.acquire` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every B, as and s, acquire B as s computes table B as once and supplies that table to reconstruct. Its first component is the complete row list and its second component is an optional original word.

**Theorem 1.13 (All suffix counts and successful native reconstruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.native_suffix_acquisition`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.native_suffix_acquisition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem native_suffix_acquisition (L : ℕ) (A : Fin L → Finset Window)     (B : Finset Bool) :     let as := List.ofFn A     (table B as).length = L + 1 ∧     (∀ (t : Fin (L + 1)) (s : Bool),       (table B as)[t.val]? = some (counts B (as.drop t.val)) ∧       entry (counts B (as.drop t.val)) s = (completions B (as.drop t.val) s).card ∧       entry (counts B (as.drop t.val)) s ≤ 5 ^ (L - t.val) ∧       ∀ (c : ℕ × ℕ) (w : List Window),         w ∈ completions B (as.drop t.val) s ↔           Allowed (as.drop t.val) w ∧ ∃ u ∈ B, ∃ d : ℕ × ℕ, NativeHistory s c w u d) ∧     (∀ s : Bool,       ((acquire B as s).2 = none ↔ entry (counts B as) s = 0) ∧       (entry (counts B as) s = 0 ↔         ¬ ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),           Allowed as w ∧ u ∈ B ∧ NativeHistory s (0, 0) w u d) ∧       (0 < entry (counts B as) s →         ∃ (w : List Window) (u : Bool) (d : ℕ × ℕ),           (acquire B as s).2 = some w ∧ w.length = L ∧ Allowed as w ∧ u ∈ B ∧           NativeHistory s (0, 0) w u d ∧           (rawMachine 0).toDFA.evalFrom (some (s, residue 0 (0, 0))) w =             some (u, residue 0 d)))

Disjointness follows from the first original letter, rather than merely the successor seam. Induction computes the whole row list. A vanished row entry is equivalent to the absence of a successful restricted native word; a positive entry makes the fixed scan choose a positive child at every remaining step. NativeHistory supplies the same actual integer execution through native_execution, with no execution or representation premise.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.Allowed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.Row`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.acquire`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.advance`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.completions`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.counts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.entry`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.modes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.native_suffix_acquisition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.pick`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.reconstruct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.table`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/NativeSuffixAcquisition.terminal`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/NullReplyFiber](../NullReplyFiber.md)
