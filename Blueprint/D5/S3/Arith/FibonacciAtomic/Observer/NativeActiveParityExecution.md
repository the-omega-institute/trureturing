# Expanded active parity execution

## Abstract

NativeActiveParityExecution

Every public full ordered skeleton S supplies a chart by numbering its leaves from left to right and constructing their literal addresses recursively. The labels already on S are ignored, so the chart depends only on its shape. Writing h for the leaf count of S, this chart is a full ordered literal skeleton with h leaves and one fixed address for each index from zero to h minus one. At that address its literal subtree is the corresponding indexed variable, and the skeleton has exactly h leaves. Each original label x(i) is independent: false means alpha and true means beta. Filling the skeleton with the atomic sources of ranks bit(x(i)) defines the original source. The unknown entry lag t applies substitution to this same source. The observation at runtime epoch j is its literal readout after t plus j substitutions; j counts genuine post-entry Updates and is proof data, not a controller register.

The expanded table retains Q(i,a) for zero through h, B(i,a,b) and C(i,b) for zero through h minus one, and V(a,01), V(a,11), V(a,10), for both Boolean accumulators and every latch bit. At nonterminal Q(i,a), the literal is the chart's address i followed by K right edges. At i equal to zero, absence selects V(a,01), branch holds Q(0,a), and either leaf reply selects B(0,a,a XOR chi(reply)). At positive i, all four replies select that B row. The decoder chi is true on absence and beta and false on alpha and branch.

V(a,01) and V(a,11) each execute one genuine Update. V(a,10) performs a root Read and returns to Q(0,a) on every reply. Every B row performs a root Read: unequal accumulator and latch bits select B(i,b,b), while equal bits select C(i,b). Every C row performs a root Read and selects Q(i+1,b). These Reads retain the actual source and discard their raw reply. Q(h,a) halts with the fixed output a. There are no internal instructions. The B and C notation distinguishes the before-advance and after-advance latch positions of the expanded table; it does not establish a binary encoding.

**Theorem 1.1 (Original parity and exact update endpoint).**

$$\forall S: Source, (\forall x: \operatorname{Fin}\left(\operatorname{length}\left(S\right)\right) \to Bool, (\forall t: Nat, (\forall K: Nat, ((t \leq 2K) \implies (((\operatorname{mod}\left(\operatorname{length}\left(S\right), 2\right) = 0) \lor (t = 0)) \implies (\forall b: Bool, (\forall N: Nat, ((\operatorname{Run}\left(\operatorname{program}\left(\operatorname{chartOf}\left(S\right), K\right), \operatorname{observations}\left(\operatorname{chartOf}\left(S\right), t, x\right), \operatorname{start}\left(\operatorname{length}\left(S\right)\right), 0, \operatorname{endpoint}\left(\operatorname{length}\left(S\right), b\right), N\right)) \iff ((b = \operatorname{parity}\left(\operatorname{labels}\left(x\right), \operatorname{length}\left(S\right)\right)) \land ((N = 2(K - \operatorname{div}\left(t + \operatorname{bit}\left(\operatorname{x}\left(0\right)\right), 2\right))) \land (\operatorname{output}\left(\operatorname{endpoint}\left(\operatorname{length}\left(S\right), b\right)\right) = \operatorname{some}\left(\operatorname{parity}\left(\operatorname{labels}\left(x\right), \operatorname{length}\left(S\right)\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.native_active_parity_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement ranges over every full original skeleton, whose chart is constructed without a native observation premise, and all independently chosen labels, and all entries with t at most twice K. Its admissible regimes are even h or zero entry lag. In the bounded source promise t at most T, choosing K as the ceiling of T divided by two supplies this bound; when T is zero, t is zero. The original output is the XOR of all h labels, written parity(labels(x),h). A finite Run to a halt has precisely that fixed output, the displayed number of genuine Updates, and the fixed Halt payload equal to that original XOR.

The pilot alignment theorem is applied to the actual first cone of rank t plus bit(x(0)). Its existing Run retains both Updates and the paid return Read. Induction on that Run splices its terminal leaf reply into the B latch route. If J is its terminal update epoch, every original cone then has rank t plus J plus bit(x(i)), in the interval from twice K minus one through twice K plus two. The exact four-reply clock law proves that chi equals rank parity on this acquired window. Since J is even, each accepted bit is (t modulo two) XOR x(i).

Induction over the remaining stages uses the concrete data Read and the two or three concrete latch-routing root Reads at each stage. The accumulator is the XOR of the accepted prefix. The common offset cancels for even h, and is zero when t is zero. The constructed actual Run reaches the asserted halt. Native halt uniqueness supplies the converse and the fixed endpoint, including its update epoch.

The pilot branch hold has no promised support under the rank bound, and no off-promise termination is asserted. Chi is not a parity decoder for arbitrary saturated branches or arbitrarily deep absent addresses. This result establishes the entire expanded symbolic table's actual-source execution. Its realization as one injective immediate binary word with no adjacent ones remains a separate obligation, together with all encoding edges, width and installed-word counts for arbitrary h and the complete primitive, address and bit-change bills. No mutable-width or physical execution-service claim follows from this statement.

**Theorem 1.2 (Literal readout on an original cone).**

$$\forall h: Nat, (\forall C: \operatorname{Chart}\left(h\right), (\forall x: \operatorname{Fin}\left(h\right) \to Bool, (\forall t: Nat, (\forall j: Nat, (\forall i: \operatorname{Fin}\left(h\right), (\forall p: Address, (\operatorname{observations}\left(C, t, x, j, \operatorname{append}\left(\operatorname{address}\left(C, i\right), p\right)\right) = \operatorname{readout}\left(p, \operatorname{atom}\left(t + j + \operatorname{bit}\left(\operatorname{x}\left(i\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.cone_read` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any supplied Chart with h independently indexed original leaves, any label assignment, entry lag t, post-entry update epoch j, original index i and arbitrary literal suffix p, the physical readout at address(i) followed by p equals the readout of p on the atom of rank t+j+bit(x(i)). The atom on the right is the actual original cone of that source at epoch j. This identity imposes no alignment-window premise and is used for the static scan as well as the active alignment. The label convention remains atom(bit(x(i))), with alpha equal to of(true) and beta equal to of(false).

**Theorem 1.3 (Common Boolean offset in a finite parity).**

$$\forall x: Nat \to Bool, (\forall b: Bool, (\forall n: Nat, (\operatorname{parity}\left(\operatorname{shift}\left(b, x\right), n\right) = \operatorname{xor}\left(\operatorname{and}\left(\operatorname{decide}\left(\operatorname{mod}\left(n, 2\right) = 1\right), b\right), \operatorname{parity}\left(x, n\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.shifted_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write shift(b,x)(i)=b XOR x(i). The XOR of its first n entries is the original prefix XOR, with one additional b exactly when n is odd. Even n cancels the common offset; a false offset vanishes for every n. This identity is used after deriving the actual scheduled contributions.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.cone_read`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.native_active_parity_execution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeActiveParityExecution.shifted_parity`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers](NativeCutFibers.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativePollingAlignment](NativePollingAlignment.md)
