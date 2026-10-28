# Boolean Assignment Banks and Both Whole Predecessor Rows

## Abstract

Exact lexicographic Boolean banks on the unrestricted native origin fiber.

Source is the actual finite ordered FreeMagma Bool: alpha is of(true), beta is of(false), and pair is its binary constructor. Substitution rho sends alpha to beta and beta to pair(beta,alpha), and preserves pairs. Addresses use false=L and true=R, ordered lexicographically with L before R. Height counts edges from a leaf of height zero. The size function is the length of PreorderTreeEvaluation.word, hence counts every constructor occurrence, including every occurrence of a repeated subtree. No DAG sharing is used in these bounds.

Put ell(n)=Nat.clog 2 (max 2 n). The list words(d) sorts the entire image of frontierAddress(fullPattern(d)) in the ordinary address order; it contains exactly all length-d words without repetitions. selected(n)=take(n,words(ell(n))). The zero-based variableWord(n,i) is selected(n)[i]; it represents source variable i+1. The fixed literal is RLL concatenated with this exact word. There is no arbitrary finite-equivalence enumeration. The bounds are 0<ell(n), n<=2^ell(n)<=4(n+1), and ell(n)<=n+1.

**Definition 1.1 (Literal Data and Polynomial Length).**

$$\forall n: Nat, ((\operatorname{LiteralSpec}\left(n\right)) \Leftrightarrow ((\operatorname{PairwiseLe}\left(\operatorname{words}\left(\operatorname{ell}\left(n\right)\right)\right)) \land (\forall a: Address, ((a \in \operatorname{words}\left(\operatorname{ell}\left(n\right)\right)) \Leftrightarrow (\operatorname{length}\left(a\right) = \operatorname{ell}\left(n\right)))) \land (\operatorname{length}\left(\operatorname{selected}\left(n\right)\right) = n) \land (\operatorname{Nodup}\left(\operatorname{selected}\left(n\right)\right)) \land (\operatorname{Injective}\left(\operatorname{variableWord}\left(n\right)\right)) \land (\forall i: \operatorname{Fin}\left(n\right), ((\operatorname{length}\left(\operatorname{variableWord}\left(n, i\right)\right) = \operatorname{ell}\left(n\right)) \land (\operatorname{literal}\left(n, i\right) = \operatorname{append}\left([R, L, L], \operatorname{variableWord}\left(n, i\right)\right)) \land (\operatorname{length}\left(\operatorname{literal}\left(n, i\right)\right) = (\operatorname{ell}\left(n\right)) + (3)))) \land (\operatorname{sum}\left(\operatorname{literalLengths}\left(n\right)\right) = (n) \times ((\operatorname{ell}\left(n\right)) + (3))) \land (\operatorname{sum}\left(\operatorname{literalLengths}\left(n\right)\right) \leq (n) \times ((n) + (4)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.LiteralSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LiteralSpec records the sorted complete word list, the exact selected prefix, distinct words, every literal length and the total length bound. PairwiseLe means the list is pairwise ordered by the ordinary non-strict lexicographic relation. literalLengths(n) is List.ofFn(i ↦ length(literal(n,i))).

**Definition 1.2 (Total Interpretation on Every Source).**

$$\forall n: Nat, ((\operatorname{AllSources}\left(n\right)) \Leftrightarrow ((\forall u: Source, (\forall i: \operatorname{Fin}\left(n\right), ((\operatorname{assignment}\left(n, u, i\right) = true) \Leftrightarrow (\operatorname{readout}\left(\operatorname{literal}\left(n, i\right), \operatorname{rho}\left(u\right)\right) = branch)))) \land (\forall u: Source, (\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(n\right), ((\operatorname{literal}\left(n, i\right) = \operatorname{literal}\left(n, j\right)) \implies (\operatorname{assignment}\left(n, u, i\right) = \operatorname{assignment}\left(n, u, j\right)))))) \land (\operatorname{branchBit}\left(branch\right) = true) \land (\operatorname{branchBit}\left(alpha\right) = false) \land (\operatorname{branchBit}\left(beta\right) = false) \land (\operatorname{branchBit}\left(absent\right) = false)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.AllSources` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

assignment(n,u,i)=branchBit(readout(literal(n,i),rho(u))). branchBit is true precisely for branch. Its values on alpha, beta and absent are false. The quantifier over Source has no resource, profile or Boolean-witness premise and therefore applies to the entire actual Fiber. Equal stationary literals have equal readings, including repeated syntactic occurrences.

B(j)=NativeClassRootPadding.pad(j,beta), so B(0)=beta and B(j+1)=pair(B(j),B(j)). payload(b,a) is B(1) when some selected variable word equals a and its bit is true, and is beta otherwise. bank(b) is exactly fill(fullPattern(ell(n)),j ↦ payload(b,frontierAddress(j))). Every selected false slot and every unused slot is beta; a true slot is the whole pair(beta,beta). This payload identity is stronger than a root branch reply.

**Definition 1.3 (The Entire Prescribed Bank).**

$$\forall n: Nat, (\forall b: (\operatorname{Fin}\left(n\right)) \to (Bool), (\forall C: Source, ((\operatorname{BankSpec}\left(n, b, C\right)) \Leftrightarrow ((C = \operatorname{fullFillPayload}\left(\operatorname{ell}\left(n\right), b\right)) \land (\forall a: Address, ((\operatorname{length}\left(a\right) = \operatorname{ell}\left(n\right)) \implies (\operatorname{subtree}\left(a, C\right) = \operatorname{some}\left(\operatorname{payload}\left(b, a\right)\right)))) \land (\forall i: \operatorname{Fin}\left(n\right), (\operatorname{payload}\left(b, \operatorname{variableWord}\left(n, i\right)\right) = \operatorname{ite}\left(b\left(i\right) = true, \operatorname{B}\left(1\right), beta\right))) \land (\forall a: Address, ((\forall i: \operatorname{Fin}\left(n\right), (\operatorname{variableWord}\left(n, i\right) \neq a)) \implies (\operatorname{payload}\left(b, a\right) = beta))) \land (\operatorname{Image}\left(C\right)) \land (\operatorname{rootType}\left(C\right) = none) \land (\operatorname{height}\left(C\right) \leq (\operatorname{ell}\left(n\right)) + (1)) \land ((\operatorname{size}\left(C\right)) + (1) \leq (16) \times ((n) + (1)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.BankSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fullFillPayload(d,b) abbreviates fill(fullPattern(d),j ↦ payload(b,frontierAddress(j))). Image(C) means an actual finite preimage under rho exists. The bank is a branch image for every n and b. Its height is at most ell(n)+1 and its ordinary size plus one is at most 16(n+1). The universal frontier assertion includes unselected positions.

The source D order is (a,c,bone,btwo,bthree,bfour). Native order is (a,bone,btwo,c,bthree,bfour). dToNative=[0,3,1,2,4,5] and nativeToD=[0,2,3,1,4,5] are inverse permutations; the native canonical first-occurrence names are [0,1,3,4,5,7]. The existing filling operation is pair(pair(pair(a,bone),pair(a,btwo)),pair(pair(c,bthree),pair(c,bfour))). Thus a and c each occur twice as the same whole subtree.

For second=false, tuple(n,C,second) in native order is [beta,alpha,B(ell(n)+2),C,B(ell(n)+3),B(ell(n)+4)]; for second=true the second and third entries are exchanged. targetIndex is respectively 1 and 2. The bank has positive height at most ell(n)+1, both leaves have height zero and different labels, and the three marker heights are ell(n)+2, ell(n)+3 and ell(n)+4. Injectivity of this six-entry function is exactly all fifteen whole-value inequalities.

**Definition 1.4 (Actual Origins and Complete Target Rows).**

$$\forall n: Nat, (\forall b: (\operatorname{Fin}\left(n\right)) \to (Bool), (\forall C: Source, (\forall second: Bool, (\forall u: Fiber, ((\operatorname{WitnessSpec}\left(n, b, C, second, u\right)) \Leftrightarrow ((\operatorname{rho}\left(\operatorname{value}\left(u\right)\right) = \operatorname{filling}\left(\operatorname{tuple}\left(n, C, second\right)\right)) \land (\operatorname{Injective}\left(\operatorname{tuple}\left(n, C, second\right)\right)) \land (\operatorname{canonicalRow}\left(P, \operatorname{value}\left(u\right)\right) = \operatorname{predecessor}\left(\operatorname{targetIndex}\left(second\right)\right)) \land (\operatorname{assignment}\left(n, \operatorname{value}\left(u\right)\right) = b) \land (\forall i: \operatorname{Fin}\left(n\right), (\operatorname{subtree}\left(\operatorname{literal}\left(n, i\right), \operatorname{rho}\left(\operatorname{value}\left(u\right)\right)\right) = \operatorname{some}\left(\operatorname{ite}\left(b\left(i\right) = true, \operatorname{B}\left(1\right), beta\right)\right))) \land (\operatorname{height}\left(\operatorname{rho}\left(\operatorname{value}\left(u\right)\right)\right) \leq (\operatorname{ell}\left(n\right)) + (7)) \land ((\operatorname{size}\left(\operatorname{rho}\left(\operatorname{value}\left(u\right)\right)\right)) + (1) \leq (280) \times ((n) + (1))) \land (\operatorname{height}\left(\operatorname{value}\left(u\right)\right) \leq (\operatorname{ell}\left(n\right)) + (7)) \land ((\operatorname{size}\left(\operatorname{value}\left(u\right)\right)) + (1) \leq (280) \times ((n) + (1)))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.WitnessSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fiber is NativeClassRootImage.OriginFiber(P,row): every finite u with canonicalRow(P,rho(u))=row. P consists of all eight length-three cut addresses. row is the complete repeated-partner current row. A witness has that exact current tree, the required entire predecessor row, the prescribed assignment and literal subtrees, and bounds for both the current tree and its actual origin.

The whole Rone row is pair(pair(beta,pair(hole(0),hole(1))),pair(pair(hole(2),hole(3)),pair(hole(2),hole(5)))). The whole Rtwo row is pair(pair(pair(hole(0),hole(1)),beta),pair(pair(hole(2),hole(3)),pair(hole(2),hole(5)))). These are predecessor(1) and predecessor(2), with concrete blocking beta leaves and surviving occurrences in canonical first-member order. They are not merely acquired labels. The original legal-values row theorem gives the current row, and native_full_root_feasibility, finite_root_minimax and type_finite_row give these complete predecessor rows on the actual origin.

The inverse bank replaces each beta frontier payload by alpha and each pair(beta,beta) payload by pair(alpha,alpha), preserving the full skeleton. Homomorphic transport proves its image is the required bank. In the first origin the exceptional leftmost depth-two pair is the concrete beta leaf; in the second origin it is the next pair. Both right-side occurrences use the one inverse bank value. Marker preimages are pad(j,alpha). Thus the inverse is explicit on this family and is compatible with the original unique native inverse, without assuming an independent realization bridge.

For an arbitrary frontier function f with height(f(j))<=H and size(f(j))<=M, induction on the complete skeleton proves height(fill(d,f))<=d+H and size(fill(d,f))+1<=2^d(M+1). This includes d=0, heterogeneous payloads and repeated payloads. Applying this to the bank and inverse bank gives size+1<=4*2^ell(n). For padding, height(pad(d,t))=d+height(t) and size(pad(d,t))+1=2^d(size(t)+1). Substituting the exact six entries into the fixed eight-occurrence exterior gives height<=ell(n)+7 and size+1<=280(n+1) for both actual origin and current image. These are numerical polynomial bounds on constructed witnesses; they impose no restriction on the all-source domain.

**Definition 1.5 (Separate Syntactic Renumbering).**

$$(LocalRenumbering) \Leftrightarrow (\forall formulas: \operatorname{List}\left(\operatorname{List}\left(Name\right)\right), ((1 \leq \operatorname{commonCount}\left(formulas\right)) \land (\forall names: \operatorname{List}\left(Name\right), ((names \in formulas) \implies ((\operatorname{localCount}\left(names\right) \leq \operatorname{commonCount}\left(formulas\right)) \land (\operatorname{Injective}\left(\operatorname{commonIndex}\left(formulas, names\right)\right)) \land (\forall a: (\operatorname{Appearing}\left(names\right)) \to (Bool), (\exists b: (\operatorname{Fin}\left(\operatorname{commonCount}\left(formulas\right)\right)) \to (Bool), (\forall x: \operatorname{Appearing}\left(names\right), (b\left(\operatorname{commonIndex}\left(formulas, names\right)\left(x\right)\right) = a\left(x\right))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.LocalRenumbering` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Name is List Bool, a finite syntactic spelling. Each formula is represented by its ordered name-occurrence list. localCount(names)=length(dedup(names)); localIndex uses the index in that fixed syntactic deduplication order. commonCount(formulas)=max(1,foldr(max,0,map(localCount,formulas))). commonIndex embeds localIndex into Fin(commonCount). Each formula independently extends every assignment on its appearing names. Different formulas need not agree on equal spellings; the common universe uses the maximum local count, not a union count.

**Definition 1.6 (Exact Coordinate Interface).**

$$(CoordinateSpec) \Leftrightarrow ((\operatorname{LeftInverse}\left(dToNative, nativeToD\right)) \land (\operatorname{LeftInverse}\left(nativeToD, dToNative\right)) \land (nativeClassNames = [0, 1, 3, 4, 5, 7]))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.CoordinateSpec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

nativeClassNames abbreviates the function i ↦ value(coord(i)), represented by its six entries. The two explicit permutations preserve the source/native coordinate correspondence and the six original canonical class names.

**Theorem 1.7 (Exact Basis Heights).**

$$\forall d: Nat, (\operatorname{height}\left(\operatorname{B}\left(d\right)\right) = d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.B_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original B(d) has height d, including B(0)=beta. Thus B(1) through B(6) are distinct actual branch values.

**Theorem 1.8 (Actual Basis Preimages).**

$$\forall d: Nat, (\operatorname{rho}\left(\operatorname{pad}\left(d, alpha\right)\right) = \operatorname{B}\left(d\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.pad_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Padding alpha to depth d gives an actual predecessor of the original B(d). Every prescribed basis image is therefore in the original substitution image, with no replacement image predicate.

**Theorem 1.9 (Full FTC Lemma 6.1).**

$$(\forall n: Nat, ((\operatorname{LiteralSpec}\left(n\right)) \land (\operatorname{AllSources}\left(n\right)) \land (\forall b: (\operatorname{Fin}\left(n\right)) \to (Bool), ((\operatorname{BankSpec}\left(n, b, \operatorname{bank}\left(b\right)\right)) \land (\forall second: Bool, (\exists u: Fiber, (\operatorname{WitnessSpec}\left(n, b, \operatorname{bank}\left(b\right), second, u\right)))))))) \land ((\operatorname{ell}\left(0\right) = 1) \land (\operatorname{selected}\left(0\right) = []) \land (\forall b: (\operatorname{Fin}\left(0\right)) \to (Bool), (\operatorname{bank}\left(b\right) = \operatorname{B}\left(1\right)))) \land (\exists u: Fiber, ((\operatorname{rho}\left(\operatorname{value}\left(u\right)\right) = \operatorname{filling}\left(zeroTuple\right)) \land (\operatorname{Injective}\left(zeroTuple\right)) \land (\operatorname{canonicalRow}\left(P, \operatorname{value}\left(u\right)\right) = \operatorname{predecessor}\left(0\right)))) \land (LocalRenumbering) \land (CoordinateSpec)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.native_boolean_assignment_banks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first clause holds for every natural n and every Boolean assignment, and supplies both second=false and second=true actual witnesses. At n=0, ell=1, selected is empty and the bank is B(1), while both witness families remain available. Independently of every assignment, zeroTuple=[B(1),B(3),B(4),B(2),B(5),B(6)] in native order is B(1) through B(6) in D order. Its explicit origin is filling of the corresponding pad(j,alpha) values. The six values are distinct branch images and its full predecessor is Rzero=predecessor(0)=row. This is the unconditional Zstar witness.

The statement combines existing actual geometry and whole-row supply with the quantitative full-skeleton construction. Finite lists, logarithms, sorting, injection extension and elementary arithmetic use the pinned mathlib library. No external hardness premise, open-problem result, source-size promise, native computed address or runtime workspace is introduced.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.AllSources`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.B_height`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.BankSpec`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.CoordinateSpec`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.LiteralSpec`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.LocalRenumbering`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.WitnessSpec`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.native_boolean_assignment_banks`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.pad_preimage`
- Dependency: [D5/S0/Computability/PreorderTreeEvaluation](../../../../../S0/Computability/PreorderTreeEvaluation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../../ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerControllers](../NativeRepeatedPartnerControllers.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformVariables](../NativeUniformVariables.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/SparseLiteralParityReadLowerBound](../SparseLiteralParityReadLowerBound.md)
