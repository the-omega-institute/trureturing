# EndpointCells

## Abstract

Retained initial targets, actual endpoint cells, and deterministic complete-block controllers.

CandidateState(k,X) is a nonempty set of pairs consisting of an initial source in an arbitrary type X and a current optional LiveRecord. AllowedBlock fixes either the full or the internally legal block alphabet; an old tail is not an alphabet restriction. replyFiber retains the initial coordinate and updates only the current coordinate, filtering by the single actual endpoint reading. acquisitionSystem uses the native finite-horizon ControlSystem and has only nonempty reply fibers as successors. targetGoal means pairwise constancy of the original target f on the retained initial coordinates, independently of current values. These definitions do not assume the first-zero criterion.

**Theorem 1.1 (Merged current records require equal initial labels).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, ell: \operatorname{Bool}, X: \operatorname{Type}, Y: \operatorname{Type}, f: X \to Y, n: \mathbb{N}, cell: \operatorname{CandidateState}(k,X), ((\operatorname{BoundedReachStrategy}(\operatorname{acquisitionSystem}(k,m,ell,X),\operatorname{targetGoal}(f),n,cell)) \implies (\forall x: X, z: X, q: \operatorname{Option}(\operatorname{LiveRecord}(k)), (((\operatorname{pair}(x,q) \in \operatorname{val}(cell)) \land (\operatorname{pair}(z,q) \in \operatorname{val}(cell))) \implies (\operatorname{f}(x) = \operatorname{f}(z)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.acquisition_merge_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and m, either alphabet choice, arbitrary types X and Y, target f from X to Y, natural budget n and nonempty candidate cell, assume a native BoundedReachStrategy for acquisitionSystem(k,m,alphabet,X) and targetGoal(f). For every initial x and z and every common current record q, membership of both (x,q) and (z,q) in that cell implies f(x)=f(z). The proof follows the actually attained nonempty reply fiber of a common successor. It covers q=none and does not identify a newly rejected live source's label with the label of an initially rejected source.

**Theorem 1.2 (Successful all-one endpoint archives are exact).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, t: \mathbb{N}, v: \operatorname{ZMod}(2), phi: \operatorname{ZMod}(k+1), s: \mathbb{N}, b: \mathbb{N} \to \operatorname{ZMod}(2), (((2 \leq k) \land (1 \leq m) \land (s < k)) \implies (((\operatorname{OnesArchive}(k,m,t,v,phi,s,b)) \iff ((s+t \cdot m < k) \land (\forall i: \mathbb{N}, ((i < t) \implies (\operatorname{allOneIncrement}(k,m,i,phi) = \operatorname{b}(i)))))) \land ((\operatorname{OnesArchive}(k,m,t,v,phi,s,b)) \implies (\operatorname{allOneOrbit}(k,m,t,\operatorname{some}(v,phi,s)) = \operatorname{some}(v+\sum_{i < t} \operatorname{b}(i),phi+t \cdot m,s+t \cdot m))) \land (\operatorname{allOneOrbit}(k,m,t,\operatorname{some}(v,phi,s)) = \operatorname{if}(s+t \cdot m < k,\operatorname{some}(v+\sum_{i < t} \operatorname{allOneIncrement}(k,m,i,phi),phi+t \cdot m,s+t \cdot m),\operatorname{none}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.all_one_archive_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least two, positive m, natural t, value v, ambient phase phi, initial tail s below k and arbitrary sequence b of ZMod 2 increments, OnesArchive says that every actual endpoint after r all-one blocks, for r from zero through t, equals v plus the sum of the first r values of b. This holds exactly when s+tm is below k and each allOneIncrement(k,m,i,phi) equals b(i) for i<t.

The theorem also supplies the actual current record of a successful archive: its value is v plus the archived sum, its phase is phi+tm, and its current tail is s+tm. Without assuming success, the literal all-one orbit equals none when s+tm reaches k; otherwise its value is v plus the sum of the actual phase increments and its other coordinates are the same shifted phase and tail. The recorded endpoints all belong to the same executed orbit; block-internal bits are unread.

**Theorem 1.3 (The first zero gives the exact rejection and merge).**

$$\forall k: \mathbb{N}, n: \mathbb{N}, a: \mathbb{N}, w: \operatorname{Fin}(n) \to \operatorname{Bool}, rest: \operatorname{List}(\operatorname{Bool}), v: \operatorname{ZMod}(2), phi: \operatorname{ZMod}(k+1), s: \mathbb{N}, (((2 \leq k) \land (\operatorname{ofFn}(w) = \operatorname{append}(\operatorname{replicate}(a,\operatorname{true}),\operatorname{cons}(\operatorname{false},rest))) \land (\operatorname{DBonacciAdmissible}(k,n,w)) \land (s < k)) \implies (\operatorname{runBits}(k,w,\operatorname{some}(v,phi,s)) = \operatorname{if}(s+a < k,\operatorname{some}(v+\operatorname{wordIncrement}(k,phi,w),phi+n,\operatorname{tailAfter}(0,w)),\operatorname{none})))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.first_zero_block_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least two, natural n and a, word w on Fin n, Boolean list rest, value v, ambient phase phi and old tail s below k, assume w is DBonacciAdmissible and its chronological list is a true bits followed by false and rest. firstZeroResult is none if s+a reaches k. Otherwise it is exactly (v+wordIncrement(k,phi,w),phi+n,tailAfter(0,w)). Thus every surviving old tail at that fixed value and phase has the same actual endpoint record. The premise is local block legality; it does not exclude cross-boundary rejection or assume success of the acquisition target.

**Theorem 1.4 (Native strategies are actual bounded controllers).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, ell: \operatorname{Bool}, X: \operatorname{Type}, Y: \operatorname{Type}, f: X \to Y, n: \mathbb{N}, cell: \operatorname{CandidateState}(k,X), ((\exists tree: \operatorname{AcquisitionTree}(k,m,ell,Y,n), ((\forall pair: \operatorname{Pair}(X,\operatorname{Option}(\operatorname{LiveRecord}(k))), ((pair \in \operatorname{val}(cell)) \implies (\operatorname{result}(tree,\operatorname{snd}(pair)) = \operatorname{f}(\operatorname{fst}(pair))))) \land (\forall q: \operatorname{Option}(\operatorname{LiveRecord}(k)), (\operatorname{length}(\operatorname{archive}(tree,q)) \leq n)))) \iff (\operatorname{BoundedReachStrategy}(\operatorname{acquisitionSystem}(k,m,ell,X),\operatorname{targetGoal}(f),n,cell)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.native_controller_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and m, either alphabet flag, arbitrary source type X and label type Y, target f:X->Y, horizon n and nonempty candidate cell, there is an AcquisitionTree of horizon n that returns f(initial) on every retained source/current pair and issues at most n blocks on every current record, if and only if the native acquisitionSystem has a BoundedReachStrategy to targetGoal(f) with that same horizon and cell. A step executes its allowed complete block, reads its actual endpoint and follows only that reply. Nonempty reply fibers preserve initial labels. Impossible replies use a label from the parent cell. No decidable equality, target observation, reset or counterfactual branch execution is assumed.

**Theorem 1.5 (Actual fixed archives synthesize retained-label controllers).**

$$\forall k: \mathbb{N}, m: \mathbb{N}, ell: \operatorname{Bool}, X: \operatorname{Type}, Y: \operatorname{Type}, f: X \to Y, actions: \operatorname{List}(\operatorname{AllowedBlock}(k,m,ell)), cell: \operatorname{CandidateState}(k,X), ((\forall first: \operatorname{Pair}(X,\operatorname{Option}(\operatorname{LiveRecord}(k))), second: \operatorname{Pair}(X,\operatorname{Option}(\operatorname{LiveRecord}(k))), (((first \in \operatorname{val}(cell)) \land (second \in \operatorname{val}(cell)) \land (\operatorname{fixedBlockArchive}(actions,\operatorname{snd}(first)) = \operatorname{fixedBlockArchive}(actions,\operatorname{snd}(second)))) \implies (\operatorname{f}(\operatorname{fst}(first)) = \operatorname{f}(\operatorname{fst}(second))))) \implies (\exists tree: \operatorname{AcquisitionTree}(k,m,ell,Y,\operatorname{length}(actions)), ((\forall pair: \operatorname{Pair}(X,\operatorname{Option}(\operatorname{LiveRecord}(k))), ((pair \in \operatorname{val}(cell)) \implies (\operatorname{result}(tree,\operatorname{snd}(pair)) = \operatorname{f}(\operatorname{fst}(pair))))) \land (\forall q: \operatorname{Option}(\operatorname{LiveRecord}(k)), (\operatorname{length}(\operatorname{archive}(tree,q)) \leq \operatorname{length}(actions))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.archive_controller_synthesis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and m, either alphabet, arbitrary source type X and label type Y, target f, finite list of allowed complete blocks and nonempty candidate cell, suppose equal fixedBlockArchive values imply equal INITIAL target labels for every pair of sources in that cell. There is a correct AcquisitionTree with horizon equal to the list length and at most that many issued blocks on every current record. fixedBlockArchive executes each actual block on the record produced by its predecessor and records only complete endpoint readings. The induction follows every attained nonempty reply fiber and constructs labels without decidable target equality. The archive-fiber hypothesis must still be established for the source's clearing and recursive acquisition construction.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.acquisition_merge_obstruction`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.all_one_archive_exact`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.archive_controller_synthesis`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.first_zero_block_exact`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells.native_controller_exact`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel](LiteralModel.md)
