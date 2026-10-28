# Shared Moore Transfer and Finite Synthesis

## Abstract

Shared finite Moore tables preserve the export, total installed state and invocation budgets on every actual predecessor fiber.

Fix a finite prefix-free cut P and a complete current row C with a nonempty actual image fiber, represented by an arbitrary reference origin. In the formulas, rho denotes substitution, fill(C,v) denotes evaluateRow(extend C v.val.val,C), and nativeStep(M,t)(s) is M.next(s,readout(M.addr(s),t)). Value arguments of types and DeepValues are coerced to their underlying class functions. BoundedCandidateType(C) is the dependent sum of Candidate(C,a,b) over all natural a,b; Running(A), Halts(A), States(A), table(A) and color(A) are its actual components. The domain consists of every finite origin u with canonicalRow P (substitution u) = C. ImageValues C are the actually acquired injective class values; the original row-fiber correspondence retains the complete exterior, every repeated class occurrence, every different-class disequality and every blocked cut member. There is no source-size, hidden-depth or intrinsic-rank restriction. The attained chart is NativeClassRootSimulation.Chart C, enumerated by NativeFiniteRootMinimax.chartList. Its entire predecessor target is NativeFullRootFeasibility.target, computed by computedTarget. The public finite_root_minimax theorem supplies both exact interfaces directly.

A native table is the existing NativeSixSourceMoore.Controller Q H, with disjoint running and halting carriers. Each running state has one fixed finite literal address and four reply transitions into Q plus H. Each halt stores its complete LiteralRow output. All installed states count, including unused states and different halts with equal outputs. The normalized exported value is the initial state itself, and inclusion is its recoverable entry map. For an original actual finite export sigma and lawful entry iota, the producer computes and actually exports tau=iota composed with sigma before the cut. The image of tau is iota applied to the actual image of sigma, so this normalization cannot increase its number of distinctions. If iota merges values, this is a changed encoder; the old sigma is not retained after entry. No separate advice, clock, phase, pointer, trace, decoder, variable address or source-dependent table remains accessible. NativeClassRootImage.imageOriginEquiv puts acquired full class values and actual origins in bijection, so exporting a function of ImageValues is exactly the normalized acquired-data contract, rather than an extra observation port.

A root table has precisely the same carriers and fixed outputs, but each running state queries one genuinely occurring class. Its four-reply next table keeps an arbitrary absent entry, although a class root is always reached. Every invocation costs one, including repeated or constant-on-chart questions. An empty class type forces the running carrier to be empty. The bounded evaluator returns the halt and the entire list of running-state visits; this mathematical list is used to specify paths and is not machine workspace. A running state after the final allowed call fails, while an initial or early halt succeeds.

**Theorem 1.1 (Native Execution and Exact Calls).**

$$\forall Q: Type, (\forall H: Type, (\forall M: \operatorname{Controller}\left(Q, H\right), (\forall t: Source, (\forall n: Nat, (\forall k: \operatorname{Sum}\left(Q, H\right), (\forall h: H, (\forall tr: \operatorname{List}\left(Q\right), (\operatorname{evaluate}\left(\operatorname{nativeStep}\left(M, t\right), n, k\right) = \operatorname{some}\left((h, tr)\right) \Leftrightarrow (\operatorname{Run}\left(M, t, k, tr, h\right)) \land (\operatorname{length}\left(tr\right) \leq n)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.native_evaluate_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary running and halting types, every source, fuel q, initial state, halt and running-state list, evaluate(nativeStep,q,k) equals some(h,tr) exactly when the original native Run holds with that same tr and halt and length(tr) at most q. Each read constructor corresponds to one recursive call. The converse reconstructs the original Run without changing the controller model.

**Theorem 1.2 (Paid Recoding on the Same Carriers).**

$$\forall Q: Type, (\forall H: Type, ([\operatorname{Fintype}\left(Q\right)], \forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall uo: Source, (\forall d: \operatorname{Classes}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), (\forall M: \operatorname{Controller}\left(Q, H\right), (\exists values: (\operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right)) \to (\operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right)), (\exists origins: (\operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right)) \to (\operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right)), ((\forall theta: \operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), ((\operatorname{rho}\left(\operatorname{value}\left(origins\left(theta\right)\right)\right) = \operatorname{fill}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), values\left(theta\right)\right)) \land (\operatorname{types}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), values\left(theta\right)\right) = \operatorname{value}\left(theta\right)) \land (\operatorname{DeepValues}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), \operatorname{installedWordBound}\left(M\right), values\left(theta\right)\right)) \land (\operatorname{target}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), \operatorname{value}\left(theta\right)\right) = \operatorname{canonicalRow}\left(P, \operatorname{value}\left(origins\left(theta\right)\right)\right)))) \land (\forall theta: \operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), (\forall n: Nat, (\forall k: \operatorname{Sum}\left(Q, H\right), (\operatorname{evaluate}\left(\operatorname{rootStep}\left(\operatorname{paidTable}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), d, M\right), \operatorname{value}\left(theta\right)\right), n, k\right) = \operatorname{evaluate}\left(\operatorname{nativeStep}\left(M, \operatorname{rho}\left(\operatorname{value}\left(origins\left(theta\right)\right)\right)\right), n, k\right))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.paid_native_recode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonempty classes, installedWordBound is the maximum address length over every installed running state, including unused entries. padded_native_query_chart supplies one simultaneous truthful actual filling and origin for every attained type at this bound. Their types, full actual origin property, deep branch values and complete target equality are retained. The original firstClass, classReply and firstClass_reply classify each installed address. If no class is entered, the root table really queries a chosen existing class d0 and ignores the answer through a constant response map. If a hole is entered, its original shared class is queried: an empty suffix forwards the root reply; a proper suffix sends leaves to absent and padded branches to branch. The fourth unreachable reply can be arbitrary.

paidTable preserves exactly Q, H and every halt output. Its next rule depends only on the installed running state and the one reply. The theorem gives equality of the complete evaluator result for every type, every fuel and every initial state on the selected actual origin. Thus all corresponding paths, invocation counts and halts agree, including early halts, convergences, repeated coordinates, unused states and cyclic union graphs. The new coloring is the original export evaluated on these selected actual fillings; its actual range is a subset of the original export range. No fixed arbitrary encoder is asserted constant on type fibers, and no execution-history unrolling is used.

**Theorem 1.3 (Installation on Every Original Origin).**

$$\forall Q: Type, (\forall H: Type, (\forall P: CutSet, (\forall hP: \operatorname{CutPrefixFree}\left(P\right), (\forall uo: Source, (\forall T: \operatorname{RootTable}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), Q, H\right), (\forall color: (\operatorname{Chart}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right)) \to (\operatorname{Sum}\left(Q, H\right)), ((\operatorname{range}\left(\operatorname{exportCode}\left(hP, uo, color\right)\right) = \operatorname{range}\left(color\right)) \land (\forall v: \operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), (\forall u: \operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), ((\operatorname{rho}\left(\operatorname{value}\left(u\right)\right) = \operatorname{fill}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), v\right)) \implies ((\operatorname{target}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), \operatorname{types}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), v\right)\right) = \operatorname{canonicalRow}\left(P, \operatorname{value}\left(u\right)\right)) \land (\forall n: Nat, (\forall k: \operatorname{Sum}\left(Q, H\right), (\operatorname{evaluate}\left(\operatorname{nativeStep}\left(\operatorname{install}\left(T\right), \operatorname{rho}\left(\operatorname{value}\left(u\right)\right)\right), n, k\right) = \operatorname{evaluate}\left(\operatorname{rootStep}\left(T, \operatorname{types}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), v\right)\right), n, k\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.install_full_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The producer inspects the roots of its actually acquired class terms and computes exportCode(c,v), the initial state c(theta(v)). This is a new complete code actually exported before the access cut under the supplied services. Every attained type has a truthful actual filling, so the actual export range equals the range of c. install replaces each coordinate by NativeWholeRowService.representative C d and keeps the carriers, four transitions and complete outputs. The first and third public conjuncts of native_full_root_feasibility give the complete target and exact representative readout. Consequently every actual origin, with arbitrary finite branch shapes, has the same complete evaluator path as its root input. Neither the padded necessity witnesses nor their depth bound restrict this direction.

**Theorem 1.4 (Identical Three Upper Budgets).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall uo: Source, (\forall r: Nat, (\forall K: Nat, (\forall q: Nat, (((1 \leq r) \land (1 \leq K)) \implies (\operatorname{NativeFeasible}\left(P, \operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), r, K, q\right) \Leftrightarrow \operatorname{RootFeasible}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), r, K, q\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.shared_moore_feasibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty full actual fiber, r at least one, K at least one and q at least zero, native and root joint feasibility are equivalent. The budgets count actual exported initial-state distinctions, all installed running plus halting states, and every invocation. Necessity uses the paid same-carrier recoding; sufficiency uses actual acquired-root export and representative addresses on the entire original fiber. With no reached classes, the chart has one empty function and the complete target is fixed. Necessity explicitly installs one halt, one code and no running state. No nonexistent coordinate and no dummy native call is introduced.

**Theorem 1.5 (One Source Has No Repeated Running State).**

$$\forall Q: Type, (\forall H: Type, (\forall step: (Q) \to (\operatorname{Sum}\left(Q, H\right)), (\forall n: Nat, (\forall k: \operatorname{Sum}\left(Q, H\right), (\forall h: H, (\forall tr: \operatorname{List}\left(Q\right), ((\operatorname{evaluate}\left(step, n, k\right) = \operatorname{some}\left((h, tr)\right)) \implies (\operatorname{Nodup}\left(tr\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.terminating_path_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any fixed deterministic step function, every successful bounded evaluator path has a duplicate-free running-state list. A suffix beginning at a repeated state would be the same terminating path by determinism but strictly shorter, contradicting equality of their lengths. This fixes one stationary input. It places no acyclicity condition on the union of paths for different inputs.

**Theorem 1.6 (All Finite Carriers and Unused Outputs).**

$$\forall C: LiteralRow, ((\operatorname{Nonempty}\left(\operatorname{Chart}\left(C\right)\right)) \implies (\forall Q: Type, (\forall H: Type, ([\operatorname{Fintype}\left(Q\right)], [\operatorname{Fintype}\left(H\right)], \forall T: \operatorname{RootTable}\left(C, Q, H\right), (\forall color: (\operatorname{Chart}\left(C\right)) \to (\operatorname{Sum}\left(Q, H\right)), (\forall r: Nat, (\forall q: Nat, (((\operatorname{ncard}\left(\operatorname{range}\left(color\right)\right) \leq r) \land (\forall theta: \operatorname{Chart}\left(C\right), (\exists h: H, (\exists tr: \operatorname{List}\left(Q\right), ((\operatorname{evaluate}\left(\operatorname{rootStep}\left(T, \operatorname{value}\left(theta\right)\right), q, color\left(theta\right)\right) = \operatorname{some}\left((h, tr)\right)) \land (\operatorname{out}\left(T, h\right) = \operatorname{target}\left(C, \operatorname{value}\left(theta\right)\right))))))) \implies (\exists A: \operatorname{Candidate}\left(C, \operatorname{card}\left(Q\right), \operatorname{card}\left(H\right)\right), ((A \in \operatorname{candidates}\left(C, \operatorname{card}\left(Q\right), \operatorname{card}\left(H\right)\right)) \land (\operatorname{check}\left(A, r, q\right) = true)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.arbitrary_carrier_completeness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every correct finite root table on arbitrary carriers is represented by an accepted candidate on Fin(card Q) plus Fin(card H). The enumeration uses explicit finite lists and List.pi, including all coordinate maps, four reply transitions into the same state set, fixed attained-output maps and all initial colorings. Canonical split partitions cover every finite running/halting partition by separate carrier equivalences. These equivalences are used only in the proof; no noncomputable equivalence supplies executable search data. State counts, color-range cardinalities and complete paths are transported. An unused halt whose output is not attained is assigned one fixed attained output. The evaluator does not inspect halt outputs, and every actually reached halt already has its correct attained output, so no attained path or output changes.

**Theorem 1.7 (Returned Tables Solve the Full Fiber).**

$$\forall P: CutSet, (\forall hP: \operatorname{CutPrefixFree}\left(P\right), (\forall uo: Source, (\forall r: Nat, (\forall K: Nat, (\forall q: Nat, (\forall A: \operatorname{BoundedCandidateType}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), ((\operatorname{synthesize}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), r, K, q\right) = \operatorname{some}\left(A\right)) \implies ((\operatorname{ncard}\left(\operatorname{range}\left(\operatorname{exportCode}\left(hP, uo, \operatorname{color}\left(A\right)\right)\right)\right) \leq r) \land (\operatorname{card}\left(\operatorname{States}\left(A\right)\right) \leq K) \land (\forall v: \operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), (\forall u: \operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right)\right), ((\operatorname{rho}\left(\operatorname{value}\left(u\right)\right) = \operatorname{fill}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), v\right)) \implies (\exists h: \operatorname{Halts}\left(A\right), (\exists tr: \operatorname{List}\left(\operatorname{Running}\left(A\right)\right), ((\operatorname{Run}\left(\operatorname{install}\left(\operatorname{table}\left(A\right)\right), \operatorname{rho}\left(\operatorname{value}\left(u\right)\right), \operatorname{exportCode}\left(hP, uo, \operatorname{color}\left(A\right)\right)\left(v\right), tr, h\right)) \land (\operatorname{out}\left(\operatorname{table}\left(A\right), h\right) = \operatorname{canonicalRow}\left(P, \operatorname{value}\left(u\right)\right)) \land (\operatorname{length}\left(tr\right) \leq q)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.synthesize_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A returned candidate has an actually computed acquired-root initial code with actual range at most r, exactly its installed sum carrier with cardinality at most K, and a native Run terminating with the whole canonical predecessor row within q invocations on every original actual origin. Soundness applies the finite Boolean check, the exact native Run/evaluator equivalence and the full-fiber installation. The complete output includes the inverse exterior, restricted canonical class partition with every equality and disequality, and every predecessor absence guard.

**Theorem 1.8 (Executable Arbitrary-Row Decision).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall uo: Source, (\forall r: Nat, (\forall K: Nat, (\forall q: Nat, (((1 \leq r) \land (1 \leq K)) \implies (\operatorname{isSome}\left(\operatorname{synthesize}\left(\operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), r, K, q\right)\right) = true \Leftrightarrow \operatorname{NativeFeasible}\left(P, \operatorname{canonicalRow}\left(P, \operatorname{rho}\left(uo\right)\right), r, K, q\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.finite_shared_synthesis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite procedure considers every positive total size through K and checks every attained chart input. A failed bounded run or an incorrect complete output rejects that input. It never tests whether the union graph is a DAG. Completeness combines same-carrier transfer, arbitrary-carrier reindexing, preservation under replacement of unused outputs and complete finite function enumeration. A positive result is a finite acquired encoder and one fixed-address native table for the original full fiber. No native address-length bound is an input. The construction decides existence in the explicit bounded-table model; it does not extract used states, longest words or a finite table from arbitrary program text.

**Theorem 1.9 (Exact Finite Checker).**

$$\forall C: LiteralRow, (\forall a: Nat, (\forall b: Nat, (\forall A: \operatorname{Candidate}\left(C, a, b\right), (\forall r: Nat, (\forall q: Nat, (\operatorname{check}\left(A, r, q\right) = true \Leftrightarrow \operatorname{Checked}\left(A, r, q\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.check_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean check is true exactly when the actual attained color range has at most r elements and every attained input reaches its correct complete target within q calls. This statement includes early halts, duplicate output values, arbitrary transition cycles and the failure of a still-running state at exhausted fuel.

**Theorem 1.10 (Complete-Output Halt Bound).**

$$\forall C: LiteralRow, (\forall Q: Type, (\forall H: Type, ([\operatorname{Fintype}\left(H\right)], \forall T: \operatorname{RootTable}\left(C, Q, H\right), (\forall color: (\operatorname{Chart}\left(C\right)) \to (\operatorname{Sum}\left(Q, H\right)), (\forall q: Nat, ((\forall theta: \operatorname{Chart}\left(C\right), (\exists h: H, (\exists tr: \operatorname{List}\left(Q\right), ((\operatorname{evaluate}\left(\operatorname{rootStep}\left(T, \operatorname{value}\left(theta\right)\right), q, color\left(theta\right)\right) = \operatorname{some}\left((h, tr)\right)) \land (\operatorname{out}\left(T, h\right) = \operatorname{target}\left(C, \operatorname{value}\left(theta\right)\right)))))) \implies (\operatorname{targetCount}\left(C\right) \leq \operatorname{card}\left(H\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.complete_output_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be targetCount C, the number of distinct attained complete predecessor rows. A recovered actual valuation supplies an attained chart point, so m is positive on every nonempty original fiber. Every correct root table has at least m halts. The factorization and actual attained witnesses identify this same output set with the outputs on the original actual fiber, so the identical bound applies to a native solution. Equal-output and unused halts cannot reduce the count. This cardinal bound is also used to reject insufficient total-state budgets before finite search.

**Theorem 1.11 (Exact Zero-Call Endpoint).**

$$\forall C: LiteralRow, (\forall r: Nat, (\forall K: Nat, (\operatorname{RootFeasible}\left(C, r, K, 0\right) \Leftrightarrow (\operatorname{targetCount}\left(C\right) \leq r) \land (\operatorname{targetCount}\left(C\right) \leq K))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.zero_call_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero calls every initial state is already a halt. Distinct targets require distinct actual exported states and distinct fixed-output halts. Conversely the table consists of exactly one halt per attained complete row and exports that halt's code, computed from acquired roots. Thus feasibility is exactly r at least m and K at least m, on either side of the transfer. A constant target has the endpoint r=K=1,q=0. With no reached classes the exterior is the entire current tree, even for a nonempty blocked cut. An empty cut is of this form. A root cut has both beta and branch types but the same one-hole predecessor row. Cuts already blocked remain absent by NativeDepthPatterns.original_present_transport. Newly reached addresses extend an original beta leaf by one edge: the absent-address clause of actual_address_geometry, the same transport, and the two substituted leaf shapes give this exact parent. canonicalRow_absent_guard retains the concrete strict-prefix blocking leaf in the complete row. The public factorization in native_full_root_feasibility identifies its old mask with H(P,u) and its target with this entire predecessor row; right_birth also gives the right-sibling alpha criterion. Thus already blocked cuts and newly blocked beta-parent guards are both retained in every installed output. In particular r=1,q=0 is feasible exactly when m=1 and K is at least one.

The concrete checker input cyclicInput uses the one-hole current row, two running states a,b both querying its root class and one halt h carrying the complete one-hole predecessor row. Beta enters a and follows a,b,h; branch enters b and follows b,a,h. Both make two calls. The actual origins alpha and beta have current images beta and E=pair(beta,alpha), respectively, so both paths belong to the same original actual row fiber. The union contains a to b to a, while each fixed-source list is duplicate-free. Other replies halt. The finite checker accepts this input and its soundness gives a full-fiber solution through actual representative-root queries and acquired code export. Finite synthesis may return the cheaper constant halt for the same row; selecting this cyclic table is not a requirement.

Classical state-associated output terminology is attributed to Edward F. Moore, Gedanken-Experiments on Sequential Machines, Automata Studies, DOI 10.1515/9781400882618-006. This attribution imports no external minimization theorem and makes no claim to verification of the full paper. The actual image grammar, unique inverse, complete row fiber and simultaneous finite padding are the existing NativeClassRootImage, NativeCutFibers, NativeFullRootFeasibility and NativeClassRootPadding results. Finite enumeration and deterministic induction are ordinary methods; no global novelty claim is made.

Acquisition, genuine actual export, complete access isolation, authenticated one-update continuity, lawful common entry and stationary native service are supplied paid premises. The mathematical export construction does not establish those physical services. Same-r,K,q feasibility preserves neither an arbitrary fixed encoder pointwise, every original native trace on every source, address width, installed tables or whole-output storage, total physical memory, acquisition/export work, entry implementation nor service time. The exact necessity comparison is with one selected actual origin per type; the newly installed sufficient table is correct on every actual origin. A charged constant recoding is a real class query, not a free phase. Zero fresh calls do not mean zero acquisition. Computed addresses or unbounded workspace require a separate proof that the total configurations satisfy the finite stationary table contract.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.arbitrary_carrier_completeness`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.check_spec`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.complete_output_lower`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.finite_shared_synthesis`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.install_full_fiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.native_evaluate_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.paid_native_recode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.shared_moore_feasibility`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.synthesize_sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.terminating_path_nodup`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.zero_call_endpoint`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax](../NativeFiniteRootMinimax.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceMoore](../NativeSixSourceMoore.md)
