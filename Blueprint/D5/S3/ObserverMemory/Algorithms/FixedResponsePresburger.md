# Fixed Response Presburger Formulas

## Abstract

Computed Presburger formulas realize fixed paths and final-update crossings exactly.

**Definition 1.1 (Computed constants and one quantified variable).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.progressionFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.progressionFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural coefficients a and C, the formula has one free count variable d. If C is zero it is d equals a. Otherwise it is exists m, d equals a plus C times m, with C times m represented by repeated addition. These are actual Mathlib Language.presburger terms and bounded formulas.

**Definition 1.2 (Endpoint-filtered finite disjunction).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathListFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathListFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A list fold joins the progression formulas whose actual endpoints equal the requested control y. All other records contribute false. An empty list gives false. No choice-based finite-set conversion or sum is used.

**Definition 1.3 (The final edge must be a genuine update).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingListFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingListFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a record ending at some z, inspect the same table at z. Retain it only if that instruction is update y, and increase its offset by one. Read and halt endpoints and the sink contribute false. Positive path weight alone is insufficient: a path ending after reads need not cross by an update into that endpoint.

**Definition 1.4 (Fixed-response path syntax).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the finite endpoint records for the supplied table, response field and initial control, then fold their endpoint-filtered formulas. The output is executable syntax with one free natural count variable.

**Definition 1.5 (Final-update crossing syntax).**

Lean statement: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingFormula`

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingFormula` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the same computed records and the same table to construct the disjunction over real final-update predecessors.

**Theorem 1.6 (Exact realization of both native relations).**

$$\forall Q, A, R: \operatorname{Type},\ [\operatorname{Fintype}(Q)], [\operatorname{DecidableEq}(Q)],\ \forall f: Q \to \operatorname{Instruction}(Q, A, R), v: A \to R,\ \forall x, y\in Q, d\in \mathbb{N},\ (\operatorname{Realize}(\operatorname{pathFormula}(f, v, x, y), \operatorname{const}(d)) \iff \operatorname{FixedPath}(f, v, x, y, d)) \land\ (\operatorname{Realize}(\operatorname{crossingFormula}(f, v, x, y), \operatorname{const}(d)) \iff \operatorname{Crossing}(f, v, x, y, d))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.fixed_response_formulas_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite control type with explicit Fintype and DecidableEq instances, arbitrary address and reply types, program f, response field v, controls x and y, and natural count d, realization of the path formula at d is equivalent to FixedPath f v x y d, and realization of the crossing formula at d is equivalent to Crossing f v x y d. Both conjuncts use the same program and vector.

Mathlib realizes computed numerals and natural scalar multiples as their natural arithmetic values. Mathlib's realization theorem for list disjunctions identifies the fold with finite progression support. The exact native-path support theorem supplies both directions. For crossing, the retained predecessor supplies the real final update constructor, and the offset shift records its unit weight.

Zero-weight cycles collapse to singleton weights while retaining endpoints. Empty paths and transient halt endpoints remain reachable; a halt has no final outgoing update. The theorem quantifies over every natural count without imposing an instruction or update bound.

For the shared-source application, fix controls Fin s, installed read occurrences Fin r and replies Fin c, with s and c positive. Every installed occurrence remains in Fin r, including repeated literals and unvisited read states. Fix a descriptor type and dimension dims(a) for each occurrence, K equal to the sum of these dimensions, and the disjoint index desc(a,k) equal to the sum of preceding dimensions plus k. The common numeric context is Ctx = Fin K disjoint-union Fin d: descriptor parameters delta precede original-source coordinates n. A zero-dimensional block is permitted.

The primitive input Reply(a,z) is an arbitrary native Presburger formula with free variables (Fin d disjoint-union Unit) disjoint-union Fin dims(a), ordered as source, epoch, local descriptor. Its internal quantifiers are unrestricted. On admitted n and valid delta, at every natural j and every permitted literal realization, its realization is equivalent to read(U iterated j times on Theta(n), literal) = z. Choose p(a,delta) among those realizations independently of the source and epoch. Write obs(delta,n,j,a) for that actual original-source read. Supply an injective rank from Fin c to Fin(q+1), monotone in j at every occurrence on the admitted, valid arguments. The endpoint h satisfies prog(h) = halt.

Native natural order needs no new relation symbol: s <= t is exists z, s+z=t, and s<t is s+1<=t. Define Gamma(v;a,b) as forall j, a<=j and j+1<=b imply the conjunction of Reply(i,v(i)) over List.finRange r. Relabel each entire Reply formula: its source coordinates map to the source block of Ctx, its descriptor coordinates map through desc to the descriptor block, and its epoch maps to this one guard binder. Mathlib Formula.relabel protects all pre-existing bound variables. Thus Gamma realizes exactly Guard obs v a b, including empty occurrence sets and quantified Reply inputs.

For l internal boundaries put m=l+1 and enumerate response vectors v_0 through v_l and intermediate controls y_0 through y_(l-1). A disjunct existentially binds the 2m+1 natural witnesses t_0 through t_m followed by d_0 through d_(m-1). Require t_0=N, t_m=J+1, t_i<t_(i+1) and Gamma(v_i;t_i,t_(i+1)) for every phase. Set x_0 to the initial control and x_(i+1)=y_i. For every i<l require t_i+d_i=t_(i+1) and crossingFormula(prog,v_i,x_i,y_i) at d_i. Finally require t_l+d_l=J and pathFormula(prog,v_l,x_l,h) at d_l. The final segment can be empty. J+1 includes reads at J; it is a guard delimiter and adds no update after halt.

The witness layout puts time t_i at index i and duration d_i at index m+1+i. Guard endpoint k, for k in Fin 2, maps to time i+k. Every source and descriptor coordinate maps identically into each phase. The Unit variable of each fixed-path or crossing formula maps only to its duration slot. BoundedFormula.relabel id promotes the named witness prefix before exs closes it; the guard epoch and all Reply, path and slack binders remain nested and capture safe.

The per-epoch formula is the finite list disjunction over l in List.range(q*r+1), every m-tuple of vectors Fin r -> Fin c and every l-tuple of intermediate controls Fin s. Enumerate a tuple by mapping List.pi (List.finRange n) with its explicit value list; membership follows from List.mem_pi. Nested use enumerates all vectors and vector tuples. The syntax uses list folds, numerals, addition and first-order quantifiers, with no variable multiplication or choice-based finite-set conversion.

To derive correctness, apply fixed_response_formulas_correct to each exact vector, control pair and duration, using its first projection for the final path and second for internal crossings. The numeric witnesses correspond to blocks = List.ofFn (i maps to (t_(i+1),v_i)). Induction on l matches the singleton and cons-cons clauses of native Partition and PhasePaths; Fin.cons records the intermediate controls and the duration equations recover their native natural differences. Conversely, List.get reads a native block list into these tuples and List.ofFn_get reconstructs the same list. No complete formula equivalence is assumed as a primitive input.

GuardedPhaseExecution.guarded_phase_execution converts these certificates to and from the original Run with the same prog, obs(delta,n), initial control, N, h and J. For a Run, the original run_epochs gives N<=J. ResponsePhasePartition.finite_response_partition supplies blocks whose length is at most q*r+1, since the summed rank potential is at most q*r. These blocks select an enumerated disjunct. Hence per-epoch realization at (delta,n,J) is equivalent to that Run for every natural J, including J<N where both are false. The halt premise makes this a first-halt interpretation.

The eventual formula existentially closes J once outside the entire per-epoch formula. Its realization at the unchanged (delta,n) is equivalent to exists J, Run prog (obs(delta,n)) initial N h J. Descriptors and the source tuple remain free and common to every phase. Independent phase sources cannot replace this tuple: two sources with constant replies 0 and 1 can each loop forever in a table where reply 0 enables the first update and reply 1 enables the later halt, while splicing their replies across that update produces a false halting certificate.

This is an application of the existing suppliers and native syntax semantics, with no new standalone mathematical declaration or literature novelty claim. It establishes the conditional abstract halt-support construction; it does not establish a source family's joint charts, descriptor coverage, exact all-source/all-epoch Reply interface or whole-row Same relation. No bound on phase duration, instruction count, update count or literal length follows. The proof adds no read port, effective last-change detector, arbitrary partial-order result, solver API, Nat-to-Int compilation or finite rational catalogue. Uniform external program encodings and section-four synthesis or output extraction require their own interfaces.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.crossingListFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.fixed_response_formulas_correct`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.pathListFormula`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger.progressionFormula`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic](FixedResponseArithmetic.md)
