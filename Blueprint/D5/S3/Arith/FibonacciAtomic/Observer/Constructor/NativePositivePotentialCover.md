# The total named source family

## Abstract

Signed source cycles and minimum natural block bases

Let p present the entire finite set X of declared names, B be a finite list of selected BranchEquation cases, and S be the actual successful free-shape unifier of shapeEquations(B). The assignment s=action(p,S) retains every named term, including unused names. A residual occurrence records its name, its ordered address and its residual sort. The list occurrenceVertices(p,s) includes isolated occurrences. An occurring sort j has at least one such vertex. Decidable equality on X serves only to select that finite sort.

**Definition 1.1 (The actual sort edges).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sortEdges`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sortEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sortEdges(B,s,j) filters sourceOffsetEdges(B,s) by the sort of the left endpoint. It preserves list order, every repeated equation and every parallel edge. For a successful unifier, both endpoints are actual vertices of the same sort. A source shift contributes its original nonnegative integer offset. Ordinary and equality comparisons contribute zero. Explicit primitive ranks are separately decorated at their named addresses. The complete comparison inventory below retains scalar equations r=r'+d and r=d and one shared natural collapse parameter with ranks r,r+1,r+2. Its block projection is exactly sourceOffsetEdges; it does not solve the independent scalar equations.

**Definition 1.2 (Both orientations retain each edge identity).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedGraph`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each indexed sort edge U=V+d, signedGraph has a forward edge from V to U and a reverse edge from U to V. The Boolean orientation is part of the edge identity. Thus zero offsets, repeated edges and parallel edges remain explicit, and reversing an edge changes only its orientation and weight.

**Definition 1.3 (The signed offset).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedWeight`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward weight is d and the reverse weight is -d. A walk has the sum of its oriented edge weights. For a potential delta satisfying every original edge, the sum is delta(finish)-delta(start), so two paths with the same endpoints have the same sum.

**Definition 1.4 (Zero signed sum on every closed walk).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ZeroCycles`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ZeroCycles` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ZeroCycles asserts that every closed walk at every occurrence has weight zero. The condition refers to the actual sort edge list rather than an epoch or head-power graph. Vertices without incident edges contribute only empty walks.

**Definition 1.5 (Integer differences on the source edges).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.Potential`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.Potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Potential(B,s,j,delta) states delta(U)=delta(V)+d for every edge U=V+d of the selected sort. Pairing both orientations identifies this exact equality with the inequalities of Maths.MaxPlusPotential.IsPotential. The finite supplier theorem exists_isPotential_iff_forall_closedWalk_nonpos supplies the existence criterion. The actual witness used for minimum normalization is computedSourcePotential on this source graph; its correctness reuses the existing cycle-pruning supplier.

**Definition 1.6 (Natural ranks on an arbitrary leaf carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.BlockSolution`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.BlockSolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A block valuation u assigns a natural rank u(U,l) to each occurrence U and each leaf l. BlockSolution imposes the original signed integer equation at every leaf and every selected edge. The carrier L may be any type; no cardinality bound is imposed. Detecting inconsistency requires L to be nonempty. In particular this includes every nonempty finite ground-shape leaf set.

**Definition 1.7 (Enumerate every signed source edge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedEdges`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

signedEdges enumerates both Boolean orientations for every index of sortEdges. Indices preserve repeated and parallel source comparisons. No vertex enumeration or connected-component choice is an input.

**Definition 1.8 (Finite integer relaxation on the actual source graph).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sourceRelaxation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sourceRelaxation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At round zero every occurrence has value zero. Each successive round takes the maximum of zero and every previous-round source value plus the actual signed edge weight whose target is this occurrence. The recurrence uses finite lists, decidable equality and integer arithmetic. A round is attained by a real walk, and bounds every real walk of that length. The existing SupplierDual cycle-pruning theorem reduces an arbitrary candidate to a walk with no repeated visited vertex, hence no repeated signed edge.

**Definition 1.9 (An executable source potential candidate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.computedSourcePotential`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.computedSourcePotential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k indexed source edges the candidate runs exactly 2k relaxation rounds, the number of signed edges. It takes only B,s,j and the queried occurrence. It requires no cycle proof, solution, potential witness, ground filling or classical choice at runtime. If every signed cycle has weight zero, cycle pruning bounds a maximizing extended walk by the signed-edge count and proves both oriented inequalities. Their conjunction is precisely every original integer source offset equation. The function is total also for inconsistent graphs; correctness is asserted only under ZeroCycles.

**Theorem 1.10 (Minimum-potential normalization classifies every natural block solution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_sort_minimum_base`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_sort_minimum_base` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p,B,S,j as above with at least one occurrence of j, the theorem has two conclusions. If ZeroCycles fails, then for every nonempty type L and every natural block valuation u on L, BlockSolution fails. If ZeroCycles holds, there exist one integer potential delta equal to computedSourcePotential(B,s,j), one actual vertex b of sort j, and natural offsets a(U), independent of L and u. The chosen b minimizes delta among all actual vertices of sort j, a(b)=0, and a(U)=delta(U)-delta(b) as an integer at every such vertex. For every L, including the empty type, and every u, BlockSolution holds exactly when u(U,l)=u(b,l)+a(U) for every actual vertex U of sort j and every l. Consequently every natural base function gives a solution by that formula, with arbitrary values outside the selected sort.

A nonempty leaf valuation at any fixed leaf gives an integer potential, which telescopes around closed walks and excludes nonzero cycle sums. Conversely the executable source relaxation gives a potential when cycles vanish. Connectivity of the actual MGU source graph identifies all vertices of the same residual sort. Subtracting any two edge potentials gives a constant along this equivalence closure. Choosing a minimum on the finite vertex list makes every potential difference nonnegative; exact integer-to-natural conversion then gives the natural rank classification. The reverse implication uses the actual endpoints of every source edge and the same potential equation. This argument includes isolated unused names, empty branch lists, zero offsets, repeated and parallel constraints. If no sort occurs, the theorem is unnecessary and there is no block-base factor.

This theorem establishes the signed-cycle and natural-rank classification using a terminating potential computation on the original source graph. The canonical recovery theorem below first presents the rank-to-code step with its precise inputs. The native source theorem then derives those inputs from an original native solution and its actual branch, without assuming a BlockSolution or desired subtree identities. The finite positive image cover and signed pullback are separate results.

**Definition 1.11 (Nonempty finite leaves of an ordered shape).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.Leaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.Leaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The leaves of a primitive shape form Unit; leaves of a pair form the disjoint sum of the two child leaf sets. These types are finite and nonempty. Distinct positions remain distinct even when their ranks are equal.

**Definition 1.12 (Fill the same ground shape with natural ranks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.fill`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.fill` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fill(T,r) puts rank r(l) at each ordered leaf l of T. Adding a natural number a to every rank gives exactly shiftCode(a,fill(T,r)). This is a structural property of finite ordered codes, with no normality assumption.

**Theorem 1.13 (Recover normal occurrence blocks by the actual native shifts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_canonical_block_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_canonical_block_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual successful source unifier and occurring sort with zero signed cycle sums, there are one actual base vertex b and natural offsets a with a(b)=0, independent of all ground fillings. The base minimizes computedSourcePotential over every actual occurrence of this sort, and a(o) equals its exact integer potential difference from b. Let T be any finite ground shape, u a natural rank valuation on its nonempty leaf type satisfying BlockSolution, and C the entire family of normal named codes. Suppose that at every actual occurrence v of this sort, the subtree of C(v.name) at v.address is exactly fill(T,u(v)). Then fill(T,u(b)) is normal. For every actual v of the sort, fill(T,u(v)) equals shiftCode(a(v),fill(T,u(b))); its expansion is the actual native substitution iterated a(v) times on the expansion of the base; and rankInverse(a(v),u(v,l)) is exactly some(u(b,l)) at every leaf.

The rank classification supplies the same minimum vertex for all fillings. Normality descends along the actual ordered subtree address in the normal named code. Structural filling converts the pointwise rank equation to literal code translation. NativeFiniteNormalInversion.shift_expand gives the native equality, and exact_natural_rank_inverse gives every exact inverse rank without truncated subtraction. No desired normal base, integer potential or reconstruction equality is assumed. The concrete subtree identities and BlockSolution are hypotheses of this intermediate theorem. They are derived automatically on the live proof path of native_source_block_recovery.

**Definition 1.14 (Separate scalar positions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ScalarPosition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ScalarPosition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar label consists of a declared name and its ordered address. Every explicit primitive occurrence gets its own label, while repeated uses of one name reuse the same decorated term. Residual blocks retain the existing name, address and sort labels.

**Definition 1.15 (Natural scalar variables and constants).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.RankExpression`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.RankExpression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rank expression is either a separately addressed natural scalar or a supplied natural constant. Its value is evaluated independently of the residual block valuation.

**Definition 1.16 (A complete decoration of each named term).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.DecoratedTerm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.DecoratedTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decorated syntax distinguishes explicit scalar leaves, residual block leaves and ordered pairs. Erasure retains the original primitive Boolean or residual sort. Evaluation substitutes a natural rank at each scalar leaf and an ambient finite code at each residual occurrence.

**Definition 1.17 (Decorate every explicit and residual position).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.scalarDecorateFrom`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.scalarDecorateFrom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Structural descent extends the address by false on the left and true on the right. It labels every primitive occurrence and every residual occurrence without identifying positions.

**Definition 1.18 (One shared decoration per original name).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.scalarDecorate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.scalarDecorate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

scalarDecorate(s,x) starts at the empty address in the entire substituted term s(x). It includes unused names and has no depth bound.

**Definition 1.19 (Scalar and block equations in one finite inventory).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ComparisonInventory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ComparisonInventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar comparison states an exact integer equation r=r'+a for natural ranks and the original natural shift a. A supplied constant gives r=d. A block comparison states literal code translation by the same shift. Pair comparisons retain both child inventories; mismatched scalar, block or pair constructors are incompatible. Under the successful shape unifier the compared erased terms agree, so no mixed scalar/block equation is generated.

**Definition 1.20 (Recursive comparison with both directions proved).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.comparisonInventory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.comparisonInventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matching scalar leaves emit their scalar offset equation; matching residual leaves emit the original block offset equation; matching pairs recursively compare both ordered children. For equal erased terms, the inventory holds exactly when the evaluated left code is the supplied shift of the evaluated right code. This equivalence is proved for arbitrary independent natural scalar and code-block assignments.

**Definition 1.21 (The actual natural collapse witness).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.BranchInventory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.BranchInventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A branch inventory is a comparison or a collapse family quantified existentially over one natural number. A collapse uses the same witness n in its three equations at ranks n+1,n,n+2. Separate collapse equations retain their own witnesses.

**Definition 1.22 (All original comparison constructors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.branchInventory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.branchInventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Primitive equations compare with their supplied rank. Shifts retain their original offset. Ordinary constructor and equality comparisons use zero offset. Collapse compares all three named terms against the three scalar constants determined by its single natural witness. The original branch list retains repeated equations.

**Theorem 1.23 (The complete decorated system is equivalent to the original branch system).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_decorated_comparison_equivalence`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_decorated_comparison_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual successful shape unifier S of the entire finite branch list B, and for every independent assignment of natural scalar values and ambient residual codes, the complete branch inventories hold exactly when every original BranchEquation holds on the reconstructed named codes. Both implications retain primitive constants, scalar offsets, ordinary zero offsets and each original existential natural collapse witness. No scalar equivalence or scalar consistency is assumed.

The theorem also identifies the concatenation of every inventory's block edges with exactly sourceOffsetEdges(B,action(p,S)), including repeated and parallel edges. The recursive projection erases only scalar equations. Collapse has no residual edge. Thus the same block equations feed the computed source potentials and minimum normalization above; no replacement graph is introduced. Successful unification supplies the erased comparison equalities; a structural equivalence handles each comparison, and then each original constructor and the entire branch list. Empty lists and empty declared families remain in scope.

**Definition 1.24 (Read actual scalar ranks at their original addresses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sourceScalarRanks`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sourceScalarRanks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a valid primitive address sourceScalarRanks reads its exact natural rank. A default zero is used only elsewhere. Structural reconstruction proves that evaluating every separately decorated named term with these scalar ranks and occurrenceCode gives the entire original named code, so no default affects an explicit primitive position.

**Definition 1.25 (Read the actual occurrence subtree).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.occurrenceCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.occurrenceCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

occurrenceCode(C,o) reads the code subtree of the original named code C(o.name) at o.address, using a fixed default only at invalid addresses. The native source theorem proves every MGU occurrence address is valid before using its code; the default contributes no valid block.

**Theorem 1.26 (Original native solutions supply their own canonical blocks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.native_source_block_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.native_source_block_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite presentation p of the entire declared named family X, original equation list E and actual native solution v, the theorem selects B in branches(E) and an actual successful shape unifier S. Every original selected BranchEquation.Holds remains true of C(x)=encode(v(x)). The theorem reconstructs every original named code from its separately addressed scalar ranks and actual occurrence blocks, and proves the complete branch inventory on these same values. Thus primitive constants, scalar offsets, full block shifts, ordinary zero offsets, equalities, and collapse witnesses r with ranks r,r+1,r+2 remain attached to this same actual solution. For every occurring residual sort there is an actual base occurrence b minimizing computedSourcePotential and natural offsets a(o)=computedSourcePotential(o)-computedSourcePotential(b), with a(b)=0. Its actual occurrenceCode is normal, and every actual occurrence block is literally shiftCode(a(o),occurrenceCode(C,b)); expansion gives the identical original native substitution iterated a(o) times.

The shape factorization is supplied by native_branch_reduction. A structural fit of the decorated MGU terms to C extracts each actual source-offset equation from BranchEquation.Holds, using the same comparison recursion. Descent through the factorized shape proves valid code subtrees and the common ground shape. Reading their ordered leaf ranks gives BlockSolution and the exact fill identities. A nonempty leaf detects zero signed cycles. These derived facts consume source_canonical_block_recovery, whose base and offsets come from source_sort_minimum_base and its computed potential. No BlockSolution, potential, desired subtree identity or desired reconstruction is an external premise. Isolated occurrences, unused names and repeated edges remain in scope. If no sort occurs the conclusion is the empty universal family. This theorem does not assert the image-cover or Theorem 3.2.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.BlockSolution`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.BranchInventory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ComparisonInventory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.DecoratedTerm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.Leaves`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.Potential`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.RankExpression`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ScalarPosition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.ZeroCycles`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.branchInventory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.comparisonInventory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.computedSourcePotential`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.fill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.native_source_block_recovery`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.occurrenceCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.scalarDecorate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.scalarDecorateFrom`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedEdges`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedGraph`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.signedWeight`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sortEdges`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sourceRelaxation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.sourceScalarRanks`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_canonical_block_recovery`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_decorated_comparison_equivalence`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover.source_sort_minimum_base`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction](NativePositiveBranchReduction.md)
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual](../../../../Combinatorics/Graph/LayeredCirculation/SupplierDual.md)
