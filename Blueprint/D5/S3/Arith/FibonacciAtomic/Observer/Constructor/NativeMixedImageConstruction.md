# Original expressions and their named equations

## Abstract

Expression naming and unrestricted mixed native soundness

Source is the algebra of finite ordered Boolean trees. Pairing is its actual constructor, and rho is the interpreted native substitution. MixedExpr uses fixed ground trees, fixed natural powers of original variables, and pairing. A positive presentation is a finite list of pairs of these expressions. The list may be empty or contain repetitions. X retains every original variable, including unused variables; X may be Fin d, also when d is zero. No tree size or depth bound is imposed.

**Definition 1.1 (Disjoint input and auxiliary namespaces).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Name`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Name` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Name X is X plus MixedExpr X. Inputs are injected on the left and expression names on the right. Every repeated use of an expression has the same auxiliary name. This namespace itself is not finite: the finite lowering emits only the definitions needed by the supplied finite expressions. Reindexing its finite support by a finite presentation remains a separate construction.

**Definition 1.2 (Name an original expression).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.root`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

root injects an expression into the auxiliary namespace without changing its variables or ground parameters.

**Definition 1.3 (Expand ground parameters into finite native syntax).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.groundDefinitions`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.groundDefinitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Boolean leaf has its primitive rank zero or one. A pair recursively includes both ground definitions and the pairing equation for their roots. This operation terminates by recursion on the supplied finite ground tree.

**Definition 1.4 (Lower every expression constructor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.definitions`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.definitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A residual occurrence rho to power a of x becomes a shift from the original input name x to its expression root. A pair includes the definitions of its two children and an ordinary native pairing equation between their roots. Repeated definitions are retained.

**Definition 1.5 (Retain all positive equalities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each original pair of expressions, flatten concatenates both lists of definitions and an equality between the two expression roots. This is a concrete terminating function on the original syntax. It does not assume that the original positive equations already hold.

**Definition 1.6 (Evaluate every named subexpression at the same source assignment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.extend`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.extend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

extend keeps the input assignment on the left and evaluates the named expression on the right. No new choice of original source is made.

**Theorem 1.7 (Exact lowering at the original assignment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All original positive expression equalities hold at v if and only if every emitted named equation holds at extend v. For the forward direction, ground recursion verifies both primitive leaves and actual native pairs; expression recursion verifies each fixed power and each ordered pair. The reverse direction reads the emitted root equality for every supplied comparison. Unused input values remain those of v.

**Theorem 1.8 (Finite canonical branches from original expression syntax).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.expression_branch_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.expression_branch_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original expression equalities hold exactly when one member of branches(flatten E) holds on the actual canonical encodings of extend v. The concrete lowering theorem supplies the native named equations. The existing exact constructor-case theorem then chooses ordinary or collapse cases from those same actual values. This finite branch list does not enumerate scalar ranks or native sources, and still retains code equations rather than unrestricted image charts.

**Theorem 1.9 (Expand arbitrary ambient branch solutions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_expansion_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_expansion_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any selected branch of flatten E, let u assign arbitrary finite ambient codes to names and satisfy that branch's code equations. Then expanding u on the original input names satisfies every original expression equality. Induction through the definitions identifies each expanded auxiliary value with evaluation of its original expression. Existing branch soundness supplies interpreted shifts, ordinary pairs, and the primitive collapse recurrence. Normality and injectivity of expansion are not premises. In particular an ordinary pair of consecutive primitive ranks may collapse after filling without invalidating its native pairing equation.

Finite scalar guards and native templates.

**Definition 1.10 (Affine natural rank atoms).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Scalar`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Scalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar is a fixed natural constant, or n(i)+a for a natural parameter n(i) and a fixed natural offset a. Thus its integer interpretation is affine, with coefficient zero or one.

Read a scalar parameter. Scalar.value evaluates the constant or the parameter with its fixed offset in the natural numbers.

**Definition 1.11 (Finite mixed ambient syntax).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Pattern`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Pattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pattern is an explicit scalar leaf, a residual native block of sort i with a fixed natural offset a, or a pair of patterns. Different residual sorts receive independently supplied native values. Equal values across different sorts are permitted.

**Definition 1.12 (Decorate exactly the actual shape leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Decoration`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Decoration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decoration k m s is defined recursively on the supplied free-shape term s. An explicit primitive leaf carries a Scalar k. A residual leaf carries an element of Fin m and a fixed natural offset. A pair carries the decorations of its two children. Empty scalar or native dimensions therefore require no nonexistent selector when the corresponding leaves are absent.

**Definition 1.13 (Construct every named mixed pattern).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.assemble`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.assemble` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

assemble traverses the actual free-shape term with its dependent decoration: explicit leaves become scalar patterns, residual occurrences become shifted native blocks, and binary nodes become pairs. A named family s and decorations d thus give the concrete pattern of every original and auxiliary name. Shared names reuse the same supplied term and decoration.

Assemble ambient codes before expansion. Scalar leaves become primitive codes; a residual block becomes shiftCode a (encode (z i)); pairs become raw ambient pairs. Pair assembly uses no smart normalization and adds no normality test.

Return the established native mixed syntax. A constant scalar becomes a fixed ground tree; a parameter scalar becomes the ranked residual rho to power a of T(n i); a block becomes rho to power a of z i; pairs remain actual native pairs. These are RankedExpr templates, using the existing rankedEval interpretation. Structural recursion proves that expanding Pattern.code is exactly rankedEval of this template.

**Definition 1.14 (A finite conjunction of affine integer equalities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Guard`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Guard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Guard is a list of pairs of scalar atoms. It has no native parameter fields.

The arithmetic domain. Each scalar pair is required to have equal integer values. Its arguments range over all natural scalar tuples. No positivity, shape, disequality, source bound, or normality predicate on residual native values occurs in this guard.

**Definition 1.15 (Extract scalar equalities from matching decorated syntax).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.compare`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.compare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two scalar leaves emit their affine equality. Two blocks succeed exactly when their residual sort and fixed offset agree syntactically, emitting no arithmetic condition. Two pairs recursively compare corresponding children and concatenate their guards. All other constructor combinations fail. Success is a sufficient symbolic comparison; no completeness of this procedure over arbitrary native equalities is asserted. In particular accidental equal native parameters are allowed, while the procedure need not recognize every equality caused by them.

Translate explicit ranks. A fixed natural shift adds its offset to constants and parameter offsets.

Translate every ambient leaf. Translation recursively shifts explicit scalar leaves and adds the supplied shift to every residual block offset. Pair structure is preserved. Its assembled code equals shiftCode of the unshifted assembled code.

**Definition 1.16 (Extract every selected branch comparison).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.branchComparisons`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.branchComparisons` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Primitive equations compare the assigned output pattern with their fixed scalar. Shift equations compare the output with syntactic translation of the input; ordinary equations compare it with a raw pair; equalities compare their two named patterns. A collapse uses a supplied scalar atom c(b) and emits all three equations: left rank value(c(b))+1, right rank value(c(b)), and output rank value(c(b))+2. The same scalar is shared in those three comparisons.

**Definition 1.17 (Combine a finite comparison family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.collect`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.collect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

collect recursively runs compare on every pattern pair and concatenates the resulting scalar guards. Failure discards the attempted decorated syntax. Success proves all ambient comparisons for every native filling satisfying the combined scalar guard.

**Theorem 1.18 (Unrestricted native soundness of extracted guards).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.guarded_mixed_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.guarded_mixed_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take any actual finite branch B of the lowered original expressions, any named free-shape family s, a dependent decoration d of every actual shape leaf, and an assignment c of scalar atoms to collapse equations. If collect succeeds on every comparison extracted from B, then for every natural tuple n satisfying its returned affine guard and every arbitrary native tuple z, the original expressions are equal at the outputs rankedEval n z (assemble(s(inl x),d(inl x))). Scalar comparisons give equal primitive ranks. Matching residual blocks have identical shifts of the same encoded native parameter. Matching pairs reconstruct equal ambient codes. The three collapse comparisons provide their explicit natural rank. Existing arbitrary-code branch expansion then proves the original native equations. The hypotheses are finite syntactic comparison success and the extracted scalar equations, rather than a hypothesis asserting the desired original native equalities.

These results establish concrete lowering and the arbitrary-filling soundness chain. They do not extract all decorations and their finite scalar indexing from an arbitrary successful shape unifier, prove that every consistent branch admits successful comparison extraction, synthesize the finite list of image charts, or prove same-source completeness of that list. Those steps require occurrence decoration and the signed-cycle, minimum-base and effective-potential supplier. The public universal finite image-cover theorem therefore requires these additional constructions. No existence of potentials or of an exact cover is assumed here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Decoration`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Guard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Name`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Pattern`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Scalar`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.assemble`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.branchComparisons`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.collect`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.compare`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.definitions`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.expression_branch_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.extend`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_expansion_sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.groundDefinitions`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.guarded_mixed_sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.root`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction](NativePositiveBranchReduction.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization](../NativeUniformResidualRealization.md)
