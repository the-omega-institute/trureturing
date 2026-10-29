# Original expressions and their named equations

## Abstract

Expression naming and unrestricted mixed native soundness

Source is the algebra of finite ordered Boolean trees. Pairing is its actual constructor, and rho is the interpreted native substitution. MixedExpr uses fixed ground trees, fixed natural powers of original variables, and pairing. A positive presentation is a finite list of pairs of these expressions. The list may be empty or contain repetitions. X retains every original variable, including unused variables; X may be Fin d, also when d is zero. No tree size or depth bound is imposed.

**Definition 1.1 (Disjoint input and auxiliary namespaces).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Name`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Name` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Name X is X plus MixedExpr X. Inputs are injected on the left and expression names on the right. Every repeated use of an expression has the same auxiliary name. This namespace itself is not finite: the finite lowering emits only the definitions needed by the supplied finite expressions. The finite presentation below restricts this namespace to the names read by the lowering and all declared inputs.

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

**Definition 1.10 (Names read by one native equation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.equationNames`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.equationNames` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List every input name of the equation, including its output. Repeated names are retained.

**Definition 1.11 (Finite support with the entire original tuple).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.nameSupport`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.nameSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For d original inputs, concatenate every inl(i), i in Fin d, with all names read by flatten E, and deduplicate this finite list. Auxiliary expressions are identified by their actual syntax. No input is removed when it is absent from the equations.

**Definition 1.12 (The actual finite carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.FiniteName`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.FiniteName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FiniteName E is the subtype of Name(Fin d) belonging to nameSupport E. It contains all declared inputs and every auxiliary name used by a lowered equation.

**Definition 1.13 (Embed every original component).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.inputName`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.inputName` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inputName E i is the original input name in the finite carrier. Its underlying name is inl(i), so distinct original components remain distinct, including unused components.

**Definition 1.14 (Present the actual finite carrier to the unifier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.namePresentation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.namePresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the deduplicated support list's explicit equivalence with its finite index interval and transport the existing finPresentation. This constructs the code and inverse decoder from the actual supplied finite syntax, without a default element or an assumed presentation of an infinite namespace.

**Definition 1.15 (Reindex every lowered equation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finiteEquations`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finiteEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each name in an equation of flatten E has a proof of support membership. Reindex that equation by the corresponding subtype elements, retaining the original list order and all repeated equations.

**Definition 1.16 (Restrict the same actual named assignment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finiteExtend`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finiteExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

finiteExtend E v reads extend v at the underlying supported name. In particular its value at inputName E i is v(i). Exact finite lowering and the existing native branch reduction supply a successful total MGU and its factorization at every supported name.

Finite scalar guards and native templates.

**Definition 1.17 (Affine natural rank atoms).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Scalar`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Scalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar is a fixed natural constant, or n(i)+a for a natural parameter n(i) and a fixed natural offset a. Thus its integer interpretation is affine, with coefficient zero or one.

Read a scalar parameter. Scalar.value evaluates the constant or the parameter with its fixed offset in the natural numbers.

**Definition 1.18 (Finite mixed ambient syntax).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Pattern`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Pattern` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A pattern is an explicit scalar leaf, a residual native block of sort i with a fixed natural offset a, or a pair of patterns. Different residual sorts receive independently supplied native values. Equal values across different sorts are permitted.

**Definition 1.19 (Decorate exactly the actual shape leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Decoration`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Decoration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Decoration k m s is defined recursively on the supplied free-shape term s. An explicit primitive leaf carries a Scalar k. A residual leaf carries an element of Fin m and a fixed natural offset. A pair carries the decorations of its two children. Empty scalar or native dimensions therefore require no nonexistent selector when the corresponding leaves are absent.

**Definition 1.20 (Construct every named mixed pattern).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.assemble`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.assemble` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

assemble traverses the actual free-shape term with its dependent decoration: explicit leaves become scalar patterns, residual occurrences become shifted native blocks, and binary nodes become pairs. A named family s and decorations d thus give the concrete pattern of every original and auxiliary name. Shared names reuse the same supplied term and decoration.

Assemble ambient codes before expansion. Scalar leaves become primitive codes; a residual block becomes shiftCode a (encode (z i)); pairs become raw ambient pairs. Pair assembly uses no smart normalization and adds no normality test.

Return the established native mixed syntax. A constant scalar becomes a fixed ground tree; a parameter scalar becomes the ranked residual rho to power a of T(n i); a block becomes rho to power a of z i; pairs remain actual native pairs. These are RankedExpr templates, using the existing rankedEval interpretation. Structural recursion proves that expanding Pattern.code is exactly rankedEval of this template.

**Definition 1.21 (A finite conjunction of affine integer equalities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Guard`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Guard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Guard is a list of pairs of scalar atoms. It has no native parameter fields.

The arithmetic domain. Each scalar pair is required to have equal integer values. Its arguments range over all natural scalar tuples. No positivity, shape, disequality, source bound, or normality predicate on residual native values occurs in this guard.

**Definition 1.22 (Extract scalar equalities from matching decorated syntax).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.compare`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.compare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two scalar leaves emit their affine equality. Two blocks succeed exactly when their residual sort and fixed offset agree syntactically, emitting no arithmetic condition. Two pairs recursively compare corresponding children and concatenate their guards. All other constructor combinations fail. Success is a sufficient symbolic comparison; no completeness of this procedure over arbitrary native equalities is asserted. In particular accidental equal native parameters are allowed, while the procedure need not recognize every equality caused by them.

Translate explicit ranks. A fixed natural shift adds its offset to constants and parameter offsets.

Translate every ambient leaf. Translation recursively shifts explicit scalar leaves and adds the supplied shift to every residual block offset. Pair structure is preserved. Its assembled code equals shiftCode of the unshifted assembled code.

**Definition 1.23 (Extract every selected branch comparison).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.branchComparisons`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.branchComparisons` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Primitive equations compare the assigned output pattern with their fixed scalar. Shift equations compare the output with syntactic translation of the input; ordinary equations compare it with a raw pair; equalities compare their two named patterns. A collapse uses a supplied scalar atom c(b) and emits all three equations: left rank value(c(b))+1, right rank value(c(b)), and output rank value(c(b))+2. The same scalar is shared in those three comparisons.

**Definition 1.24 (Combine a finite comparison family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.collect`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.collect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

collect recursively runs compare on every pattern pair and concatenates the resulting scalar guards. Failure discards the attempted decorated syntax. Success proves all ambient comparisons for every native filling satisfying the combined scalar guard.

**Theorem 1.25 (Unrestricted native soundness of extracted guards).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.guarded_mixed_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.guarded_mixed_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take any actual finite branch B of the lowered original expressions, any named free-shape family s, a dependent decoration d of every actual shape leaf, and an assignment c of scalar atoms to collapse equations. If collect succeeds on every comparison extracted from B, then for every natural tuple n satisfying its returned affine guard and every arbitrary native tuple z, the original expressions are equal at the outputs rankedEval n z (assemble(s(inl x),d(inl x))). Scalar comparisons give equal primitive ranks. Matching residual blocks have identical shifts of the same encoded native parameter. Matching pairs reconstruct equal ambient codes. The three collapse comparisons provide their explicit natural rank. Existing arbitrary-code branch expansion then proves the original native equations. The hypotheses are finite syntactic comparison success and the extracted scalar equations, rather than a hypothesis asserting the desired original native equalities.

**Definition 1.26 (Enumerate explicit leaves of the actual free shape).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.scalarAddresses`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.scalarAddresses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An explicit primitive contributes its empty address, a residual variable contributes none, and a pair prefixes false or true to its two lists of addresses. This enumeration traverses the total MGU term of every supported name.

**Definition 1.27 (Read a rank at an actual code address).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankAt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read the primitive rank at the specified subtree address, with zero as a total fallback. The extraction theorem proves that the fallback is excluded for every enumerated explicit MGU leaf.

**Definition 1.28 (Named scalar and collapse coordinates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.RankSlot`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.RankSlot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An explicit slot retains its name and ordered address. A collapse slot retains its output, left input and right input. Slots distinguish positions while repeated uses of a named value keep that same actual value.

**Definition 1.29 (Construct the finite scalar-coordinate list).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankSlots`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankSlots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Traverse the presentation's entire name enumeration and every explicit leaf of its total MGU term, then append one slot for each occurrence of a collapse equation in the actual branch. Residual blocks contribute no scalar slot. Empty lists and zero scalar dimensions retain their ordinary meanings.

Read each coordinate from actual canonical codes. An explicit slot reads its named subtree's primitive rank. A collapse slot reads the primitive rank of its right input, the same r shared by all three collapse equations.

**Definition 1.30 (Extract the natural tuple automatically).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankParameters`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankParameters` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Index rankSlots by its finite length and read RankSlot.value at each index from the same actual code assignment. This gives a finite tuple of natural numbers, with no supplied decorations or assumed successful comparison extraction.

Exact meaning of each extracted coordinate. An explicit coordinate r means that the actual named subtree is the primitive code [r]. A collapse coordinate r means simultaneously that its actual left input is [r+1], its right input is [r], and its output is [r+2].

**Theorem 1.31 (Actual-solution extraction on the finite total MGU).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finite_rank_extraction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finite_rank_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite original presentation E on the whole declared Fin d tuple and every actual solution v, first retain the identity finiteExtend E v (inputName E i) = v(i) at every original input, then select an actual branch of finiteEquations E and a successful total MGU of its shape equations. Every supported name factors through that MGU at the shape of its actual canonical code. The automatically constructed rankParameters tuple satisfies RankSlot.Correct at every index of rankSlots. Structural induction on the MGU term proves that each explicit leaf address lands at a primitive of the actual code. Reading that primitive recovers its rank. Actual branch soundness at each chosen collapse supplies all three equations with the rank read from its right input. The same construction includes all unused input names, repetitions, an empty declared tuple and branches with no scalar slots.

**Definition 1.32 (Use the actual finite scalar-coordinate index).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.slotScalar`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.slotScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Look up an explicit or collapse slot in rankSlots and return its parameter with zero added offset. The total fallback is the constant zero, but membership at every actual explicit leaf and selected collapse excludes that fallback. Evaluation at rankParameters recovers the same actual slot value.

**Definition 1.33 (Keep the complete total-MGU occurrence list).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualOccurrences`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualOccurrences` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reuse occurrenceVertices on every name in the actual finite presentation. The list retains each residual name, ordered address and residual sort, including occurrences in isolated unused input outputs.

**Definition 1.34 (Automatically decorate an actual shape subtree).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.decorateAt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.decorateAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recurse through the actual MGU subtree at a proved address. An explicit primitive receives slotScalar for that name and address. A residual receives its finite sort and natural offset from a map defined only at proved actual occurrences. Pairs recurse at the two appended child addresses. This dependent domain permits zero residual dimensions when no residual occurs.

**Definition 1.35 (Construct each full named decoration).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.automaticDecoration`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.automaticDecoration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply decorateAt at the empty address of the actual total-MGU term of the named value. No scalar decoration is supplied as a premise.

**Definition 1.36 (Construct the shared collapse scalar).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.automaticCollapse`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.automaticCollapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each selected collapse uses its actual collapse slot in the same finite scalar tuple. Its three branch comparisons therefore share one parameter, shifted by one, zero and two. Other branch constructors do not use this scalar.

Retain scalar versus residual syntax. Erase scalar ranks and block labels, retaining different leaf tags for explicit scalars and residuals and preserving ordered pair constructors. An actual residual that happens to fill with a primitive is still a residual in this frame.

**Definition 1.37 (The precise remaining residual comparison condition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.blockCompatible`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.blockCompatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At two matching block leaves require the same finite sort and fixed natural offset. At matching pairs recurse on both children. Other combinations contribute no residual condition; successful MGU frame matching independently excludes mismatched constructors.

Read actual scalar leaves and pair constructors. At a scalar leaf, the actual code must be the primitive with its evaluated rank. At a pair, the actual code must be the corresponding raw pair and both children must agree. A residual leaf contributes no assertion about its actual block. This predicate records scalar and constructor information and is not full code reconstruction.

**Definition 1.38 (Enumerate the finite actual residual sorts).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualSorts`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualSorts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map the complete occurrence list to its residual labels and deduplicate. This includes every isolated sort of an unused original name; no default sort is introduced for an empty list.

**Definition 1.39 (Index a proved actual residual sort).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualSortIndex`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualSortIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successful actual MGU supplies the exact occurrence-membership theorem. Use that membership to index the residual label in residualSorts. Thus the finite sort index is constructed from the actual MGU and needs no default element.

**Definition 1.40 (Combine automatic sorts with occurrence offsets).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.sortedBlocks`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.sortedBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each proved residual occurrence receives its computed residualSortIndex and the supplied natural occurrence offset. Only these offsets remain external block data; scalar indices, collapse indices and finite residual sorts have already been constructed.

**Theorem 1.41 (Automatic source scalar guards with an exact residual obstruction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finite_guard_extraction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finite_guard_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original solution v on the entire Fin d tuple, retain every input identity and select an actual finite branch and successful total MGU. The returned witnesses include every actual branch equation and the same-assignment shape factorization at every supported name. For every assignment of natural offsets to its actual residual occurrences, use sortedBlocks and automaticDecoration to construct the named patterns and use automaticCollapse for their shared collapse scalars. At the rank tuple read from the same canonical codes, every named pattern agrees with its actual code in the precise scalar-and-pair sense above. Moreover there exists a successful collect result whose entire affine integer guard holds at those actual ranks if and only if blockCompatible holds throughout that same actual branchComparisons traversal. The proof derives comparison frames from the successful MGU equations. It derives scalar agreement from actual primitive constants, original fixed shifts, zero-offset ordinary pairs and equalities, and all three actual collapse equations. Recursive comparison then emits and verifies the scalar equalities. Neither successful collect nor scalar guard satisfaction is assumed. Residual offset compatibility is exposed as the exact remaining condition, rather than asserted to exist. The tuple, empty presentations and zero dimensions remain quantified.

Concrete lowering, finite total-name reduction, automatic finite scalar and residual-sort decorations, the exact scalar-guard obstruction theorem and arbitrary-filling soundness hold on the original source objects. The independent signed-cycle/minimum-base supplier must still construct compatible nonnegative offsets on the actual sourceOffsetEdges, connect that edge law to blockCompatible in this traversal, and recover every actual residual block from its normal minimum block. Full actual-code reconstruction, lifting the finite-name templates to unrestricted original-expression soundness, construction of the finite chart list and both inclusions of the universal cover remain open. No corresponding supplier result or whole-cover conclusion is assumed here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Decoration`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.FiniteName`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Guard`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Name`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Pattern`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.RankSlot`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.Scalar`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.assemble`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.automaticCollapse`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.automaticDecoration`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.blockCompatible`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.branchComparisons`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.collect`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.compare`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.decorateAt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.definitions`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.equationNames`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.expression_branch_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.extend`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finiteEquations`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finiteExtend`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finite_guard_extraction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.finite_rank_extraction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.flatten_expansion_sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.groundDefinitions`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.guarded_mixed_sound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.inputName`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.namePresentation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.nameSupport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankAt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankParameters`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.rankSlots`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualOccurrences`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualSortIndex`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.residualSorts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.root`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.scalarAddresses`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.slotScalar`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeMixedImageConstruction.sortedBlocks`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction](NativePositiveBranchReduction.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformResidualRealization](../NativeUniformResidualRealization.md)
