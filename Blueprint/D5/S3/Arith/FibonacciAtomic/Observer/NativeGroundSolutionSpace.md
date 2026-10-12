# All native ground solutions and constraint pullback

## Abstract

All native ground solutions and constraint pullback.

**Definition 1.1 (Native source carrier).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Source`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source is the repository FreeMagma Bool carrier, preserving both Boolean generators and ordered binary trees.

**Definition 1.2 (Finite original equations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Equations`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Equations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equations are finite lists of pairs of original Term X expressions. All original variables remain in X, even when absent from these equations.

**Definition 1.3 (Faithful equation encoding).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeEquations`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both sides of every original equation are encoded by the same complete variable presentation.

**Definition 1.4 (Original ground solutions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Sol`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Sol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An assignment from all original X to native Source solves C exactly when evaluation agrees on both sides of every equation in C.

**Definition 1.5 (Ground value lookup).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundValue`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A successfully decoded original identifier receives the encoding of its assigned native ground source.

**Definition 1.6 (Full finite ground assignment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite substitution binds every original identifier to its assigned native ground tree and leaves other identifiers unbound.

**Theorem 1.7 (Every original coordinate is bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_find`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_find` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original x, the ground substitution lookup at code x is exactly some of the ground encoding of v x.

**Theorem 1.8 (Other identifiers stay unbound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_other`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_other` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every identifier distinct from every original code, lookup in the finite ground substitution is none.

**Theorem 1.9 (Encoding commutes with evaluation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_evaluate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_evaluate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original native term, applying the full ground substitution to its encoding equals the ground encoding of evaluation under that assignment.

**Theorem 1.10 (Ground encoding is injective).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeGround_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeGround_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The encoding retains both distinct Boolean labels and both ordered children at every branch.

**Theorem 1.11 (A common finite substitution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_sol`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_sol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original ground solution produces one finite Strata substitution solving all encoded equations simultaneously.

**Theorem 1.12 (Native satisfiability prevents failure).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.native_complete`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.native_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original ground solution v on all X is encoded as one finite groundSubst using the complete presentation enumeration. groundSubst_evaluate proves that this same substitution solves each encoded equation; absorption of the empty state is automatic. The unrestricted Constraints.unify_complete proof then produces success of the actual native call. Both the finite evaluation correspondence and unrestricted completeness remain live in this application; no groundness or well-formedness premise is imposed on the arbitrary R of the generic completeness theorem.

**Theorem 1.13 (Actual successful output shape).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_native`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every stored value of a successful encoded-native output has the exact native constructor shape.

**Theorem 1.14 (Equation identifier support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.equations_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.equations_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every free identifier in the encoded equation list is the code of an original variable.

**Theorem 1.15 (Output value support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_supported`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_supported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every free identifier of every stored successful output value remains in the original variable alphabet.

**Definition 1.16 (Total original-variable action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original x, decode the actual substituted code x. The total action includes aliases, unbound variables and variables unused by C; its fallback is unreachable after actual native success.

**Theorem 1.17 (The total action is the actual substitution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_encode`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_encode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every successful native output and every x in the full original type, encoding action x equals the actual Strata substitution applied to the variable code x.

**Definition 1.18 (Actual bound subset).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.D`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D consists exactly of original variables whose identifiers occur in the successful substitution key set.

**Definition 1.19 (Complementary parameter type).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Y`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Y` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Y is the subtype of all original variables outside D, including unused original variables.

**Definition 1.20 (Actual term variable support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.termVars`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.termVars` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The variable list retains every variable occurrence and concatenates the lists of ordered children.

**Theorem 1.21 (Exact encoded support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encode_variables`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encode_variables` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The free-variable list of an encoded native term is exactly the list of its original variables mapped through the code.

**Theorem 1.22 (Support lies in the complement).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every variable occurring in any total action value lies outside the actual key subset D. The algorithm invariant excludes every key from every substituted value.

**Theorem 1.23 (Identity on unbound original variables).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original variable outside D, its total action is exactly that same variable leaf.

**Theorem 1.24 (Exact bound characterization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.bound_iff_nonidentity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.bound_iff_nonidentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every successful output and original x, membership in D is equivalent to the total action being different from the original variable leaf.

**Definition 1.25 (Relabeling supported terms).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restrictTerm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restrictTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A term whose variables lie outside D is relabeled into the complementary subtype Y, preserving all Boolean leaves and ordered branches.

**Definition 1.26 (Normalized parameter terms).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.sigma`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total action at every original x is relabeled into Term Y using its proved support in Y. No recursive normalization algorithm is introduced.

**Definition 1.27 (The same extension map).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary w from Y to native Source, Ext w at original x is evaluation of sigma x under w.

**Definition 1.28 (Exact original restriction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An original assignment is restricted to the complementary original-variable subtype Y.

**Theorem 1.29 (Relabeling preserves evaluation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.evaluate_restrictTerm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.evaluate_restrictTerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating a relabeled term under an assignment restricted to Y equals evaluating the original term under the whole original assignment.

**Theorem 1.30 (Extension has exact restriction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction_Ext`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction_Ext` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary assignment w on Y, restricting Ext w returns exactly w.

**Theorem 1.31 (Every original ground solution factors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original ground solution v on all X, Ext of its restriction equals v at every original coordinate. The original arbitrary-substitution MGU law supplies the factorization.

**Theorem 1.32 (Empty support produces native ground).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.shape_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.shape_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A type tree with exact native Shape and empty free-variable list is the encoding of an actual Boolean-leaf ground source.

**Theorem 1.33 (Ground encoding has empty support).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeGround_freeVars`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeGround_freeVars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual native ground source encodes to a tree with no free variables.

**Theorem 1.34 (Exact unique native ground detection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.native_ground_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.native_ground_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every tree having exact native Shape, empty variable support is equivalent to existence of exactly one native Source tree with that encoding. The Shape hypothesis excludes foreign nullary constructors and bit vectors.

**Definition 1.35 (Native simultaneous action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.substitute`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.substitute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing free-magma lift extends a total assignment of native terms to simultaneous substitution on all original terms.

**Theorem 1.36 (Evaluation composition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.substitute_evaluate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.substitute_evaluate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating simultaneous term substitution equals evaluating the original term under the assignment obtained by evaluating each substituted variable term.

**Theorem 1.37 (Native action and Strata substitution commute).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_substitute_encode`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_substitute_encode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Encoding simultaneous total native action on any original term equals actual Strata substitution on that term encoding.

**Theorem 1.38 (Normalization supplied by the algorithm).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original x after actual native success, another simultaneous application of the total action leaves action x unchanged. The original SubstInfo well-formedness and subst_idempotent theorem supply normalization.

**Definition 1.39 (Comparison assignment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.fill`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.fill` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A parameter assignment is extended to original X by giving bound coordinates one fixed Boolean leaf. Those coordinates never occur in sigma and cannot affect Ext.

**Theorem 1.40 (Filling preserves parameter values).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction_fill`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction_fill` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting the comparison assignment to Y returns the supplied parameter assignment exactly.

**Theorem 1.41 (Extension evaluates the total action).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_evaluate_action`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_evaluate_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ext w at any original x equals evaluation of action x under the comparison assignment. This uses only relabeling and the support in Y.

**Theorem 1.42 (All parameter assignments give solutions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_sol`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_sol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every successful actual native output and every arbitrary w on Y, the same Ext w solves every original equation in C. No injectivity of arbitrary ground evaluation is assumed.

**Definition 1.43 (The complete ground solution set).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.solutionEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.solutionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original variable type with complete finite presentation, every finite original equation list C and every successful output S from empty substitution, extension and restriction form the exact equivalence (Y to Source) with the subtype of all original assignments solving C. Empty X and empty C remain included.

**Definition 1.44 (All original disequalities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Diseq`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Diseq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every old disequality is evaluated on the entire original assignment. None is dropped when its variables are absent from the new equation list.

**Definition 1.45 (Exact guard and disequality pullback).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.constrainedEquiv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.constrainedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every old disequality list Delta and arbitrary predicate G on original assignments, the same extension and restriction give an equivalence between parameter assignments satisfying Diseq Delta (Ext w) and G (Ext w), and original assignments satisfying Sol C v, Diseq Delta v and G v. This constrained parameter subtype is not assumed to be a product, and no decision procedure for arbitrary G is asserted.

**Theorem 1.46 (All-variable normalized action laws).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.total_action_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.total_action_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every successful output and every original x, simultaneous action fixes action x; every variable in action x belongs to Y; outside D the action is the original variable; and D is exactly the set of nonidentity actions.

**Theorem 1.47 (Keys stay original).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_keys`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_keys` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every key in a successful output is an original-variable code. The original keys_incl supplier prevents introduction of foreign identifiers.

**Definition 1.48 (Exact native ground decoder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundDecoder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundDecoder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The executable decoder admits only the two nullary Boolean leaves and ordered binary pairs. It rejects variables, bit vectors, foreign names and malformed arities.

**Theorem 1.49 (Ground decoding is exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundDecoder_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundDecoder_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decoding a type tree to a particular Source succeeds exactly when the tree is that source encoding. No foreign constructor can be mistaken for native ground.

**Definition 1.50 (The complete normalized solution interface).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Parameterization`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Parameterization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A successful state supplies its actual original-variable keys, normalized total action, complementary parameters, exact nonidentity and ground characterizations, and all-ground-solutions and constrained-space equivalences.

**Definition 1.51 (Actual algorithm parameterization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.parameterization`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.parameterization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every successful encoded-native output realizes the full Parameterization interface. Every original variable remains represented; every old disequality and arbitrary already established guard is pulled back along the same Ext.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.D`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Diseq`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Equations`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_evaluate_action`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_restriction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Ext_sol`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Parameterization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Sol`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Source`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.Y`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_encode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_idempotent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_identity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_substitute_encode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.action_support`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.bound_iff_nonidentity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.constrainedEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeEquations`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeGround_freeVars`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encodeGround_injective`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.encode_variables`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.equations_supported`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.evaluate_restrictTerm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.fill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundDecoder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundDecoder_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_evaluate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_find`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_other`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundSubst_sol`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.groundValue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.native_complete`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.native_ground_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_keys`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_native`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.output_supported`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.parameterization`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restrictTerm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction_Ext`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.restriction_fill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.shape_ground`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.sigma`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.solutionEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.substitute`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.substitute_evaluate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.termVars`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.total_action_spec`
- Dependency: [D5/S0/Rewriting/UnificationCompleteness](../../../../S0/Rewriting/UnificationCompleteness.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](../GenealogicalFiberTransport.md)
