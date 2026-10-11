# Delayed leaf certificates for arbitrary templates

## Abstract

One delayed physical probe per original leaf identifies any known finite template.

The template g is known finite native syntax, while the competitor u ranges over all native finite trees. No equal-shape, equal-size, positive-image or finite-competitor premise is imposed. The common natural epoch N changes physical addresses and expected labels. Every requested address and every expected reply is computed from N and g.

**Definition 1.1 (Literal label reply).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafReply`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

leafReply(true)=alpha and leafReply(false)=beta.

**Definition 1.2 (Known frontier label).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafBit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

leafBit(g,p) tests whether the known template reply is alpha. On its original leaves this is precisely the Boolean leaf label. The beta default outside the original frontier is never used to construct a certificate entry.

**Definition 1.3 (Label-dependent physical delay).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafDelay`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafDelay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

leafDelay(N,b)=N/2+(N%2) times the beta indicator, which is zero for alpha and one for beta.

**Definition 1.4 (Expected delayed leaf).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.expected`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.expected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At even epochs the expected reply is the original leaf label. At odd epochs the expected alpha and beta labels are swapped. Both expected replies are actual leaf labels.

**Definition 1.5 (One query per original leaf).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateQueries`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateQueries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map the original leaf list p of g, in left-to-right order, to p followed by rights(leafDelay(N,leafBit(g,p))). The generator inspects only the known template.

**Definition 1.6 (Known expected list).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateExpected`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateExpected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map the same original leaf list to expected(N,leafBit(g,p)), preserving exactly the same chronological order as templateQueries.

**Definition 1.7 (Total terminal Boolean output).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateCheck`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compare the complete supplied reply list with templateExpected. A wrong reply or a wrong list length returns false. This compares finite replies, never unknown source trees.

**Definition 1.8 (Unrestricted semantic matching).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.DelayedMatches`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.DelayedMatches` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original leaf p of g, the actual current reply at its generated probe equals the generated expected leaf. The definition quantifies all native competitor trees without a shape promise.

**Definition 1.9 (Rightmost original leaf).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.rightTip`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.rightTip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A leaf has right-tip depth zero and its own label. Pair(x,y) adds one to the right-tip depth of y and keeps its label. Its physical all-right original address belongs to the complete leaf list.

**Theorem 1.10 (Delayed evidence reflects original leaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_leaf_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_leaf_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all N,g,u, delayed matching implies equality of the original replies of u and g at every original leaf of g. A branch template cannot collapse to a competing leaf. Its rightmost leaf has positive relative depth, so the delayed probe either passes beyond that leaf image or gives the wrong label. In particular, at N=1, pair(alpha,alpha) versus beta is rejected by the right probe returning alpha instead of the expected beta, rather than by an absent reply.

**Theorem 1.11 (Exact whole-tree identification).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N,g,u, DelayedMatches(N,g,u) holds if and only if u=g. The forward direction applies the existing unrestricted zero-delay source_foundation leaf rigidity directly to delayed_leaf_reflection. The reverse direction recursively verifies each actual delayed leaf. Iterated pair preservation is the direct Mathlib Semiconj2 iteration applied to substitution.map_mul.

**Definition 1.12 (Original leaf word sum).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafAddressSum`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafAddressSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

leafAddressSum(g) is the sum of the lengths of the original leaf list.

**Definition 1.13 (Exact maximum generated length).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayedRadius`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayedRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map every original leaf p to length(p)+N/2+(N%2) times its beta indicator, and take the maximum with zero as empty-list default. Native sources have at least one leaf, so this is the maximum over the nonempty frontier.

**Theorem 1.14 (Exact three-coordinate resources).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_resources`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_resources` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generated physical query list has no duplicates and length exactly FreeMagma.length(g). Its total address length is leafAddressSum(g)+(N/2) times FreeMagma.length(g)+(N%2) times the beta component of composition(g). Its maximum address length is delayedRadius(N,g). Probe distinctness uses the prefix incomparability of original leaves: two equal extended words would give comparable original leaf prefixes, hence identical leaves. The existing native total and beta leaf counts identify the coefficients.

**Theorem 1.15 (Finite full-list checker).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_service`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_service` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The executable listController terminates with fuel length(templateQueries)+1, recording the actual ordered replies and returning templateCheck. Its output is true exactly when u=g. The chronological number of calls is exactly FreeMagma.length(g); the actual transcript address-length sum and maximum equal the two displayed resources. Full-list checking, including after a mismatch, attains these exact equalities.

With a physically lawful original-present prefix a, append a to every generated address and use the original-present transport and appended-readout bridge. The call count stays ell(g); the word sum increases by length(a) times ell(g), and the radius increases by length(a). These are list identities on a nonempty frontier. The original-present premise remains essential; an address born later is not a substitute.

Different ground-binding checks may submit overlapping physical addresses independently. Every occurrence then counts as an additional raw call. This one-probe-per-leaf construction preserves coefficient one in the ground-template part of a stationary whole-row upper bound; using the two-call original decoder per template leaf would not give that coefficient. Finite-cell selection, ground-binding decision, same-register operation and whole-row output are separate constructions. The equalities here assert attainment by this checker, without a minimax or lower-bound claim.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.DelayedMatches`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayedRadius`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_leaf_reflection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_certificate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_resources`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.delayed_template_service`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.expected`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafAddressSum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafBit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafDelay`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.leafReply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.rightTip`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateCheck`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateExpected`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/DelayedTemplateCertificate.templateQueries`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate](../ActualImageAddressCertificate.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualJointResponseCostCore](../ActualJointResponseCostCore.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout](DelayedOriginalReadout.md)
