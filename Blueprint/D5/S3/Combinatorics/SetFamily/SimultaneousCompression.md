# Simultaneous Weighted Compression

## Abstract

Simultaneous coordinate deletion for cross-intersecting families with two independent exact-trace measures.

**Definition 1.1 (Cross-intersection).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.CrossIntersecting`

*Formalization.* `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.CrossIntersecting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two finite families A and B are cross-intersecting if every X in A has a common element with every Y in B. Each side may contain mutually disjoint sets; the condition compares only opposite sides.

**Definition 1.2 (A local coordinate replacement).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.shift`

*Formalization.* `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.shift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The shifted trace replaces t by s: shift(s,t,X) is the union of {s} with X minus {t}. The operation is defined for every finite trace.

**Definition 1.3 (One trace becomes one or two traces).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.compressedFamily`

*Formalization.* `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.compressedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Imre Leader, Ta Sheng Tan (2026). *Some results on intersecting families of triangulations*. URL: <https://arxiv.org/abs/2610.39116v1>.

*Commentary.*

Let Omega be the finite feasible trace family. Among members X of A containing t, move exactly those whose shifted trace is absent from A. Retain all other members, insert each moved trace's shifted trace, and also insert its extension by u when that extension belongs to Omega. Finite-set unions count each resulting trace once.

**Definition 1.4 (Exact-trace mass).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.mass`

*Formalization.* `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real weight w on finite traces, mass(w,A) is the sum of w(X) over the members X of A. Distinct completions may contribute to a single trace's weight.

**Definition 1.5 (The full projection fibre).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.marginalWeight`

*Formalization.* `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.marginalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reduced weight of R is the sum of w(X) over every feasible X whose deletion of t equals R. This includes all feasible original traces, whether or not they belonged to the selected family. It neither chooses one completion nor discards multiplicities.

**Theorem 1.6 (A common deletion does not decrease either mass).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.exists_simultaneous_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.exists_simultaneous_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Imre Leader, Ta Sheng Tan (2026). *Some results on intersecting families of triangulations*. URL: <https://arxiv.org/abs/2610.39116v1>.

*Commentary.*

Let alpha be any type with decidable equality, Omega a finite family of feasible finite subsets, and A and B subfamilies of Omega. Choose s,t,u with s distinct from both t and u. Every feasible trace containing t must omit s and u, and replacing t by s must remain feasible. Suppose A and B are cross-intersecting. Let w and v be two arbitrary real weights, each nonnegative on Omega. For every feasible X containing t, require separately for w and v that the weight of X equals the weight of its shift plus the weight of the shifted trace extended by u if that extension is feasible, and equals the shifted weight alone otherwise. No equality between w and v is assumed.

Then there are families C and D in the image of Omega under deletion of t. They remain cross-intersecting after this common deletion, mass(w,A) is at most mass(marginalWeight(Omega,w,t),C), and mass(v,B) is at most mass(marginalWeight(Omega,v,t),D). Each nonempty input side has a nonempty output side, even when all its weights vanish. Empty input families and zero weights are allowed.

To prove this, first extend the pair to mutually maximal cross-intersecting families inside Omega, using the polar operation twice. In a maximal family, a moved trace's extension target was also absent: otherwise a disjoint opposite trace supplied by maximality would have to contain t and u simultaneously. Each of the two target maps is injective on moved traces, and their images are disjoint because exactly the extension targets contain u. They are also disjoint from retained members. The local equation therefore preserves each maximal family's mass without counting a target twice.

For cross-intersection after deletion, if both outputs contain s they meet there. Otherwise an output lacking s is retained. A retained trace containing t has its shift already in its original family. Comparing this shifted trace with the opposite original trace rules out an intersection only at t, including when the other output came from a moved trace. Finally, full projection fibres can only increase mass by nonnegativity. The argument uses each side's own weight equation.

Leader and Tan use the one-to-two ear replacement in the proof of Theorem 2 and simultaneous compression for cross-intersecting triangulation families in Lemma 8. Here the two nonnegative weights have their own explicitly assumed local equations.

Iteration requires the feasibility, local equations and full projection law on every reduced support. Applying this result to polygon triangulations additionally requires actual conditional completion weights and a condition-preserving ear-slide construction. The present statement assumes the local weight equations; it does not establish those geometric facts or an original-family deficit bound.

**Definition 1.7 (Relative upper closure).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.RelativelyUpper`

*Formalization.* `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.RelativelyUpper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A family is relatively upper inside Omega when every feasible superset of any of its members is also a member. No upward closure of Omega itself is required.

**Definition 1.8 (Coherent data on every reduced support).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.DeletionSystem`

*Formalization.* `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.DeletionSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix a finite coordinate support J. For every sub-support H, specify a finite feasible trace family, two real weights and a terminal predicate. Both weights are nonnegative on feasible traces. Deleting any t in H maps the feasible family exactly onto the family at H minus t, and the full projection-fibre sums of each weight equal that side's weights there. At every nonterminal H there must be s,t,u with t in H and s distinct from both t and u, satisfying the local exclusion, feasible-shift and two separate one-to-two weight equations. These conditions specify feasible traces and weights; they do not assume that selected families remain cross-intersecting after deletion.

**Theorem 1.9 (A common terminal support for both measures).**

Lean statement: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.exists_terminal_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.exists_terminal_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Imre Leader, Ta Sheng Tan (2026). *Some results on intersecting families of triangulations*. URL: <https://arxiv.org/abs/2610.39116v1>.

*Commentary.*

For any deletion system on J and cross-intersecting subfamilies A and B of its feasible traces at J, there are a sub-support K of J and feasible families C,D at K. The support K is terminal, C and D are cross-intersecting and each is relatively upper. The left mass of C is at least the original left mass of A, and the right mass of D is at least the original right mass of B. Each nonempty input side has a nonempty output side, including when its weights vanish.

Strong induction on the finite support applies the local simultaneous compression at a nonterminal support. Deleting its chosen t strictly reduces the support. The exact projection and marginal equations identify both reduced mass bounds with the next system's weights, so the induction preserves them separately. At a terminal support, two polar extensions give a mutually maximal cross-intersecting pair; any feasible superset of a member also meets the opposite family and therefore belongs to that pair.

The terminal predicate is arbitrary. A polygon application must establish all the system conditions for its actual conditional completion counts and prove that terminal supports have the desired independent-coordinate meaning. This theorem does not establish those geometric and counting conditions or a same-original-family deficit.

## References

- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.CrossIntersecting`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.DeletionSystem`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.RelativelyUpper`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.compressedFamily`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.exists_simultaneous_compression`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.exists_terminal_compression`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.marginalWeight`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.mass`
- Truth anchor: `D5/S3/Combinatorics/SetFamily/SimultaneousCompression.shift`
