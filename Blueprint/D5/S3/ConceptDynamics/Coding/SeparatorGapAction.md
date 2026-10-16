# Separator gaps

## Abstract

Length-separated separator actions on bilateral legal histories.

**Definition 1.1 (One separator and a family of data lengths).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right),\; \operatorname{Family}\left(E, I, d\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.Family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Family stores a separator b, positive injectively indexed lengths d(n), and injective codes I(n)→Fin(d(n))→E avoiding b at every offset. E and I may have independent universes. No invariant-selection or action law is a premise.

**Definition 1.2 (A complete separator-bounded code word).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, x \in \operatorname{Function}\left(Int, E\right), s \in Int, i \in \operatorname{apply}\left(I, n\right),\; \operatorname{Selected}\left(F, n, x, s, i\right) \Leftrightarrow \left(\operatorname{apply}\left(x, s\right) = \operatorname{separator}\left(F\right) \land \left(\operatorname{apply}\left(x, s + \operatorname{apply}\left(d, n\right) + 1\right) = \operatorname{separator}\left(F\right) \land \left(\forall j \in \operatorname{Fin}\left(\operatorname{apply}\left(d, n\right)\right),\; \operatorname{apply}\left(x, s + 1 + \operatorname{integerIndex}\left(j\right)\right) = \operatorname{data}\left(F, n, i, j\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.Selected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All natural coordinates in integer sums are cast to Int. Separator avoidance makes the two endpoints consecutive separator positions. The sequence may contain arbitrary noncoded gaps, extra edge symbols, and infinite separator-free tails.

**Definition 1.3 (Simultaneous replacement of all eligible gaps of one length).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{Function}\left(Int, E\right), t \in Int,\; \operatorname{apply}\left(\operatorname{replace}\left(F, n, sigma, x\right), t\right):E$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An interior hit outputs data(n,sigma(i),j), and every other coordinate returns x(t). Two overlapping interiors between consecutive separators must have identical endpoints. Length injectivity, code injectivity and the offset equation give uniqueness, so the chosen hit does not change the output.

**Theorem 1.4 (Exact preservation of the entire separator set).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{Function}\left(Int, E\right), t \in Int,\; \operatorname{apply}\left(\operatorname{replace}\left(F, n, sigma, x\right), t\right) = \operatorname{separator}\left(F\right) \Leftrightarrow \operatorname{apply}\left(x, t\right) = \operatorname{separator}\left(F\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.separator_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a hit, both the old and new data avoid b. Off hits the coordinate is fixed. Thus neither a new separator nor a missing separator can alter the parsing.

**Theorem 1.5 (Eligibility is invariant in both directions).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{Function}\left(Int, E\right), s \in Int, i \in \operatorname{apply}\left(I, n\right),\; \operatorname{Selected}\left(F, n, \operatorname{replace}\left(F, n, sigma, x\right), s, \operatorname{apply}\left(sigma, i\right)\right) \Leftrightarrow \operatorname{Selected}\left(F, n, x, s, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.selected_same` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An old selected interval is relabeled by sigma. Conversely, new selection gives an old interval between the same consecutive separators. Any old hit meeting its interior has those endpoints; if none exists, the entire data word was unchanged and was already eligible. This does not assume an inverse law.

**Theorem 1.6 (Other lengths preserve every data edge).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, m \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{Function}\left(Int, E\right), s \in Int, i \in \operatorname{apply}\left(I, m\right), j \in \operatorname{Fin}\left(\operatorname{apply}\left(d, m\right)\right),\; n \ne m \Rightarrow \left(\operatorname{Selected}\left(F, m, x, s, i\right) \Rightarrow \operatorname{apply}\left(\operatorname{replace}\left(F, n, sigma, x\right), s + 1 + \operatorname{integerIndex}\left(j\right)\right) = \operatorname{apply}\left(x, s + 1 + \operatorname{integerIndex}\left(j\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_on_other_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Different indexed lengths cannot have the same endpoints. Their selected interiors are disjoint even when they share a separator.

**Theorem 1.7 (Different lengths neither create nor remove a selection).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, m \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{Function}\left(Int, E\right), s \in Int, i \in \operatorname{apply}\left(I, m\right),\; n \ne m \Rightarrow \left(\operatorname{Selected}\left(F, m, \operatorname{replace}\left(F, n, sigma, x\right), s, i\right) \Leftrightarrow \operatorname{Selected}\left(F, m, x, s, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.selected_other` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions follow from exact separator preservation and interval rigidity. The converse covers gaps that were initially not code words.

**Theorem 1.8 (The actual noncommutative composition order).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), tau \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{Function}\left(Int, E\right),\; \operatorname{replace}\left(F, n, sigma, \operatorname{replace}\left(F, n, tau, x\right)\right) = \operatorname{replace}\left(F, n, sigma \cdot tau, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a selected interval the label becomes sigma(tau(i)); off every interval both maps fix the coordinate. Unit and both inverse laws follow.

**Theorem 1.9 (Commutation derived from spatial separation).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, m \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), tau \in \operatorname{Perm}\left(\operatorname{apply}\left(I, m\right)\right), x \in \operatorname{Function}\left(Int, E\right),\; n \ne m \Rightarrow \operatorname{replace}\left(F, n, sigma, \operatorname{replace}\left(F, m, tau, x\right)\right) = \operatorname{replace}\left(F, m, tau, \operatorname{replace}\left(F, n, sigma, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two rules preserve each other's selections and central data. This proves commutation on every sequence, although both rules can move the same whole history.

**Theorem 1.10 (A finite original-coordinate window).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), n \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{Function}\left(Int, E\right), y \in \operatorname{Function}\left(Int, E\right), t \in Int,\; \left(\forall s \in Int,\; t - \left(\operatorname{apply}\left(d, n\right) + 1\right) \le s \Rightarrow \left(s \le t + \operatorname{apply}\left(d, n\right) + 1 \Rightarrow \operatorname{apply}\left(x, s\right) = \operatorname{apply}\left(y, s\right)\right)\right) \Rightarrow \operatorname{apply}\left(\operatorname{replace}\left(F, n, sigma, x\right), t\right) = \operatorname{apply}\left(\operatorname{replace}\left(F, n, sigma, y\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Radius d(n)+1 contains both endpoints and all data of every hit at t. Locality and integer-translation equivariance give continuity using the existing historyWindow_continuous theorem for the finite discrete word space.

**Definition 1.11 (Legal paths with distinct endpoint roles).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right),\; \forall V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right),\; \operatorname{Paths}\left(F, G\right):Prop$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.Paths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each data word is legal, starts at target(b), and ends at source(b). The separator need not be a loop. These are finite-edge conditions.

**Definition 1.12 (Replacement on all legal histories).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), P \in \operatorname{Paths}\left(F, G\right), n \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), x \in \operatorname{History}\left(G\right),\; \operatorname{onHistory}\left(F, G, P, n, sigma, x\right):\operatorname{History}\left(G\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.onHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Interior seams use data legality. The first and last data edges meet the unchanged separators through their actual target and source. All remaining seams retain the original legal-history equation.

**Definition 1.13 (A homeomorphism with its actual inverse).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), P \in \operatorname{Paths}\left(F, G\right), n \in Nat, sigma \in \operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right),\; [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{DiscreteTopology}\left(E\right)] \operatorname{homeomorph}\left(F, G, P, n, sigma\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(G\right), \operatorname{History}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.homeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse uses sigma inverse on exactly the same intervals. Both maps are continuous on the original legal subspace; no encoded-history restriction appears.

**Definition 1.14 (A coordinate in the full unit-shift centralizer).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), P \in \operatorname{Paths}\left(F, G\right), n \in Nat,\; [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{DiscreteTopology}\left(E\right)] \operatorname{action}\left(F, G, P, n\right):\operatorname{MonoidHom}\left(\operatorname{Perm}\left(\operatorname{apply}\left(I, n\right)\right), \operatorname{FullAut}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translation of a selected word translates its start. Thus the homeomorphism commutes with the actual unit shift, and its group law has ordinary composition order.

**Definition 1.15 (The noncommutative restricted product at identity).**

$$\forall J \in \operatorname{Function}\left(Nat, Type\right),\; \operatorname{FinitePerm}\left(J\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.FinitePerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FinitePerm J is Mathlib RestrictedProduct of Perm(J(n)), with bottom subgroups and the cofinite filter. Its elements have finitely many nonidentity coordinates. Multiplication is coordinatewise and the individual factors may be nonabelian.

**Definition 1.16 (All finitely many active coordinates act together).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), P \in \operatorname{Paths}\left(F, G\right),\; [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{DiscreteTopology}\left(E\right)] \operatorname{finiteAction}\left(F, G, P\right):\operatorname{MonoidHom}\left(\operatorname{FinitePerm}\left(I\right), \operatorname{FullAut}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite noncommProd assembles the coordinate homomorphisms. Cross-length commutation proves independence of ordering and identity padding. Enlarging two supports to their union proves the homomorphism law without commuting the two factors inside a single coordinate. Every tuple has a finite window as a finite composition. No unrestricted infinite-product continuity is claimed.

**Theorem 1.17 (Subgroup closure of the simultaneous action).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), P \in \operatorname{Paths}\left(F, G\right), H \in \operatorname{Subgroup}\left(\operatorname{FullAut}\left(G\right)\right), g \in \operatorname{FinitePerm}\left(I\right),\; [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{DiscreteTopology}\left(E\right)] \left(\forall n \in Nat,\; \operatorname{member}\left(\operatorname{action}\left(F, G, P, n, \operatorname{apply}\left(g, n\right)\right), H\right)\right) \Rightarrow \operatorname{member}\left(\operatorname{apply}\left(\operatorname{finiteAction}\left(F, G, P\right), g\right), H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite fold stays in any subgroup containing all coordinate images. This is used to place the alternating product in the original representation kernel.

**Theorem 1.18 (Joint coordinate observation on arbitrary tails).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), P \in \operatorname{Paths}\left(F, G\right), g \in \operatorname{FinitePerm}\left(I\right), x \in \operatorname{History}\left(G\right), n \in Nat, s \in Int, i \in \operatorname{apply}\left(I, n\right), j \in \operatorname{Fin}\left(\operatorname{apply}\left(d, n\right)\right),\; [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{DiscreteTopology}\left(E\right)] \operatorname{Selected}\left(F, n, \operatorname{historyEdges}\left(x\right), s, i\right) \Rightarrow \operatorname{apply}\left(\operatorname{historyEdges}\left(\operatorname{apply}\left(\operatorname{apply}\left(\operatorname{finiteAction}\left(F, G, P\right), g\right), x\right)\right), s + 1 + \operatorname{integerIndex}\left(j\right)\right) = \operatorname{data}\left(F, n, \operatorname{apply}\left(\operatorname{apply}\left(g, n\right), i\right), j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction_at_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a selected n-gap the complete finite-support action outputs D(n,g(n)(i)) at every offset. Every other length leaves this observation fixed regardless of how its action changes the exterior history.

**Theorem 1.19 (Joint faithfulness of the countable finite-support action).**

$$\forall E \in Type, I \in \operatorname{Function}\left(Nat, Type\right), d \in \operatorname{Function}\left(Nat, Nat\right), F \in \operatorname{Family}\left(E, I, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), P \in \operatorname{Paths}\left(F, G\right),\; [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{DiscreteTopology}\left(E\right)] [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(V\right)] \operatorname{Essential}\left(G\right) \Rightarrow \operatorname{FunctionInjective}\left(\operatorname{finiteAction}\left(F, G, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The legal word b D(n,i) b has positive length and is realized by an actual bilateral history using EssentialWordRealization.exists_history_containing. Comparing two actions on these witnesses determines every data word, hence every permutation coordinate. The action itself remains defined on all histories.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.Family`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.FinitePerm`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.Paths`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.Selected`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.action`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction_at_selected`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.finiteAction_mem`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.homeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.onHistory`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_commute`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_local`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_mul`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.replace_on_other_gap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.selected_other`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.selected_same`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/SeparatorGapAction.separator_iff`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms](StandardBeamHomeomorphisms.md)
