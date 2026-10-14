# Original finite-window dynamics

## Abstract

Uniform guarded marker permutations on original numbered Reset histories.

The simultaneous M D_i M method is classical: Boyle–Lind–Rudolph, The automorphism group of a shift of finite type, Trans. AMS 306 (1988), 71–114, section 2 pp. 74–75, DOI 10.1090/S0002-9947-1988-0927684-2. The new formal content is the arbitrary-history guard protection and eligible-interval invariance, with every finite-word hypothesis verified on the original ResetGraph. No publication novelty is claimed.

The original history action connects to arithmetic through ResetHistoryKernel: the cyclic native chart makes the actual rho image abelian, so the alternating restrictions give nonabelian finite subgroups of unbounded orders in its kernel. This describes a subgroup family, not the complete kernel or a claim that the whole kernel is locally finite. Display aliases denote the exact typed functions described in each entry; graph edge labels, multiplicities and absolute signs remain.

**Definition 1.1 (Unbordered at every edge offset).**

$$\forall E \in Type, m \in Nat, M \in \operatorname{Function}\left(\operatorname{Fin}\left(m\right), E\right),\; \operatorname{NoPartialOverlap}\left(M\right):Prop$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.NoPartialOverlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NoPartialOverlap M means that for every natural r with 0<r<m, the equality M[r+j]=M[j] fails for at least one j in Fin(m-r). The indices retain their proved bounds. No return-time alignment or symbolic conjugacy is assumed.

**Definition 1.2 (Finite marker and injective data family).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat,\; \operatorname{GuardedWords}\left(E, I, m, d\right):Type$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Words` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Words stores marker:Fin m→E and data:I→Fin d→E, with 0<m, d<m, NoPartialOverlap marker and Function.Injective data. E and I may have independent universes. These are finite-word hypotheses, not a marker automorphism.

**Definition 1.3 (Exact integer marker occurrence).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), x \in \operatorname{Function}\left(Int, E\right), a \in Int,\; \operatorname{Occurs}\left(W, x, a\right) \Leftrightarrow \left(\forall j \in \operatorname{Fin}\left(m\right),\; \operatorname{apply}\left(x, a + \operatorname{integerIndex}\left(j\right)\right) = \operatorname{apply}\left(\operatorname{marker}\left(W\right), j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Occurs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Function(A,B) is the full function type A→B; apply is evaluation. integerIndex(j) casts the natural value of j to Int. Occurs compares every original edge.

**Definition 1.4 (A guarded data interval).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), x \in \operatorname{Function}\left(Int, E\right), a \in Int, i \in I,\; \operatorname{Selected}\left(W, x, a, i\right) \Leftrightarrow \left(\operatorname{Occurs}\left(W, x, a\right) \land \left(\operatorname{Occurs}\left(W, x, a + m + d\right) \land \left(\forall j \in \operatorname{Fin}\left(d\right),\; \operatorname{apply}\left(x, a + m + \operatorname{integerIndex}\left(j\right)\right) = \operatorname{apply}\left(\operatorname{apply}\left(\operatorname{data}\left(W\right), i\right), j\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Selected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Selected W x a i is exactly M D_i M starting at a. Natural lengths are cast to Int in coordinate sums. Only the half-open central interval is replaceable.

**Definition 1.5 (Simultaneous central-data replacement).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), pi \in \operatorname{Perm}\left(I\right), x \in \operatorname{Function}\left(Int, E\right), t \in Int,\; \operatorname{apply}\left(\operatorname{replace}\left(W, pi, x\right), t\right):E$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a coordinate in a selected gap, replace outputs data(pi(i)) at the same offset. Otherwise it returns x(t). Marker separation proves unique start, injective data proves unique label, and coordinate equality proves unique offset. The noncomputable selection changes no mathematical choice of output.

**Theorem 1.6 (Every marker occurrence is invariant).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), pi \in \operatorname{Perm}\left(I\right), x \in \operatorname{Function}\left(Int, E\right), a \in Int,\; \operatorname{Occurs}\left(W, \operatorname{replace}\left(W, pi, x\right), a\right) \Leftrightarrow \operatorname{Occurs}\left(W, x, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.marker_occurrences_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct unbordered markers are at least m apart. A marker of length m>d meeting a selected gap must overlap one of its protected guards. This proves both preservation and exclusion of new markers on arbitrary bilateral sequences. It is used by eligibility invariance, inverse and composition.

**Theorem 1.7 (Eligibility and data labels are preserved).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), pi \in \operatorname{Perm}\left(I\right), x \in \operatorname{Function}\left(Int, E\right), a \in Int, i \in I,\; \operatorname{Selected}\left(W, \operatorname{replace}\left(W, pi, x\right), a, \operatorname{apply}\left(pi, i\right)\right) \Leftrightarrow \operatorname{Selected}\left(W, x, a, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.selected_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exactly the same selected intervals survive. The data label becomes pi(i). A previously unselected interval cannot become eligible because any hit there would already have the same selected start. This supports the real group law.

**Theorem 1.8 (Ordinary permutation composition).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), pi \in \operatorname{Perm}\left(I\right), tau \in \operatorname{Perm}\left(I\right), x \in \operatorname{Function}\left(Int, E\right),\; \operatorname{replace}\left(W, pi, \operatorname{replace}\left(W, tau, x\right)\right) = \operatorname{replace}\left(W, pi \cdot tau, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The convention is (pi*tau)(i)=pi(tau(i)). All successive replacements use the same intervals, including adjacent templates sharing one guard.

**Theorem 1.9 (Both inverse laws).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), pi \in \operatorname{Perm}\left(I\right), x \in \operatorname{Function}\left(Int, E\right),\; \operatorname{replace}\left(W, pi^{-1}, \operatorname{replace}\left(W, pi, x\right)\right) = x \land \operatorname{replace}\left(W, pi, \operatorname{replace}\left(W, pi^{-1}, x\right)\right) = x$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both inverse equations consume eligibility invariance and composition; no inverse automorphism is supplied as an assumption.

**Theorem 1.10 (A uniform finite original-edge window).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), pi \in \operatorname{Perm}\left(I\right), x \in \operatorname{Function}\left(Int, E\right), y \in \operatorname{Function}\left(Int, E\right), t \in Int,\; \left(\forall s \in Int,\; \left(t - \left(m + d\right) \le s \land s \le t + m + d\right) \Rightarrow \operatorname{apply}\left(x, s\right) = \operatorname{apply}\left(y, s\right)\right) \Rightarrow \operatorname{apply}\left(\operatorname{replace}\left(W, pi, x\right), t\right) = \operatorname{apply}\left(\operatorname{replace}\left(W, pi, y\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Radius m+d suffices. Every template relevant at t lies in the displayed closed interval. Transporting its finite tests proves local dependence, which factors replacement through a finite discrete window for continuity.

**Theorem 1.11 (Commutation with integer translation).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), pi \in \operatorname{Perm}\left(I\right), x \in \operatorname{Function}\left(Int, E\right), c \in Int, t \in Int,\; \operatorname{apply}\left(\operatorname{replace}\left(W, pi, \operatorname{translateSequence}\left(c, x\right)\right), t\right) = \operatorname{apply}\left(\operatorname{replace}\left(W, pi, x\right), t + c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

translateSequence(c,x)(s)=x(s+c). Translation carries selected starts by the same integer displacement; c=1 is the actual unit left shift.

**Definition 1.12 (Legal common-endpoint finite loops).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right),\; \forall V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), p \in V,\; \operatorname{Loops}\left(W, G, p\right):Prop$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Loops` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Loops requires 0<d, all interior target/source seams of marker and data, and source(first)=target(last)=p for marker and every data word. It stores only these finite graph facts. The Reset specialization proves every field.

**Definition 1.13 (Replacement of actual legal histories).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), p \in V, L \in \operatorname{Loops}\left(W, G, p\right), pi \in \operatorname{Perm}\left(I\right), x \in \operatorname{History}\left(G\right),\; \operatorname{onHistory}\left(W, G, L, pi, x\right):\operatorname{History}\left(G\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.onHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

History G is the original legal subtype of Int→E. Internal replacements use data legality; the final data edge meets the untouched right guard at p; the first data edge meets the old left seam at p. All other seams are unchanged.

**Definition 1.14 (The genuine history homeomorphism).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), p \in V, L \in \operatorname{Loops}\left(W, G, p\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), pi \in \operatorname{Perm}\left(I\right),\; \operatorname{homeomorph}\left(W, G, L, pi\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(G\right), \operatorname{History}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.homeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The edge topology is discrete. Both directions are onHistory with pi and pi inverse; finite-window dependence proves continuity in the original product/subtype topology, and replace_inverse proves both inverse laws.

**Definition 1.15 (A hom into the full UNIT-shift centralizer).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), p \in V, L \in \operatorname{Loops}\left(W, G, p\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), finV \in \operatorname{Fintype}\left(V\right), finE \in \operatorname{Fintype}\left(E\right), eqV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right),\; \operatorname{action}\left(W, G, L\right):\operatorname{MonoidHom}\left(\operatorname{Perm}\left(I\right), \operatorname{FullAut}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.action` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FullAut is StandardBeamHomeomorphisms.fullAutSubgroup: every actual history homeomorphism commuting with UNIT shift. The displayed finite/discrete instances are the exact domain requirements. The hom uses ordinary composition.

**Theorem 1.16 (Faithfulness on actual histories).**

$$\forall E \in Type, I \in Type, m \in Nat, d \in Nat, W \in \operatorname{GuardedWords}\left(E, I, m, d\right), V \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), p \in V, L \in \operatorname{Loops}\left(W, G, p\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), finV \in \operatorname{Fintype}\left(V\right), finE \in \operatorname{Fintype}\left(E\right), eqV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \operatorname{FunctionInjective}\left(\operatorname{action}\left(W, G, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.action_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each i, the positive legal word M D_i M extends to an actual history by exists_history_containing. Its central gap remains selected independently of the exterior extension. Equality of actions forces equality of encoded data, then equality of permutation values by the injective data family.

**Definition 1.17 (The exact numbered Reset marker).**

$$\forall q \in Nat, k \in Nat, hq \in 1 < q,\; \operatorname{resetMarker}\left(hq\right):\operatorname{Function}\left(\operatorname{Fin}\left(6 \cdot k + 5\right), \operatorname{Product}\left(\operatorname{Edge}\left(\operatorname{resetMatrix}\left(q\right)\right), MultiplicativeBool\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetMarker` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Marker edges are transported by originalEdge from B^(2k+1)A. A=ab and B=acd: a is reset 0→0 at absolute sign 1, b is reset 0→0 at sign zeta, c is advance 0→1 at sign zeta, d is reset 1→0 at sign zeta. Reset edges have flip label, advance has identity label, and all edge numbers are the proved unique zero. zeta=Multiplicative.ofAdd true, p=(0,1).

**Definition 1.18 (The Boolean indexed six-edge data words).**

$$\forall q \in Nat, k \in Nat, hq \in 1 < q, b \in \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right),\; \operatorname{resetData}\left(hq, b\right):\operatorname{Function}\left(\operatorname{Fin}\left(6 \cdot k\right), \operatorname{Product}\left(\operatorname{Edge}\left(\operatorname{resetMatrix}\left(q\right)\right), MultiplicativeBool\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each Boolean true chooses A^3, each false chooses B^2. All k chunks have length six and endpoints p. Their second edges differ, giving injectivity by equal-length chunk splitting, without a free-shift conjugacy.

**Definition 1.19 (Discharged original finite-word hypotheses).**

$$\forall q \in Nat, k \in Nat, hq \in 1 < q,\; \operatorname{resetWords}\left(hq\right):\operatorname{GuardedWords}\left(\operatorname{Product}\left(\operatorname{Edge}\left(\operatorname{resetMatrix}\left(q\right)\right), MultiplicativeBool\right), \operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right), 6 \cdot k + 5, 6 \cdot k\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The expanded edge b appears only at the marker's final position. Every proper prefix excludes it while every suffix ends in it, proving edge unborderedness at all offsets. Data length 6k is less than marker length 6k+5, independently of the data contents.

**Definition 1.20 (Discharged legality and endpoint hypotheses).**

$$\forall q \in Nat, k \in Nat, hq \in 1 < q, hk \in 0 < k,\; \operatorname{Loops}\left(\operatorname{resetWords}\left(hq\right), \operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{origin}\left(q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetLoops` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Existing actual_source and actual_target transport the original ListPath proofs for A, B, repeats and concatenated chunks. Every loop returns to the same original vertex p; q need not be even. origin(q) denotes (0,1).

**Definition 1.21 (The original Reset history permutation action).**

$$\forall q \in Nat, k \in Nat, hq \in 1 < q, hk \in 0 < k,\; \operatorname{resetAction}\left(hq, hk\right):\operatorname{MonoidHom}\left(\operatorname{Perm}\left(\operatorname{Function}\left(\operatorname{Fin}\left(k\right), Bool\right)\right), \operatorname{FullAut}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This instantiates the checked guarded action on actual expanded Reset edges. Extra q>2 edges and arbitrary noncoded tails remain in its domain. Its symmetric original-edge window has radius m+d=12k+5.

**Theorem 1.22 (The original Reset action is faithful).**

$$\forall q \in Nat, k \in Nat, hq \in 1 < q, hk \in 0 < k,\; \operatorname{FunctionInjective}\left(\operatorname{resetAction}\left(hq, hk\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetAction_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

reset_expanded_essential supplies essentiality for every positive q, and the general action_injective theorem uses the exact original finite-word realization. This is consumed by the original representation-kernel embedding.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Loops`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.NoPartialOverlap`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Occurs`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Selected`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.Words`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.action`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.action_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.homeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.marker_occurrences_invariant`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.onHistory`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_inverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_local`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_mul`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.replace_translate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetAction`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetAction_injective`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetData`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetLoops`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetMarker`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.resetWords`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/MarkerPermutationAction.selected_iff`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories](ResetAlternatingHistories.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares](ResetAlternatingSquares.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms](StandardBeamHomeomorphisms.md)
