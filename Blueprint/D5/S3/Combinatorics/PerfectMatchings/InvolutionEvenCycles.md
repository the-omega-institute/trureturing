# Rooted Interlacing of Two Perfect Matchings

## Abstract

Ordered perfect matchings correspond to actual even-cycle permutations by rooted interlacing.

In an arbitrary universe, let X be any finite linearly ordered type. Perm(X) denotes Equiv.Perm X. The input uses the existing D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution X: its elements are exactly permutations p satisfying p(p(x)) = x and p(x) ≠ x for all x. Connected(s,t,x,y) is the existing reflexive transitive closure of s-edges and t-edges. SameCycle uses the full integer-power orbit, including singleton product orbits. Products act from right to left; the even-position product is t*s.

componentRoot(s,t,x) is the least vertex of the actual component through x. firstPhase(s,t,x) means that x is in the full t*s orbit of this minimum. Both matching edges exchange its two product-orbit classes, by InvolutionOrbitSplit. interlace(s,t) follows s in firstPhase and t outside it; its predecessor follows t in firstPhase and s outside it. The root therefore first follows the FIRST input color s. This convention is fixed by the supplied order and is unrelated to numeric label parity.

**Theorem 1.1 (Full Component Coverage and Ordered Recovery).**

$$\forall X \in Type,\; \forall finite \in \operatorname{Fintype}\left(X\right),\; \forall order \in \operatorname{LinearOrder}\left(X\right),\; \forall s \in \operatorname{FixedPointFreeInvolution}\left(X\right),\; \forall t \in \operatorname{FixedPointFreeInvolution}\left(X\right),\; \operatorname{recover}\left(\operatorname{forward}\left(\operatorname{pair}\left(s, t\right)\right)\right) = \operatorname{pair}\left(s, t\right) \land \left(\left(\forall x \in X,\; \forall y \in X,\; \operatorname{SameCycle}\left(\operatorname{interlace}\left(s, t\right), x, y\right) \Leftrightarrow \operatorname{Connected}\left(\operatorname{val}\left(s\right), \operatorname{val}\left(t\right), x, y\right)\right) \land \left(\left(\forall x \in X,\; \operatorname{Connected}\left(\operatorname{val}\left(s\right), \operatorname{val}\left(t\right), x, \operatorname{componentRoot}\left(s, t, x\right)\right) \land \left(\forall y \in X,\; \operatorname{Connected}\left(\operatorname{val}\left(s\right), \operatorname{val}\left(t\right), x, y\right) \Rightarrow \operatorname{componentRoot}\left(s, t, x\right) \le y\right)\right) \land \left(\left(\forall m \in X,\; \left(\forall y \in X,\; \operatorname{Connected}\left(\operatorname{val}\left(s\right), \operatorname{val}\left(t\right), m, y\right) \Rightarrow m \le y\right) \Rightarrow \left(\forall k \in Nat,\; \operatorname{apply}\left(\operatorname{interlace}\left(s, t\right)^{2 \cdot k}, m\right) = \operatorname{apply}\left(\left(\operatorname{val}\left(t\right) \cdot \operatorname{val}\left(s\right)\right)^{k}, m\right) \land \operatorname{apply}\left(\operatorname{interlace}\left(s, t\right)^{2 \cdot k + 1}, m\right) = \operatorname{apply}\left(\operatorname{val}\left(s\right), \operatorname{apply}\left(\left(\operatorname{val}\left(t\right) \cdot \operatorname{val}\left(s\right)\right)^{k}, m\right)\right)\right)\right) \land \left(\forall x \in X,\; \operatorname{apply}\left(\operatorname{interlace}\left(s, t\right), x\right) = \operatorname{ite}\left(\operatorname{firstPhase}\left(s, t, x\right), \operatorname{apply}\left(\operatorname{val}\left(s\right), x\right), \operatorname{apply}\left(\operatorname{val}\left(t\right), x\right)\right) \land \left(\operatorname{apply}\left(\operatorname{inv}\left(\operatorname{interlace}\left(s, t\right)\right), x\right) = \operatorname{ite}\left(\operatorname{firstPhase}\left(s, t, x\right), \operatorname{apply}\left(\operatorname{val}\left(t\right), x\right), \operatorname{apply}\left(\operatorname{val}\left(s\right), x\right)\right) \land \left(\operatorname{cyclePhase}\left(\operatorname{interlace}\left(s, t\right), x\right) \Leftrightarrow \operatorname{firstPhase}\left(s, t, x\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles.rooted_interlacing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu (1990). *Skew-symmetric matrices and the Pfaffian*. URL: <https://sites.cs.ucsb.edu/~omer/DOWNLOADABLE/Pfaffian90.pdf>.

*Commentary.*

The actual component splits into two disjoint product orbits. Natural powers enumerate each finite full orbit. Interlacing their vertices as r^k(m), s(r^k(m)) covers the entire component, with no repeated orientation choice. The one-step action changes phase, so a returning cycle has even length. The square orbit of the resulting permutation at the same minimum is precisely the first product orbit; alternating successor and predecessor recovers both original mates. The formula quantifies every minimum m of an actual component and every natural k.

For an arbitrary output q, cycleRoot(q,x) is the least vertex of its full cycle. cyclePhase(q,x) means (q^2).SameCycle(cycleRoot(q,x),x). The output subtype requires BOTH no fixed point and even support cardinality for every member of q.cycleFactorsFinset. Fixed-point exclusion is essential: that finset omits singleton cycles. On this subtype the even cycle period prevents adjacent vertices from lying in the same square orbit. Consequently cyclePhase flips at both successor and predecessor, including across the last-to-first edge.

**Theorem 1.2 (Reconstructing the Entire Original Permutation).**

$$\forall X \in Type,\; \forall finite \in \operatorname{Fintype}\left(X\right),\; \forall order \in \operatorname{LinearOrder}\left(X\right),\; \forall q \in \operatorname{Subtype}\left((q: \operatorname{Perm}\left(X\right)) \mapsto \left(\forall x \in X,\; \operatorname{apply}\left(q, x\right) \ne x\right) \land \left(\forall c \in \operatorname{Perm}\left(X\right),\; c \in \operatorname{cycleFactorsFinset}\left(q\right) \Rightarrow \operatorname{Even}\left(\operatorname{card}\left(\operatorname{support}\left(c\right)\right)\right)\right)\right),\; \operatorname{forward}\left(\operatorname{recover}\left(q\right)\right) = q \land \left(\forall x \in X,\; \operatorname{apply}\left(\operatorname{val}\left(\operatorname{fst}\left(\operatorname{recover}\left(q\right)\right)\right), x\right) = \operatorname{ite}\left(\operatorname{cyclePhase}\left(\operatorname{val}\left(q\right), x\right), \operatorname{apply}\left(\operatorname{val}\left(q\right), x\right), \operatorname{apply}\left(\operatorname{inv}\left(\operatorname{val}\left(q\right)\right), x\right)\right) \land \operatorname{apply}\left(\operatorname{val}\left(\operatorname{snd}\left(\operatorname{recover}\left(q\right)\right)\right), x\right) = \operatorname{ite}\left(\operatorname{cyclePhase}\left(\operatorname{val}\left(q\right), x\right), \operatorname{apply}\left(\operatorname{inv}\left(\operatorname{val}\left(q\right)\right), x\right), \operatorname{apply}\left(\operatorname{val}\left(q\right), x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles.rooted_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu (1990). *Skew-symmetric matrices and the Pfaffian*. URL: <https://sites.cs.ucsb.edu/~omer/DOWNLOADABLE/Pfaffian90.pdf>.

*Commentary.*

recover(q) has first mate q(x) at even rooted distance and q inverse(x) at odd rooted distance; the second mate uses the opposite choices. Both are fixed-point-free involutions. Their actual components equal the full q-cycles, their component minima are the same cycle minima, and their first product orbit equals the original square orbit. Applying forward therefore returns q itself.

**Definition 1.3 (The Actual Equivalence).**

$$\forall X \in Type,\; \forall finite \in \operatorname{Fintype}\left(X\right),\; \forall order \in \operatorname{LinearOrder}\left(X\right),\; \operatorname{equivalence}\left(X\right): \operatorname{Equiv}\left(\operatorname{Product}\left(\operatorname{FixedPointFreeInvolution}\left(X\right), \operatorname{FixedPointFreeInvolution}\left(X\right)\right), \operatorname{Subtype}\left((q: \operatorname{Perm}\left(X\right)) \mapsto \left(\forall x \in X,\; \operatorname{apply}\left(q, x\right) \ne x\right) \land \left(\forall c \in \operatorname{Perm}\left(X\right),\; c \in \operatorname{cycleFactorsFinset}\left(q\right) \Rightarrow \operatorname{Even}\left(\operatorname{card}\left(\operatorname{support}\left(c\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles.equivalence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ömer Eğecioğlu (1990). *Skew-symmetric matrices and the Pfaffian*. URL: <https://sites.cs.ucsb.edu/~omer/DOWNLOADABLE/Pfaffian90.pdf>.

*Commentary.*

The forward function is forward(s,t), with underlying permutation interlace(s,t). The inverse function is recover. The two preceding theorems supply the exact left and right inverse laws of this Equiv. No cardinality argument or arbitrary equipotence is used. All finite X are included, without Nonempty, Inhabited or an even-cardinality input hypothesis. On the empty type the maps are the unique empty permutations. On odd cardinalities both admissible carriers are empty. A common matching pair is a genuine transposition; when s=t, interlace(s,s)=s. On two-cycles the recovered mates coincide. Longer cycles retain the ordered color distinction and disconnected components are rooted separately.

Literature: Eğecioğlu, Skew-symmetric matrices and the Pfaffian, Ars Combinatoria 29, 107–116, sections 1.2–1.3 and the bijection proof; Library/Combinatorics/egecioglu1990pfaffian.md. The paper labels the incoming edge at the minimum alpha; this construction instead explicitly follows its first input outward from the minimum. No equality of these phase conventions is asserted. This structural equivalence proves no weighted matching-sign identity, Pfaffian determinant-square formula, embedding theorem or complexity bound.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles.equivalence`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles.rooted_interlacing`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/InvolutionEvenCycles.rooted_reconstruction`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit](InvolutionOrbitSplit.md)
- Dependency: [D5/S3/Zeros/Convolution/PerfectMatchingCount](../../Zeros/Convolution/PerfectMatchingCount.md)
