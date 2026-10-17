# Compact stable ranges

## Abstract

A continuous compact Hausdorff endomorphism restricts to a continuous surjection of its actual compact stable range.

For any self-map f, core(f) is the literal intersection of range(f^n) over every natural n, including zero. It is forward invariant without topology: an n-step preimage of c gives an (n+1)-step preimage of f(c). restriction(f) sends the actual subtype point c to f(c), with invariance proving subtype membership.

**Theorem 1.1 (The compact onto core system).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), [\operatorname{TopologicalSpace}\left(X\right)] [\operatorname{CompactSpace}\left(X\right)] [\operatorname{T2Space}\left(X\right)] \\\forall f: X \to X, \operatorname{Continuous}\left(f\right) \Rightarrow\\\operatorname{IsCompact}\left(\operatorname{core}\left(f\right)\right) \land \operatorname{Continuous}\left(\operatorname{restriction}\left(f\right)\right) \land \operatorname{Surjective}\left(\operatorname{restriction}\left(f\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/StableRange.compact_surjective_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bernhard Banaschewski (1955). *Über nulldimensionale Räume*. DOI: [10.1002/mana.19550130302](https://doi.org/10.1002/mana.19550130302). URL: <https://doi.org/10.1002/mana.19550130302>.

*Commentary.*

Every iterate is continuous. Its range is compact and therefore closed in Hausdorff X. Their intersection is closed; compactness of X gives compactness of this same core.

Fix c in the core. For each natural n form F(n)=range(f^n) intersected with f inverse-image of {c}. These are closed and decreasing. Membership of c in range(f^(n+1)) gives a point f^n(a) in F(n). The compact nested-intersection theorem supplies one a in every F(n). It lies in the actual core and satisfies f(a)=c. This proves surjectivity of the actual restriction, without constructing a coherent backward orbit.

Continuity is inherited from f by the subtype topology. The proof permits empty X and empty core, arbitrary compact Hausdorff topology, and nononto or noninvertible f. No positive-time, metric, countability or chosen-selector hypothesis occurs. This supplies a core system for later dynamics; it asserts no period or shadowing.

## References

- Truth anchor: `D5/S1/Dynamics/StableRange.compact_surjective_restriction`
