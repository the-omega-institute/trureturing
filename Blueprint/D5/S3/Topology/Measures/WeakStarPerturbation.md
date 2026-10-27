# Uniform weak-star perturbations

## Abstract

Weak-star closed norm balls transfer dense uniform estimates to the entire compactification.

**Theorem 1.1 (The estimate at every point).**

$$\forall X: Type, [\operatorname{NormedAddCommGroup}\left(X\right)] [\operatorname{NormedSpace}\left(Real, X\right)] \forall A: Type, \forall T: Type, [\operatorname{TopologicalSpace}\left(T\right)] \forall i: A \to T, \forall f: T \to \operatorname{WeakDual}\left(Real, X\right), \forall g: T \to \operatorname{WeakDual}\left(Real, X\right), \forall epsilon: Real, {\operatorname{DenseRange}\left(i\right) \land \operatorname{Continuous}\left(f\right) \land \operatorname{Continuous}\left(g\right) \land \forall a: A, \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{f}\left(\operatorname{i}\left(a\right)\right) - \operatorname{g}\left(\operatorname{i}\left(a\right)\right)\right)\right) \le epsilon} \Rightarrow {\forall p: T, \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{f}\left(p\right) - \operatorname{g}\left(p\right)\right)\right) \le epsilon}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/WeakStarPerturbation.norm_sub_le_of_denseRange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X is any real normed space; A is any index type and T any topological space. The image of i is dense. For weak-star continuous f and g, the strong-dual norm of f minus g is at most epsilon everywhere if it is at most epsilon at every i(a). The inverse image of the weak-star closed epsilon ball under f minus g is closed and contains the dense range. No continuity of the norm is asserted.

**Theorem 1.2 (Injection survives when twice the error is below the gap).**

$$\forall X: Type, [\operatorname{NormedAddCommGroup}\left(X\right)] [\operatorname{NormedSpace}\left(Real, X\right)] \forall A: Type, \forall T: Type, [\operatorname{TopologicalSpace}\left(T\right)] \forall i: A \to T, \forall f: T \to \operatorname{WeakDual}\left(Real, X\right), \forall g: T \to \operatorname{WeakDual}\left(Real, X\right), \forall c: Real, \forall epsilon: Real, {\operatorname{DenseRange}\left(i\right) \land \operatorname{Continuous}\left(f\right) \land \operatorname{Continuous}\left(g\right) \land \forall p: T, \forall q: T, {p \neq q} \Rightarrow {c \le \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{f}\left(p\right) - \operatorname{f}\left(q\right)\right)\right)} \land 2 \cdot epsilon < c \land \forall a: A, \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{f}\left(\operatorname{i}\left(a\right)\right) - \operatorname{g}\left(\operatorname{i}\left(a\right)\right)\right)\right) \le epsilon} \Rightarrow {\operatorname{Injective}\left(g\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/WeakStarPerturbation.injective_of_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume every unequal pair of f-values has strong-dual norm distance at least c, and twice epsilon is less than c. The dense estimate transfers to every p and q. If g(p)=g(q), the triangle inequality gives norm(f(p)-f(q)) at most twice epsilon, contradicting the gap. The signed-ball application obtains c directly from WeakStarNormSeparation.exists_pos_le_norm_sub on the full Stone–Čech domain.

**Theorem 1.3 (The bounded extension exists).**

$$\forall X: Type, [\operatorname{NormedAddCommGroup}\left(X\right)] [\operatorname{NormedSpace}\left(Real, X\right)] \forall a: Nat \to \operatorname{StrongDual}\left(Real, X\right), \forall R: Real, {\forall n: Nat, \operatorname{norm}\left(\operatorname{a}\left(n\right)\right) \le R} \Rightarrow {\exists f: \operatorname{Ultrafilter}\left(Nat\right) \to \operatorname{WeakDual}\left(Real, X\right), \operatorname{Continuous}\left(f\right) \land \forall n: Nat, \operatorname{f}\left(\operatorname{pure}\left(n\right)\right) = \operatorname{toWeakDual}\left(\operatorname{a}\left(n\right)\right) \land \forall p: \operatorname{Ultrafilter}\left(Nat\right), \operatorname{norm}\left(\operatorname{toStrongDual}\left(\operatorname{f}\left(p\right)\right)\right) \le R}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/WeakStarPerturbation.exists_bounded_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Banach–Alaoglu makes the full radius R dual ball compact in the weak-star topology. Extend the sequence into that actual compact subtype and then forget the subtype. The extension agrees at every principal ultrafilter and remains in the same ball at every free ultrafilter.

**Theorem 1.4 (Normalize by the actual norms).**

$$\forall E: Type, [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(Real, E\right)] \forall a: Nat \to E, \forall B: Real, \forall r: Real, {\forall n: Nat, \operatorname{norm}\left(\operatorname{a}\left(n\right)\right) \le B \land 0 < r \land \operatorname{Tendsto}\left(n \mapsto \operatorname{norm}\left(\operatorname{a}\left(n\right)\right), atTop, \operatorname{nhds}\left(r\right)\right)} \Rightarrow {\operatorname{Tendsto}\left(n \mapsto \operatorname{smul}\left(\operatorname{inv}\left(\operatorname{norm}\left(\operatorname{a}\left(n\right)\right)\right), \operatorname{a}\left(n\right)\right) - \operatorname{smul}\left(\operatorname{inv}\left(r\right), \operatorname{a}\left(n\right)\right), atTop, \operatorname{nhds}\left(0\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/WeakStarPerturbation.normalize_sub_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a bounded sequence a(n) in an arbitrary real normed space with norms tending to r greater than zero, the displayed difference is norm(a(n)) inverse times a(n), minus r inverse times a(n). It tends to zero in norm. The scalar coefficient norm(a(n)) inverse minus r inverse tends to zero; multiplying its norm by the fixed bound B gives a vanishing upper bound. No equality of the raw norms is assumed.

## References

- Truth anchor: `D5/S3/Topology/Measures/WeakStarPerturbation.exists_bounded_extension`
- Truth anchor: `D5/S3/Topology/Measures/WeakStarPerturbation.injective_of_approximation`
- Truth anchor: `D5/S3/Topology/Measures/WeakStarPerturbation.norm_sub_le_of_denseRange`
- Truth anchor: `D5/S3/Topology/Measures/WeakStarPerturbation.normalize_sub_tendsto_zero`
- Dependency: [D5/S3/Topology/ExtremallyDisconnected/WeakStarNormSeparation](../ExtremallyDisconnected/WeakStarNormSeparation.md)
