# One-Parameter Generators of a Locally Compact Group in a Banach Algebra

## Abstract

For a locally compact topological group G with a continuous injective homomorphism rho into the units of a real Banach algebra A, the elements X of A for which t -> exp(t X) lifts through rho to a continuous curve in G form a closed Lie subalgebra of A, and limits of normalized logarithms of elements tending to the identity are such generators.

**Definition 1.1 (One-parameter generators).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)],\ [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)],\ \forall G \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(G\right)],\ [\operatorname{Group}\left(G\right)],\ \forall rho \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(A\right)\right),\; \forall X \in A,\; \operatorname{IsOneParameterGenerator}\left(rho, X\right) \Leftrightarrow \left(\exists gamma \in \mathbb{R} \to G,\; \operatorname{Continuous}\left(gamma\right) \land \left(\forall t \in \mathbb{R},\; \operatorname{val}\left(rho\left(gamma\left(t\right)\right)\right) = \operatorname{exp}\left(\operatorname{smul}\left(t, X\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.IsOneParameterGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let A be a real normed algebra, written NormedRing(A) together with NormedAlgebra(R, A), let G be a group with a topology, and let rho be a group homomorphism from G into the group Units(A) of invertible elements of A. Here val denotes the inclusion of Units(A) into A, exp is the exponential series of A and smul(t, X) is the real multiple t X. An element X of A is a one-parameter generator for rho when the curve t -> exp(t X) of A lifts through rho to a continuous curve: there is a continuous map gamma from the real line to G with val(rho(gamma(t))) = exp(t X) for every real t. No continuity or injectivity of rho is part of the definition.

When rho is injective a lift is unique when it exists and is a one-parameter subgroup of G. Indeed exp((s + t) X) = exp(s X) exp(t X) because s X and t X commute, so rho(gamma(s + t)) = rho(gamma(s) gamma(t)) and injectivity gives gamma(s + t) = gamma(s) gamma(t). The zero element is always a generator, lifted by the constant curve at the identity.

**Theorem 1.2 (Real multiples of a generator).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)],\ [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)],\ \forall G \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(G\right)],\ [\operatorname{Group}\left(G\right)],\ \forall rho \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(A\right)\right),\; \forall X \in A,\; \operatorname{IsOneParameterGenerator}\left(rho, X\right) \Rightarrow \left(\forall c \in \mathbb{R},\; \operatorname{IsOneParameterGenerator}\left(rho, \operatorname{smul}\left(c, X\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If X is a one-parameter generator for rho, then so is the real multiple c X for every real c. In the same setting as the definition, with no further hypothesis on A, G or rho.

If gamma lifts t -> exp(t X), then the reparametrized curve t -> gamma(t c) is continuous and lifts t -> exp(t c X) = exp(t (c X)).

**Theorem 1.3 (Escape lemma).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)],\ [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)],\ \forall G \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(G\right)],\ [\operatorname{Group}\left(G\right)],\ [\operatorname{CompleteSpace}\left(A\right)],\ [\operatorname{IsTopologicalGroup}\left(G\right)],\ [\operatorname{LocallyCompactSpace}\left(G\right)],\ \forall rho \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(A\right)\right),\; \operatorname{Continuous}\left(rho\right) \Rightarrow \left(\operatorname{Injective}\left(rho\right) \Rightarrow \left(\forall g \in \mathbb{N} \to G,\; \operatorname{Tendsto}\left(g, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(1\right)\right) \Rightarrow \left(\forall Y \in \mathbb{N} \to A,\; \operatorname{Tendsto}\left(Y, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(0\right)\right) \Rightarrow \left(\left(\forall k \in \mathbb{N},\; \operatorname{val}\left(rho\left(g\left(k\right)\right)\right) = \operatorname{exp}\left(Y\left(k\right)\right)\right) \Rightarrow \left(\forall X \in A,\; \operatorname{MapClusterPt}\left(X, \operatorname{atTop}\left(\right), {k:\mathbb{N}}\mapsto \operatorname{smul}\left(\left\lVert Y\left(k\right) \right\rVert^{-1}, Y\left(k\right)\right)\right) \Rightarrow \operatorname{IsOneParameterGenerator}\left(rho, X\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.isOneParameterGenerator_of_mapClusterPt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. Let g be a sequence in G tending to the identity, and let Y be a sequence in A tending to 0 with val(rho(g(k))) = exp(Y(k)) for every k. Then every cluster point X of the sequence of directions smul(norm(Y(k))^(-1), Y(k)) is a one-parameter generator for rho. Indices with Y(k) = 0 contribute the direction 0, and 0 is a generator, so no nonvanishing hypothesis on Y is needed. No first countability and no separation axiom on G is assumed.

The statement is the escape lemma of the closed-subgroup theorem of J. von Neumann for closed subgroups of the general linear group and of E. Cartan for closed subgroups of Lie groups. Here the closedness of a linear group is replaced by local compactness of G together with injectivity of rho, in three places. First, fix a compact neighbourhood V of the identity in G. On V the map rho reflects convergence: if points of V have images tending to rho(a), then they tend to a, because every cluster point of them lies in V and has image rho(a), hence equals a by injectivity. Second, there are a positive delta and a neighbourhood U of the identity such that the powers g^n stay in V whenever g lies in U, rho(g) = exp(Y) and n norm(Y) is at most delta; this follows by induction on n from a neighbourhood W of the identity with W W contained in V and from continuity of exp at 0.

Third, pass to a subsequence along which the directions converge to X, with X different from 0 (the case X = 0 is the zero generator). For t in [0, delta] the powers of g(k) with exponent the integer part of t / norm(Y(k)) lie in V and their images tend to exp(t X), so a cluster point v of these powers in the compact set V satisfies val(rho(v)) = exp(t X); negative times are handled with the inverses of g(k) and the sequence -Y(k). Such lifts on [-delta, delta] extend to all real t by taking N-th powers of a lift of exp((t / N) X), and the lift is a homomorphism by injectivity. It is continuous at 0 because its values near 0 lie in V, where rho reflects convergence, and hence continuous everywhere.

Local compactness of G cannot be dropped. Let G be the additive group of rational numbers with its usual topology, A the real numbers and rho(q) = exp(q). Then rho is continuous and injective, g(k) = 1 / (k + 1) tends to the identity 0 and Y(k) = 1 / (k + 1) satisfies the hypotheses, and every direction equals 1. But 1 is not a generator: a continuous curve from the real line into the rationals is constant, while exp(t) is not constant.

**Theorem 1.4 (The set of generators is closed).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)],\ [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)],\ \forall G \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(G\right)],\ [\operatorname{Group}\left(G\right)],\ [\operatorname{CompleteSpace}\left(A\right)],\ [\operatorname{IsTopologicalGroup}\left(G\right)],\ [\operatorname{LocallyCompactSpace}\left(G\right)],\ \forall rho \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(A\right)\right),\; \operatorname{Continuous}\left(rho\right) \Rightarrow \left(\operatorname{Injective}\left(rho\right) \Rightarrow \operatorname{IsClosed}\left(\operatorname{setOf}\left({X:A}\mapsto \operatorname{IsOneParameterGenerator}\left(rho, X\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.isClosed_setOf_isOneParameterGenerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. Then the set of one-parameter generators for rho is a closed subset of A.

Since A is a metric space it suffices to consider a sequence of generators X(n) tending to X, with X different from 0. Let gamma(n) be lifts, fix a compact neighbourhood V of the identity and choose times s(n) with 0 < s(n) < 1 / (n + 1) and gamma(n)(s(n)) in V; such times exist since gamma(n)(0) is the identity and gamma(n) is continuous. The points gamma(n)(s(n)) of V have images exp(s(n) X(n)) tending to 1, so they tend to the identity because rho reflects convergence on V. Their logarithms s(n) X(n) tend to 0 and are eventually nonzero, and their directions tend to X / norm(X). The argument of the escape lemma, applied along this sequence, shows that X / norm(X) is a generator, and so is its multiple X.

**Theorem 1.5 (Sum of two generators).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)],\ [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)],\ \forall G \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(G\right)],\ [\operatorname{Group}\left(G\right)],\ [\operatorname{CompleteSpace}\left(A\right)],\ [\operatorname{IsTopologicalGroup}\left(G\right)],\ [\operatorname{LocallyCompactSpace}\left(G\right)],\ \forall rho \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(A\right)\right),\; \operatorname{Continuous}\left(rho\right) \Rightarrow \left(\operatorname{Injective}\left(rho\right) \Rightarrow \left(\forall X \in A,\; \forall Y \in A,\; \operatorname{IsOneParameterGenerator}\left(rho, X\right) \Rightarrow \left(\operatorname{IsOneParameterGenerator}\left(rho, Y\right) \Rightarrow \operatorname{IsOneParameterGenerator}\left(rho, X + Y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. If X and Y are one-parameter generators for rho, then so is X + Y.

The proof rests on a velocity statement: if a curve c in G is continuous at 0 with val(rho(c(0))) = 1 and s -> val(rho(c(s))) has derivative D at 0, then D is a generator. The derivative of exp at 0 is the identity, so by the inverse function theorem exp has a local inverse near 1 that sends 1 to 0 and has the identity as derivative at 1. Composing it with s -> val(rho(c(s))) gives logarithms Z(s) with val(rho(c(s))) = exp(Z(s)) for small s, Z(0) = 0 and derivative D at 0. For D different from 0 the quotients Z(s) / s tend to D as s decreases to 0, so the directions of Z(s) tend to D / norm(D), and the escape argument along s decreasing to 0 shows that D / norm(D), hence D, is a generator. For lifts gamma of exp(t X) and beta of exp(t Y), the product curve s -> gamma(s) beta(s) is continuous, passes through the identity, and its image exp(s X) exp(s Y) has derivative X + Y at 0 by the product rule.

**Theorem 1.6 (Commutator of two generators).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)],\ [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)],\ \forall G \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(G\right)],\ [\operatorname{Group}\left(G\right)],\ [\operatorname{CompleteSpace}\left(A\right)],\ [\operatorname{IsTopologicalGroup}\left(G\right)],\ [\operatorname{LocallyCompactSpace}\left(G\right)],\ \forall rho \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(A\right)\right),\; \operatorname{Continuous}\left(rho\right) \Rightarrow \left(\operatorname{Injective}\left(rho\right) \Rightarrow \left(\forall X \in A,\; \forall Y \in A,\; \operatorname{IsOneParameterGenerator}\left(rho, X\right) \Rightarrow \left(\operatorname{IsOneParameterGenerator}\left(rho, Y\right) \Rightarrow \operatorname{IsOneParameterGenerator}\left(rho, X \cdot Y - Y \cdot X\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be complete, let G be a locally compact topological group and let rho be continuous and injective. If X and Y are one-parameter generators for rho, then so is the commutator X Y - Y X.

Let gamma lift exp(t X) and beta lift exp(t Y). For each real s the curve t -> gamma(s) beta(t) gamma(s)^(-1) is continuous and lifts exp(t exp(s X) Y exp(-s X)), because conjugation by a unit commutes with the exponential series; so the conjugates exp(s X) Y exp(-s X) are generators. Their derivative at s = 0 is X Y - Y X by the product rule. The difference quotients t^(-1) (exp(t X) Y exp(-t X) - Y) are generators by the sum theorem and real multiples, and they tend to X Y - Y X as t tends to 0 with t different from 0. The set of generators is closed, so the limit X Y - Y X is a generator.

**Definition 1.7 (The Lie subalgebra of generators).**

$$\forall A \in \operatorname{Type}*,\; [\operatorname{NormedRing}\left(A\right)],\ [\operatorname{NormedAlgebra}\left(\mathbb{R}, A\right)],\ \forall G \in \operatorname{Type}*,\; [\operatorname{TopologicalSpace}\left(G\right)],\ [\operatorname{Group}\left(G\right)],\ [\operatorname{CompleteSpace}\left(A\right)],\ [\operatorname{IsTopologicalGroup}\left(G\right)],\ [\operatorname{LocallyCompactSpace}\left(G\right)],\ \forall rho \in \operatorname{MonoidHom}\left(G, \operatorname{Units}\left(A\right)\right),\; \forall hc \in \operatorname{Continuous}\left(rho\right),\; \forall hi \in \operatorname{Injective}\left(rho\right),\; \operatorname{generatorSubalgebra}\left(rho, hc, hi\right) \in \operatorname{LieSubalgebra}\left(\mathbb{R}, A\right) \land \operatorname{carrier}\left(\operatorname{generatorSubalgebra}\left(rho, hc, hi\right)\right) = \operatorname{setOf}\left({X:A}\mapsto \operatorname{IsOneParameterGenerator}\left(rho, X\right)\right)$$

*Formalization.* `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.generatorSubalgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let A be complete, let G be a locally compact topological group and let rho be continuous and injective, with hc a proof of continuity and hi a proof of injectivity. Regard A as a real Lie algebra with the commutator bracket [X, Y] = X Y - Y X. Then generatorSubalgebra(rho, hc, hi) is the Lie subalgebra of A whose carrier is the set setOf of one-parameter generators for rho.

The carrier contains 0, is closed under sums, under real multiples and under the commutator bracket by the preceding theorems, so it is a Lie subalgebra over the real numbers. By the closedness theorem it is moreover a closed subset of A. In the classical closed-subgroup theorem this is the Lie algebra of a closed linear group; here no manifold structure on G is used or asserted.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.IsOneParameterGenerator`
- Truth anchor: `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.add`
- Truth anchor: `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.commutator`
- Truth anchor: `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.generatorSubalgebra`
- Truth anchor: `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.isClosed_setOf_isOneParameterGenerator`
- Truth anchor: `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.isOneParameterGenerator_of_mapClusterPt`
- Truth anchor: `D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators.smul`
