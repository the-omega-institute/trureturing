# A Helly bound for classical signaling dimension

## Abstract

At most binomially many inputs certify that a finite classical channel requires more than d messages.

**Definition 1.1 (Simulation with finite shared randomness).**

$$\forall (\alpha: \operatorname{Type}), (\forall (k: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (p: (\alpha) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), ((\operatorname{D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate.IsSimulable}\left(d, p\right)) \Leftrightarrow (\exists (n: \mathbb{N}), (\exists (q: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\exists (t: (\operatorname{Fin}\left(n\right)) \to ((\alpha) \to ((\operatorname{Fin}\left(d\right)) \to (\mathbb{R})))), (\exists (r: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(d\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R})))), ((\forall (l: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) \le q\left(l\right))) \land ((\sum_{l: \operatorname{Fin}\left(n\right)} (q\left(l\right)) = (1: \mathbb{R})) \land ((\forall (l: \operatorname{Fin}\left(n\right)), (\operatorname{D5.S3.Estimation.DecisionRisk.DescentDefectBounds.IsRowStochastic}\left(t\left(l\right)\right))) \land ((\forall (l: \operatorname{Fin}\left(n\right)), (\operatorname{D5.S3.Estimation.DecisionRisk.DescentDefectBounds.IsRowStochastic}\left(r\left(l\right)\right))) \land (\forall (x: \alpha), (\forall (y: \operatorname{Fin}\left(k\right)), (p\left(x, y\right) = \sum_{l: \operatorname{Fin}\left(n\right)} (q\left(l\right) \cdot \sum_{\mu: \operatorname{Fin}\left(d\right)} (r\left(l\right)\left(\mu, y\right) \cdot t\left(l\right)\left(x, \mu\right))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.IsSimulable` (`✓ std3`).

*Citation.* Brian Doolittle; Eric Chitambar (2021). *Certifying the classical simulation cost of a quantum channel*. DOI: [10.1103/PhysRevResearch.3.043073](https://doi.org/10.1103/PhysRevResearch.3.043073). URL: <https://arxiv.org/abs/2102.12543v1>.

*Commentary.*

A simulation uses a shared random index l in Fin n, a probability distribution q, an encoder t l from inputs to d messages, and a decoder r l from messages to k outputs. Each encoder and decoder is row stochastic: all its entries are nonnegative and each row sums to one. The channel is their composition averaged with weights q l. All sums range over the entire displayed finite type.

This is equation (Eq:d-simulate) in arXiv:2102.12543v1, main.tex lines 150–158; lines 160–162 define the signaling polytope of such channels. The source writes P(y|x) as a column stochastic matrix; here p x y places the input first. The definition allows an arbitrary input type α and natural k and d, and explicitly requires finite shared randomness.

**Theorem 1.2 (A small input set still excludes d-message simulation).**

$$\forall (m: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (d: \mathbb{N}), (((1: \mathbb{N}) \le d) \to ((d < k) \to (\forall (p: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), ((\operatorname{D5.S3.Estimation.DecisionRisk.DescentDefectBounds.IsRowStochastic}\left(p\right)) \to ((\neg (\operatorname{D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate.IsSimulable}\left(d, p\right))) \to (\exists (i: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)), ((\operatorname{Finset.Nonempty}\left(i\right)) \land ((\operatorname{Finset.card}\left(i\right) \le \operatorname{Nat.choose}\left(k, d\right)) \land (\neg (\operatorname{D5.S3.Quantum.QuantumChannels.SignalingDimensionHellyCertificate.IsSimulable}\left(d, \operatorname{Set.domRestrict}\left((\operatorname{SetLike.coe}\left(i\right): \operatorname{Set}\left(\operatorname{Fin}\left(m\right)\right)), p\right)\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.result` (`✓ std3`). ∎

*Resolves.* `Problems/doolittle-chitambar-2021-signaling-dimension-certificate-size` (proved) by `D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"doolittle-chitambar-2021-signaling-dimension-certificate-size","declaration_gid":"D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Brian Doolittle; Eric Chitambar (2021). *Certifying the classical simulation cost of a quantum channel*. DOI: [10.1103/PhysRevResearch.3.043073](https://doi.org/10.1103/PhysRevResearch.3.043073). URL: <https://arxiv.org/abs/2102.12543v1>.

*Commentary.*

For every finite row stochastic channel p, with 1 ≤ d < k, failure of d-message simulation already occurs on a nonempty set i of at most binomial(k,d) inputs. The restriction keeps all k outputs and uses the subtype of inputs belonging to i. The hypotheses on d, k and p are implications in the formula. SetLike.coe makes the conversion of i from a finite set to a set explicit; both the cardinality and the binomial coefficient are natural numbers. This is the certificate-size conclusion conjectured in arXiv:2102.12543v1, main.tex line 409. It asserts neither sharpness of the bound nor a classification of facets.

Let S be the type of d-element subsets s of Fin k and let K be its cardinality, binomial(k,d). For each input x define Fₓ to consist of vectors q on S with nonnegative coordinates summing to one for which there are nonnegative numbers aₛᵧ, zero when y is outside s, such that the sum over y of aₛᵧ is qₛ and the sum over s of aₛᵧ is p x y. Thus q is a common distribution on output subsets, while a describes how its mass produces the row at x.

First, a stochastic matrix u on finite types decomposes into deterministic functions f with weights equal to the product over x of u x (f x). These weights are nonnegative. Distributing the sums over functions as a product of row sums shows that their total is one. The product row marginal identity shows that their weighted indicator of f x = y is u x y.

Next, consider a finite mixture of deterministic maps v j with nonnegative weights w j summing to one, each map having at most d outputs. Since d < k, extend each image to a d-element subset s j. For each subset t, sum the weights of the indices with s j = t to obtain q t. For each input x and output y, sum the weights with both s j = t and v j x = y to obtain a t y. Nonnegativity, support, and the two sum identities show that this single q belongs to every Fₓ.

Apply the deterministic decomposition to every encoder and decoder of a simulation. The mixture indices are triples (l,f,g), where f maps inputs to Fin d and g maps Fin d to Fin k. Give the triple weight q l times the product over x of t l x (f x), times the product over μ of r l μ (g μ). The associated map sends x to g(f x), so its image has at most d elements. The product weights sum to one; summing first over g and then over f, using the marginal identities, recovers the simulation equation. The preceding construction therefore gives a point in every Fₓ.

Conversely, any mixture indexed by a finite type can be indexed by Fin of its cardinality using a bijection, without changing its sums. Suppose the input type is nonempty and a single q belongs to every Fₓ. Choose the arrays a separately for each x, and for each s choose a bijection e s from Fin d to the elements of s. When q s is nonzero, define the encoder c s x μ as a x s (e s μ) divided by q s. When q s is zero, use the point mass at z = 0 in Fin d, which exists because 1 ≤ d. Nonnegativity and the sum identity make c s stochastic. Use the deterministic decoder sending μ to e s μ. If q s is zero, every a x s y is zero because nonnegative entries sum to zero. If q s is nonzero, cancellation and the bijection e s show that the contribution of subset s is exactly a x s y.

Finally decompose each c s into deterministic encoders f. The pair (s,f) receives weight q s times the product over x of c s x (f x), encoder f, and the same decoder for s. These weights are nonnegative and sum to one. Their row marginals give the contribution a x s y; summing over s gives p x y. Reindexing this finite mixture constructs a simulation. For an empty input type a simulation exists directly: take one shared index, the vacuous encoder, and a decoder constantly returning output zero, which exists because 1 ≤ d < k.

Each Fₓ is convex. Given two points with arrays a and u and nonnegative coefficients b and c with b + c = 1, combine their distributions and arrays coordinatewise as b a + c u. The support and normalization equations are preserved, and the output marginal becomes b times p x y plus c times p x y, again p x y.

To obtain the normalized form of Helly's theorem, consider any finite family of convex sets of vectors on a nonempty finite type β, all having coordinate sum one. Choose a coordinate s and delete it, mapping vectors linearly to the coordinates indexed by b ≠ s. This map is injective on the sum-one hyperplane: equality of the other coordinates and their sums forces equality at s. The target space has dimension cardinality(β) − 1, as the deleted-coordinate type together with one point is in bijection with β. If every subfamily of at most cardinality(β) sets had a common point, their linear images would satisfy Convex.helly_theorem'. A common image point lifts to a point in each original set; injectivity makes all these lifts equal. An empty total intersection therefore gives a nonempty subfamily of at most cardinality(β) sets with empty intersection. The empty family itself has a common zero vector.

Now failure of simulation first implies m > 0, by the empty-input construction. Also K > 0 because d < k. The sets Fₓ have empty total intersection, since a common point would give a simulation by the converse construction. Apply the normalized Helly argument to these convex sets to obtain a nonempty input set i with at most K elements and empty intersection. If the restriction of p to i were simulable, the forward construction would give one q belonging to Fₓ for every x in i, contradicting that empty intersection. Substituting K = binomial(k,d) proves the bound.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.IsSimulable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/SignalingDimensionHellyCertificate.result`
- Dependency: [D5/S3/Estimation/DataProcessing/OrderedCoordinateHistoryInterpreter](../../Estimation/DataProcessing/OrderedCoordinateHistoryInterpreter.md)
- Dependency: [D5/S3/Estimation/DecisionRisk/DescentDefectBounds](../../Estimation/DecisionRisk/DescentDefectBounds.md)
