# Weighted-tree cycle row error and sharp constant one

## Abstract

Actual rows of a positively weighted finite tree cannot uniformly approximate a positive bidirectional simple cycle below its least directed rate; endpoint folding attains the bound for every cycle size.

**Definition 1.1 (Original positive tree data).**

$$\forall V \in \operatorname{Type},\; \operatorname{TreeData}\left(V\right):\operatorname{Type}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.TreeData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TreeData consists of an actual simple tree, positive real mass at each original vertex, symmetric conductances positive on every edge, and arbitrary nonnegative killing. Conductance values off edges are unused. The theorem concerns finite carriers; connectedness supplies nonemptiness. Fibres need not be connected.

**Definition 1.2 (Killed coarse generators).**

$$\forall B \in \operatorname{Type},\; \operatorname{KilledGenerator}\left(B\right):\operatorname{Type}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.KilledGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A killed generator stores arbitrary nonnegative off-diagonal rates and nonnegative killing. Its diagonal rate field has no effect on its action, since it multiplies a zero difference.

**Definition 1.3 (The original backward generator).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall f \in V \to \operatorname{Real},\; \forall x \in V,\; \operatorname{generator}\left(T, f, x\right) = \sum_{y \in V} \operatorname{ite}\left(\operatorname{Adj}\left(\operatorname{graph}\left(T\right), x, y\right), \frac{\operatorname{conductance}\left(T, x, y\right)}{\operatorname{mass}\left(T, x\right)} \cdot \left(f\left(y\right) - f\left(x\right)\right), 0\right) - \operatorname{killing}\left(T, x\right) \cdot f\left(x\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.generator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only actual neighbours contribute. Division is by the original vertex mass, with no time rescaling; killing is subtracted in the same clock.

**Definition 1.4 (Actual off-label row sums).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \forall x \in V,\; \forall b \in B,\; \operatorname{labelRate}\left(T, p, x, b\right) = \sum_{y \in V} \operatorname{ite}\left(\operatorname{Adj}\left(\operatorname{graph}\left(T\right), x, y\right) \land p\left(y\right) = b, \frac{\operatorname{conductance}\left(T, x, y\right)}{\operatorname{mass}\left(T, x\right)}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.labelRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum runs over every original vertex, retaining exactly actual neighbours with the requested label. No quotient-edge multiplicity or displayed proxy matrix replaces these rows.

**Definition 1.5 (Uniform off-label error).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \forall Q \in \operatorname{KilledGenerator}\left(B\right),\; \operatorname{delta}\left(T, p, Q\right) = \max_{x \in V,b \in B} \operatorname{ite}\left(b \ne p\left(x\right), \lvert\operatorname{labelRate}\left(T, p, x, b\right) - \operatorname{rate}\left(Q, p\left(x\right), b\right)\rvert, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite maximum contains every original vertex row. Same-label entries are assigned zero; the nonnegative finite supremum has bottom zero, so an empty off-label maximum is zero.

**Definition 1.6 (Induced masses).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \forall a \in B,\; \operatorname{inducedMass}\left(T, p, a\right) = \sum_{x \in V} \operatorname{ite}\left(p\left(x\right) = a, \operatorname{mass}\left(T, x\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.inducedMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each label mass is the sum of the original positive masses in its fibre.

**Definition 1.7 (Induced conductances).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \forall a \in B,\; \forall b \in B,\; \operatorname{inducedConductance}\left(T, p, a, b\right) = \sum_{x \in V} \operatorname{ite}\left(p\left(x\right) = a, \sum_{y \in V} \operatorname{ite}\left(\operatorname{Adj}\left(\operatorname{graph}\left(T\right), x, y\right) \land p\left(y\right) = b, \operatorname{conductance}\left(T, x, y\right), 0\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.inducedConductance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual conductances are summed over ordered edges from the first class to the second. No missing edge is inserted.

**Definition 1.8 (Literal mass-weighted compression).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \left(\forall a \in B,\; \forall b \in B,\; \operatorname{rate}\left(\operatorname{compression}\left(T, p\right), a, b\right) = \frac{\sum_{x \in V} \operatorname{ite}\left(p\left(x\right) = a, \operatorname{mass}\left(T, x\right) \cdot \operatorname{labelRate}\left(T, p, x, b\right), 0\right)}{\operatorname{inducedMass}\left(T, p, a\right)}\right) \land \left(\forall a \in B,\; \operatorname{killing}\left(\operatorname{compression}\left(T, p\right), a\right) = \frac{\sum_{x \in V} \operatorname{ite}\left(p\left(x\right) = a, \operatorname{mass}\left(T, x\right) \cdot \operatorname{killing}\left(T, x\right), 0\right)}{\operatorname{inducedMass}\left(T, p, a\right)}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.compression` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rates average the actual original row sums with original masses; killing is averaged with the same masses. The generator action identity in the sharpness theorem proves that this is the literal compression of G on pulled-back label functions. Empty fibres are permitted in the definition; all theorem label maps are onto.

**Definition 1.9 (Coarse backward action).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall Q \in \operatorname{KilledGenerator}\left(B\right),\; \forall f \in B \to \operatorname{Real},\; \forall a \in B,\; \operatorname{coarseAction}\left(Q, f, a\right) = \sum_{b \in B} \operatorname{rate}\left(Q, a, b\right) \cdot \left(f\left(b\right) - f\left(a\right)\right) - \operatorname{killing}\left(Q, a\right) \cdot f\left(a\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.coarseAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Diagonal rates cancel. This action includes the complete killed diagonal through the rate differences and killing term.

**Definition 1.10 (Original mass average).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \forall g \in V \to \operatorname{Real},\; \forall a \in B,\; \operatorname{massAverage}\left(T, p, g, a\right) = \frac{\sum_{x \in V} \operatorname{ite}\left(p\left(x\right) = a, \operatorname{mass}\left(T, x\right) \cdot g\left(x\right), 0\right)}{\operatorname{inducedMass}\left(T, p, a\right)}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.massAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the original-mass average of a vertex function on a label class.

**Definition 1.11 (Every direction of a full simple cycle).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall Q \in \operatorname{KilledGenerator}\left(B\right),\; \forall eta \in \operatorname{Real},\; \operatorname{CycleRates}\left(Q, eta\right) \Leftrightarrow \left(\exists n \in \operatorname{Nat},\; \exists i \in \operatorname{Fin}\left(n + 3\right) \to B,\; \operatorname{Injective}\left(i\right) \land \left(\forall a \in \operatorname{Fin}\left(n + 3\right),\; \forall b \in \operatorname{Fin}\left(n + 3\right),\; \operatorname{Adj}\left(\operatorname{cycleGraph}\left(n + 3\right), a, b\right) \Rightarrow eta \le \operatorname{rate}\left(Q, i\left(a\right), i\left(b\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.CycleRates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An injective cyclic list has length n+3, hence at least three. Both ordered directions of every cycle edge satisfy the lower bound, while all other labels and rates remain arbitrary.

**Theorem 1.12 (Universal actual-tree lower bound).**

$$\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \operatorname{Surjective}\left(p\right) \Rightarrow \left(\forall Q \in \operatorname{KilledGenerator}\left(B\right),\; \forall eta \in \operatorname{Real},\; \left(0 < eta \land \operatorname{CycleRates}\left(Q, eta\right)\right) \Rightarrow eta \le \operatorname{delta}\left(T, p, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.cycle_row_error_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict the original tree to vertices carrying cycle labels. If every such vertex had a neighbour of each adjacent cycle label, cycle degree two and injectivity would give two distinct actual neighbours at every vertex of this induced forest. A finite nonempty forest component has a leaf, a contradiction. Thus an actual original row misses an adjacent cycle class, has row sum zero there, and differs from its specified coarse rate by at least eta. No missing-neighbour hypothesis, connected-fibre hypothesis, diagonal condition or killing equality is assumed.

**Definition 1.13 (The entire sharp path family).**

$$\forall k \in \operatorname{Nat},\; \forall eta \in \operatorname{Real},\; \forall he \in 0 < eta,\; \operatorname{graph}\left(\operatorname{sharpPath}\left(k, eta\right)\right) = \operatorname{pathGraph}\left(k + 1\right) \land \left(\forall x \in \operatorname{Fin}\left(k + 1\right),\; \operatorname{mass}\left(\operatorname{sharpPath}\left(k, eta\right), x\right) = 1 \land \left(\operatorname{killing}\left(\operatorname{sharpPath}\left(k, eta\right), x\right) = 0 \land \left(\forall y \in \operatorname{Fin}\left(k + 1\right),\; \operatorname{conductance}\left(\operatorname{sharpPath}\left(k, eta\right), x, y\right) = 2 \cdot eta\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.sharpPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There are k+1 original vertices and k edges. Every original mass is one, every edge conductance is 2 eta, and killing vanishes. Positivity follows for every real eta>0.

**Definition 1.14 (Endpoint-folding labels).**

$$\forall k \in \operatorname{Nat},\; \forall hk \in 0 < k,\; \forall x \in \operatorname{Fin}\left(k + 1\right),\; \operatorname{endpointFold}\left(k\right)\left(x\right) = \operatorname{ite}\left(\operatorname{val}\left(x\right) < k, \operatorname{val}\left(x\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.endpointFold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertices zero through k-1 retain their indices; vertex k receives label zero. The zero fibre consists of the two endpoints and is disconnected for k>=3.

**Theorem 1.15 (All sizes and scales attain the bound).**

$$\forall k \in \operatorname{Nat},\; \forall hk \in 3 \le k,\; \forall eta \in \operatorname{Real},\; \forall he \in 0 < eta,\; \operatorname{Surjective}\left(\operatorname{endpointFold}\left(k\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \operatorname{inducedMass}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), a\right) = \operatorname{ite}\left(a = 0, 2, 1\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{inducedConductance}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), a, b\right) = \operatorname{ite}\left(\operatorname{Adj}\left(\operatorname{cycleGraph}\left(k\right), a, b\right), 2 \cdot eta, 0\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a, b\right) = \operatorname{ite}\left(\operatorname{Adj}\left(\operatorname{cycleGraph}\left(k\right), a, b\right), \operatorname{ite}\left(a = 0, eta, 2 \cdot eta\right), 0\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \operatorname{killing}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a\right) = 0\right) \land \left(\operatorname{CycleRates}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), eta\right) \land \left(\left(\exists a \in \operatorname{Fin}\left(k\right),\; \exists b \in \operatorname{Fin}\left(k\right),\; \operatorname{Adj}\left(\operatorname{cycleGraph}\left(k\right), a, b\right) \land \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a, b\right) = eta\right) \land \left(\left(\forall x \in \operatorname{Fin}\left(k + 1\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \lvert\operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), x, b\right) - \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), \operatorname{endpointFold}\left(k\right)\left(x\right), b\right)\rvert \le eta\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; a \ne 0 \Rightarrow \operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{castSucc}\left(a\right), b\right) = \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a, b\right)\right) \land \left(\left(\forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), 0, b\right) = \operatorname{ite}\left(\operatorname{val}\left(b\right) = 1, 2 \cdot eta, 0\right)\right) \land \left(\left(\forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{last}\left(k\right), b\right) = \operatorname{ite}\left(\operatorname{val}\left(b\right) + 1 = k, 2 \cdot eta, 0\right)\right) \land \left(\left(\forall f \in \operatorname{Fin}\left(k\right) \to \operatorname{Real},\; \forall a \in \operatorname{Fin}\left(k\right),\; \operatorname{coarseAction}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), f, a\right) = \operatorname{massAverage}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{generator}\left(\operatorname{sharpPath}\left(k, eta\right), f\circ\operatorname{endpointFold}\left(k\right)\right), a\right)\right) \land \operatorname{delta}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right)\right) = eta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.endpoint_folding_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each integer k>=3 and real eta>0, the indicated literal compression has mass two at zero and one elsewhere, conductance 2 eta on every cycle edge, rate eta out of zero and 2 eta out of every other label. Every directed cycle rate is at least eta and a rate out of zero equals eta. Every internal original row agrees with Q. At the first endpoint the only nonzero row entry is 2 eta toward label one; at the last it is 2 eta toward label k-1. Both endpoint errors are bounded by eta, as are all rows, and the universal lower bound gives exact delta=eta. The full operator compression identity is included. This establishes sharpness in the unrestricted weighted-tree comparison class; it makes no fixed native orbit, native-operation, physical-space, or arbitrary memory/encoding assertion.

**Theorem 1.16 (The complete cycle obstruction and optimal constant).**

$$\left(\forall V \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(B\right)] \forall T \in \operatorname{TreeData}\left(V\right),\; \forall p \in V \to B,\; \operatorname{Surjective}\left(p\right) \Rightarrow \left(\forall Q \in \operatorname{KilledGenerator}\left(B\right),\; \forall eta \in \operatorname{Real},\; \left(0 < eta \land \operatorname{CycleRates}\left(Q, eta\right)\right) \Rightarrow eta \le \operatorname{delta}\left(T, p, Q\right)\right)\right) \land \left(\forall k \in \operatorname{Nat},\; \forall hk \in 3 \le k,\; \forall eta \in \operatorname{Real},\; \forall he \in 0 < eta,\; \operatorname{Surjective}\left(\operatorname{endpointFold}\left(k\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \operatorname{inducedMass}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), a\right) = \operatorname{ite}\left(a = 0, 2, 1\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{inducedConductance}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), a, b\right) = \operatorname{ite}\left(\operatorname{Adj}\left(\operatorname{cycleGraph}\left(k\right), a, b\right), 2 \cdot eta, 0\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a, b\right) = \operatorname{ite}\left(\operatorname{Adj}\left(\operatorname{cycleGraph}\left(k\right), a, b\right), \operatorname{ite}\left(a = 0, eta, 2 \cdot eta\right), 0\right)\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \operatorname{killing}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a\right) = 0\right) \land \left(\operatorname{CycleRates}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), eta\right) \land \left(\left(\exists a \in \operatorname{Fin}\left(k\right),\; \exists b \in \operatorname{Fin}\left(k\right),\; \operatorname{Adj}\left(\operatorname{cycleGraph}\left(k\right), a, b\right) \land \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a, b\right) = eta\right) \land \left(\left(\forall x \in \operatorname{Fin}\left(k + 1\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; \lvert\operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), x, b\right) - \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), \operatorname{endpointFold}\left(k\right)\left(x\right), b\right)\rvert \le eta\right) \land \left(\left(\forall a \in \operatorname{Fin}\left(k\right),\; \forall b \in \operatorname{Fin}\left(k\right),\; a \ne 0 \Rightarrow \operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{castSucc}\left(a\right), b\right) = \operatorname{rate}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), a, b\right)\right) \land \left(\left(\forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), 0, b\right) = \operatorname{ite}\left(\operatorname{val}\left(b\right) = 1, 2 \cdot eta, 0\right)\right) \land \left(\left(\forall b \in \operatorname{Fin}\left(k\right),\; \operatorname{labelRate}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{last}\left(k\right), b\right) = \operatorname{ite}\left(\operatorname{val}\left(b\right) + 1 = k, 2 \cdot eta, 0\right)\right) \land \left(\left(\forall f \in \operatorname{Fin}\left(k\right) \to \operatorname{Real},\; \forall a \in \operatorname{Fin}\left(k\right),\; \operatorname{coarseAction}\left(\operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right), f, a\right) = \operatorname{massAverage}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{generator}\left(\operatorname{sharpPath}\left(k, eta\right), f\circ\operatorname{endpointFold}\left(k\right)\right), a\right)\right) \land \operatorname{delta}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right), \operatorname{compression}\left(\operatorname{sharpPath}\left(k, eta\right), \operatorname{endpointFold}\left(k\right)\right)\right) = eta\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.cycle_row_error_and_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete statement combines the universal lower bound with the full endpoint-folding construction for every k>=3 and every eta>0. Both clauses use the same original generator, actual row norm, masses and clock described above.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.CycleRates`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.KilledGenerator`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.TreeData`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.coarseAction`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.compression`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.cycle_row_error_and_sharpness`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.cycle_row_error_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.delta`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.endpointFold`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.endpoint_folding_sharpness`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.generator`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.inducedConductance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.inducedMass`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.labelRate`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.massAverage`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError.sharpPath`
