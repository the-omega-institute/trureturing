# A Counterexample to One-Divisor Interval-Density Unimodality

## Abstract

Exact periodic densities refute unimodality of the one-divisor interval density.

**Definition 1.1 (Natural density).**

$$\forall A \in Set\left(\mathbb{N}\right),\; \forall delta \in \mathbb{R},\; (hasDensity\left(A, \delta\right)) \Leftrightarrow (Tendsto\left(\Lambda N, ((card\left(filter\left(range\left(N\right), \Lambda k, (k \in A)\right)\right)) / (N)), atTop, nhds\left(\delta\right)\right))$$

*Formalization.* `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.hasDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A set has density delta when the proportion of its members in the first N natural numbers tends to delta as N tends to infinity.

**Theorem 1.2 (Density of a periodic set).**

$$\forall A \in Set\left(\mathbb{N}\right),\; \forall P \in \mathbb{N},\; (0 < P) \Rightarrow ((Periodic\left(\Lambda k, (k \in A), P\right)) \Rightarrow (hasDensity\left(A, (card\left(filter\left(range\left(P\right), \Lambda k, (k \in A)\right)\right)) / (P)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.hasDensity_of_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive period P, split N into complete periods and a remainder. The complete periods contribute the same count, while the remainder is bounded by P and vanishes after division by N.

**Definition 1.3 (Exactly one divisor in an interval).**

$$\forall n \in \mathbb{N}, m \in \mathbb{N}, N \in \mathbb{N},\; (exactlyOneDivisorIn\left(n, m, N\right)) \Leftrightarrow (\exists! d: \mathbb{N}, ((n < d) \land \left((d < m) \land (d \mid N)\right)))$$

*Formalization.* `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.exactlyOneDivisorIn` (`✓ std3`).

*Citation.* Gérald Tenenbaum (2013). *Some of Erdős' Unconventional Problems in Number Theory, Thirty-four Years Later*. DOI: [10.1007/978-3-642-39286-3_23](https://doi.org/10.1007/978-3-642-39286-3_23).

*Commentary.*

An integer N satisfies the interval predicate when there is a unique divisor d strictly between n and m.

**Definition 1.4 (The one-divisor interval density).**

Lean statement: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.epsOne`

*Formalization.* `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.epsOne` (`✓ std3`).

*Citation.* Gérald Tenenbaum (2013). *Some of Erdős' Unconventional Problems in Number Theory, Thirty-four Years Later*. DOI: [10.1007/978-3-642-39286-3_23](https://doi.org/10.1007/978-3-642-39286-3_23).

*Commentary.*

The value epsOne(n,m) is the natural density of integers having exactly one divisor in the open interval from n to m. It is set to zero if no such density exists; the periodic-density theorem proves existence.

**Definition 1.5 (Weak unimodality on a tail).**

$$\forall f \in \mathbb{N} \to \mathbb{R},\; \forall lo \in \mathbb{N},\; (Unimodal\left(f, lo\right)) \Leftrightarrow (\exists m0: \mathbb{N}, ((lo \le m0) \land \left((\forall a \in \mathbb{N}, b \in \mathbb{N},\; (lo \le a) \Rightarrow ((a \le b) \Rightarrow ((b \le m0) \Rightarrow (f\left(a\right) \le f\left(b\right))))) \land (\forall a \in \mathbb{N}, b \in \mathbb{N},\; (m0 \le a) \Rightarrow ((a \le b) \Rightarrow (f\left(b\right) \le f\left(a\right))))\right)))$$

*Formalization.* `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.Unimodal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A function is weakly unimodal from lo when some mode m0 lies at or after lo, the function is nondecreasing from lo through m0, and it is nonincreasing from m0 onward.

**Definition 1.6 (The printed unimodality suggestion).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; Unimodal\left(\Lambda m, (epsOne\left(n, m\right)), n + 2\right))$$

*Formalization.* `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim` (`✓ std3`).

*Citation.* Gérald Tenenbaum (2013). *Some of Erdős' Unconventional Problems in Number Theory, Thirty-four Years Later*. DOI: [10.1007/978-3-642-39286-3_23](https://doi.org/10.1007/978-3-642-39286-3_23).

*Commentary.*

Erdős writes: Perhaps ε₁(n,m) is unimodular for m greater than n+1, but I know nothing about this. The tail begins at n+2.

**Theorem 1.7 (A strict valley refutes unimodality).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/erdos-1979-exactly-one-divisor-unimodality` (refuted) by `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"erdos-1979-exactly-one-divisor-unimodality","declaration_gid":"D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gérald Tenenbaum (2013). *Some of Erdős' Unconventional Problems in Number Theory, Thirty-four Years Later*. DOI: [10.1007/978-3-642-39286-3_23](https://doi.org/10.1007/978-3-642-39286-3_23).

*Commentary.*

For n=2 the exact values at m=6, 7, and 8 are 13/30, 11/30, and 13/35. The decrease followed by an increase contradicts either possible side of every proposed mode, so the printed assertion is false.

## References

- Truth anchor: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.Unimodal`
- Truth anchor: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.claim`
- Truth anchor: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.epsOne`
- Truth anchor: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.exactlyOneDivisorIn`
- Truth anchor: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.hasDensity`
- Truth anchor: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.hasDensity_of_periodic`
- Truth anchor: `D5/S3/Arith/Density/ErdosExactlyOneDivisorUnimodalityRefutation.result`
