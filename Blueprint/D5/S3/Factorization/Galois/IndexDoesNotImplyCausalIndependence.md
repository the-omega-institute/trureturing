# Index Does Not Imply Causal Independence

## Abstract

Distinct prime addresses can share one mechanism, while separate noise coordinates supply the independent control.

**Definition 1.1 (Crosswise recombination of realized readout values).**

$$\operatorname{CI}(L, R) \iff \forall e_{L}, e_{R}, \exists e, \operatorname{L}(e) = \operatorname{L}(e_{L}) \land \operatorname{R}(e) = \operatorname{R}(e_{R}).$$

*Formalization.* `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.CausallyIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two readouts satisfy the named predicate when every left value and right value realized by possibly different latent states can be realized together by one latent state. This is the minimal fiber-transversality interpretation selected for this module.

**Definition 1.2 (Every address reads one supplied exogenous mechanism).**

$$\forall p, e, K_{p}(e) = \operatorname{h}(e).$$

*Formalization.* `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.sharedNoiseModule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The address parameter changes only the module's address. Its value is the same supplied noise function at every address, making mechanism sharing explicit rather than inferred from a label.

**Definition 1.3 (Each address reads its own exogenous coordinate).**

$$\forall p, e, C_{p}(e) = e(p).$$

*Formalization.* `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.coordinateNoiseModule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The control family reads coordinate p from a natural-number-indexed noise state. Distinct addresses can therefore be assigned values independently by changing one coordinate and preserving another.

**Theorem 1.4 (Distinct prime addresses can remain causally coupled).**

$$\exists p, q \in Primes,\\{}p \neq q \land {\forall e, K_{p}(e) = e \land K_{q}(e) = e} \land \neg\operatorname{CI}(K_{p}, K_{q}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.distinct_prime_indices_can_share_exogenous_noise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the prime addresses two and three, but let both modules expose the identity function on one Boolean exogenous variable. False from one latent state cannot be combined with true from another, so crosswise recombination fails.

Primality certifies that the witnesses are prime addresses but is not used by the coupling argument. The same family of source phenomena also includes directed edges, common environments, shared apparatus disturbance, and other coupled mechanisms.

The strict joint-kernel refinement in SamePrimeScaleRedundancy is about discrimination, not generation. It has no premise or conclusion about exogenous noise and does not contradict this mechanism-level counterexample.

**Theorem 1.5 (Distinct coordinate-noise addresses are independent).**

$$\forall p, q \in \mathbb{N}, p \neq q \Rightarrow \operatorname{CI}(C_{p}, C_{q}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.distinct_indices_imply_independence_for_coordinate_noise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given two latent noise states, overwrite coordinate p of the second with coordinate p of the first. The left value is then retained, and p unequal to q ensures that the right coordinate is unchanged. This is the required positive control.

**Lemma 1.6 (Coordinate-noise independence needs unequal addresses).**

$$\operatorname{Prime}(2) \land \neg\operatorname{CI}(C_{2}, C_{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.index_distinctness_is_necessary_for_coordinate_noise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the single prime address two, both readouts inspect the same Boolean coordinate. False and true cannot occur there simultaneously. This concrete theorem proves the control theorem's sole hypothesis necessary and also audits the equal-index mechanism.

## References

- Truth anchor: `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.CausallyIndependent`
- Truth anchor: `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.coordinateNoiseModule`
- Truth anchor: `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.distinct_indices_imply_independence_for_coordinate_noise`
- Truth anchor: `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.distinct_prime_indices_can_share_exogenous_noise`
- Truth anchor: `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.index_distinctness_is_necessary_for_coordinate_noise`
- Truth anchor: `D5/S3/Factorization/Galois/IndexDoesNotImplyCausalIndependence.sharedNoiseModule`
