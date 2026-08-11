# Counting Hypotheses with Uniform Finite Fano

## Abstract

Uniform finite Fano bounds hypothesis count in a side-condition-free product form and a quotient form valid below unit error.

**Theorem 1.1 (The product form bounds the resolvable hypothesis count).**

$$(1-\varepsilon) \cdot \log \lvert X \rvert \le I(X; Y)+ \log 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoDivergenceForm.fano_hypothesis_count_product_bound_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This general module was split from the arbitrary-reference material because an artifact's generality is bounded above by its dependency closure. The instance-level frozen DemonIdentity cannot be imported by a general artifact under SL-010. An independent walk of this module's transitive import closure found fourteen modules, all general, with DemonIdentity absent. The split therefore follows the dependency layer rather than merely dividing the exposition.

Let X and Y be finite, let p be a nonnegative mass function on Y x X with total mass one, and let g from Y to X be arbitrary. Assume that the X-marginal obtained from the swapped law is the constant mass 1/card X and that the p-mass on pairs with g(y) unequal to x is at most epsilon. With no cardinality restriction and no condition on epsilon, the theorem gives

$$
(1-\varepsilon) \cdot \log \lvert X \rvert \le I(X; Y)+ \log 2
$$

The previous wave used the already-frozen Fano relation to lower-bound error. This theorem changes the direction of use and solves the same relation for the number of candidates. It is not a new information inequality. In operational terms, at error below one an observation carrying I nats cannot reliably resolve substantially more than exp((I + log 2)/(1 - epsilon)) candidates.

The product form is primary because it has no epsilon < 1 side condition. At epsilon equal to one and zero mutual information, its left side vanishes for every finite X and the statement reduces to

$$
0\le \log 2
$$

This is true for every candidate count and therefore imposes no ceiling. That vacuity is required: an estimator permitted to be wrong with probability one constrains nothing.

**Theorem 1.2 (The quotient form isolates the logarithmic candidate budget).**

$$\log \lvert X \rvert \le \frac{I(X; Y)+ \log 2}{(1-\varepsilon)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/FanoDivergenceForm.fano_hypothesis_count_bound_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same finite-space, probability-law, uniform hidden-marginal, arbitrary-estimator, and error-at-most-epsilon hypotheses as the product theorem, add exactly the condition epsilon < 1. The conclusion is

$$
\log \lvert X \rvert \le \frac{I(X; Y)+ \log 2}{(1-\varepsilon)}
$$

The extra hypothesis appears only because the proof divides by 1 - epsilon and needs that quantity positive to preserve the order. It is absent from the product theorem rather than silently inherited by it.

The informative compiled illustration takes zero mutual information and epsilon equal to one half. The budget is log 2 divided by one half, which equals log 4. For a natural candidate count M, the source checks that M at least one together with log M at most log 4 forces M at most four:

$$
I=0, \varepsilon=\frac{1}{2}, M\ge 1, \log M\le \log 4 \Rightarrow M\le 4
$$

Exhibiting both the four-candidate ceiling and the epsilon-equals-one vacuous regime is substantive. A ceiling that binds in no regime would be worthless, while a ceiling that never becomes vacuous would be wrong. Together the two examples show that the rearranged bound both constrains and releases the hypothesis count in the regimes where it should.

## References

- Truth anchor: `D5/S3/Estimation/FanoDivergenceForm.fano_hypothesis_count_bound_uniform`
- Truth anchor: `D5/S3/Estimation/FanoDivergenceForm.fano_hypothesis_count_product_bound_uniform`
- Dependency: [D5/S3/Estimation/FanoErrorBound](FanoErrorBound.md)
