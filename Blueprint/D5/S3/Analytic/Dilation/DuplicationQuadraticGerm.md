# Duplication and the Quadratic Germ

## Abstract

A bounded duplication solution with a prescribed quadratic germ is a cosine.

**Theorem 1.1 (The cosine quadratic germ).**

$$\forall k \in \mathbb{R},\; \operatorname{IsLittleO}\left(\operatorname{nhds}\left(0\right), (t: \mathbb{R} \mapsto (\operatorname{cos}\left((k \cdot t)\right)-(1-(\frac{k^{2}}{2} \cdot t^{2})))), (t: \mathbb{R} \mapsto t^{2})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/DuplicationQuadraticGerm.cosine_quadratic_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real k, the difference between cos(kt) and 1-k^2 t^2/2 is o(t^2) in the full neighborhood filter at zero. This auxiliary expansion is consumed by the global uniqueness theorem below.

**Theorem 1.2 (The germ determines the global solution).**

$$\forall f \in \mathbb{R}\to \mathbb{R},\; \forall k \in \mathbb{R},\; \left(\forall t \in \mathbb{R},\; \left|f\left(t\right)\right| \le 1\right) \Rightarrow \left(\left(\forall t \in \mathbb{R},\; f\left((2 \cdot t)\right) = ((2 \cdot f\left(t\right)^{2})-1)\right) \Rightarrow \left(\operatorname{IsLittleO}\left(\operatorname{nhds}\left(0\right), (t: \mathbb{R} \mapsto (f\left(t\right)-(1-(\frac{k^{2}}{2} \cdot t^{2})))), (t: \mathbb{R} \mapsto t^{2})\right) \Rightarrow \left(\forall t \in \mathbb{R},\; f\left(t\right) = \operatorname{cos}\left((k \cdot t)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/DuplicationQuadraticGerm.eq_cos_of_quadratic_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Kuczma (1964). *On a characterization of the cosine*. DOI: [10.4064/ap-16-1-53-57](https://doi.org/10.4064/ap-16-1-53-57). URL: <https://pldml.icm.edu.pl/pldml/element/bwmeta1.element.desklight-8a8cd230-5b5b-4547-9aaf-2776afdc8fbd/c/apm16_1_07.pdf>.

*Commentary.*

Let f be a real-valued function on the real line, with absolute value at most one, and let k be any real number. Assume the duplication equation f(2t)=2f(t)^2-1 and the quadratic expansion f(t)=1-k^2 t^2/2+o(t^2) at zero. Then f(t)=cos(kt) for every real t. Taking k to be the nonnegative square root of twice a nonnegative quadratic coefficient gives the corresponding coefficient formulation.

The little-o relation uses the full neighborhood filter at zero, including the value there. In particular the expansion forces f(0)=1. If a punctured neighborhood is used instead, the value f(0)=1 must be supplied separately; otherwise the duplication equation also permits the isolated value f(0)=-1/2.

For two bounded duplication solutions f and g, one doubling multiplies their absolute difference by at most four. After n doublings, the difference at t is bounded by 4^n times the difference at t/2^n. If their difference is o(t^2) at zero, this bound is arbitrarily small, and the two functions agree everywhere.

The cosine has the required quadratic germ because its remainder is (k^2/2)(1-sinc(kt/2)^2)t^2 and sinc is continuous with value one at zero. The double-angle identity then supplies the comparison solution. No differentiability of f away from zero is assumed.

The duplication equation and earlier cosine characterizations are classical. Kuczma reports Forder's uniqueness result for even solutions twice differentiable at zero, and proves characterizations with continuity and periodicity assumptions. Those statements do not have the precise bounded quadratic-germ hypotheses here. This citation does not assert priority for the remainder formulation.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/DuplicationQuadraticGerm.cosine_quadratic_germ`
- Truth anchor: `D5/S3/Analytic/Dilation/DuplicationQuadraticGerm.eq_cos_of_quadratic_germ`
