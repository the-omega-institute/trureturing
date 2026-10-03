# Independent finite convolution: the exact L1 minimum

## Abstract

The full L1 deviation of independent finite convolution from uniform has an attained exact minimum.

**Definition 1.1 (Ordinary independent convolution).**

$$\begin{gathered}\forall n: \mathbb{N}, \forall p, q: \operatorname{Fin}(n)\to \mathbb{R}, \forall k: \mathbb{N},\\\operatorname{ordinaryConvolution}(n,p,q,k)=\sum_{i,j:\operatorname{Fin}(n), \operatorname{val}(i)+\operatorname{val}(j)=k} p(i) q(j).\end{gathered}$$

*Formalization.* `D5/S3/TotalVariation/IndependentConvolutionL1Minimum.ordinaryConvolution` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilava Metya and Satyaki Mukherjee (2026). *Approximate Uniformity in Finite Convolution Models*. DOI: [10.48550/arXiv.2609.38243](https://doi.org/10.48550/arXiv.2609.38243). URL: <https://arxiv.org/abs/2609.38243v1>.

*Commentary.*

For real arrays p and q on Fin n, the coefficient at natural k is the sum of p(i)q(j) over i+j=k. The indices use ordinary natural addition.

**Definition 1.2 (Full L1 deviation).**

$$\begin{gathered}\forall n: \mathbb{N}, \forall p, q: \operatorname{Fin}(n)\to \mathbb{R},\\W_{n}=\operatorname{Nat.sub}(2n,1),\\\operatorname{fullL1}(n,p,q)=\sum_{k\in \operatorname{range}(W_{n})} \left|\operatorname{ordinaryConvolution}(n,p,q,k)-\frac{1}{W_{n}}\right|.\end{gathered}$$

*Formalization.* `D5/S3/TotalVariation/IndependentConvolutionL1Minimum.fullL1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nilava Metya and Satyaki Mukherjee (2026). *Approximate Uniformity in Finite Convolution Models*. DOI: [10.48550/arXiv.2609.38243](https://doi.org/10.48550/arXiv.2609.38243). URL: <https://arxiv.org/abs/2609.38243v1>.

*Commentary.*

Sum the absolute deviations from 1/(2n-1) over every natural output index k below 2n-1. This is the full L1 norm.

Here W_n is 2*n-1 computed by natural subtraction; range(W_n) contains every k from zero through W_n-1. The denominator is cast to the reals, and division is real division. As in Lean, division by zero has value zero.

**Theorem 1.3 (Attained minimum for all real simplex factors and every n at least three).**

$$\begin{gathered}\forall n: \mathbb{N}, 3\le n\Rightarrow\\\operatorname{IsLeast}\left(\left\{v: \mathbb{R}|\exists p, q: \operatorname{Fin}(n)\to \mathbb{R}, p\in \Delta_{n}\land q\in \Delta_{n}\land \operatorname{fullL1}(n,p,q)=v\right\}, \frac{1}{2n-1}\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/IndependentConvolutionL1Minimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/metya-mukherjee-independent-convolution-l1` (proved) by `D5/S3/TotalVariation/IndependentConvolutionL1Minimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"metya-mukherjee-independent-convolution-l1","declaration_gid":"D5/S3/TotalVariation/IndependentConvolutionL1Minimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nilava Metya and Satyaki Mukherjee (2026). *Approximate Uniformity in Finite Convolution Models*. DOI: [10.48550/arXiv.2609.38243](https://doi.org/10.48550/arXiv.2609.38243). URL: <https://arxiv.org/abs/2609.38243v1>.

*Commentary.*

Write Delta_n for the closed real standard simplex stdSimplex R (Fin n):

$$
\Delta_{n}=\left\{x: \operatorname{Fin}(n)\to \mathbb{R}|(\forall i: \operatorname{Fin}(n), 0\le x(i))\land \sum_{i: \operatorname{Fin}(n)} x(i)=1\right\}.
$$

IsLeast includes membership at the displayed value and a lower bound for every member of the value set. Thus it includes attainment as well as the universal lower bound.

For every natural n at least three, 1/(2n-1) is the least element of the set of fullL1 values of pairs in the closed real standard simplex on Fin n. Zero entries, irrational entries and asymmetric factors are included.

The target is Conjecture 4.7 in section 4.3 of Nilava Metya and Satyaki Mukherjee, Approximate Uniformity in Finite Convolution Models, arXiv:2609.38243v1, equation (21). The source is available at https://arxiv.org/html/2609.38243v1#S4.Thmlemma7 under CC BY-SA 4.0. The attaining pair is the parameter-one member of its equation (22): with m=n-1 and t=1/(2n-1), p assigns one half to each endpoint, q(0)=t and q(j)=2t for j>0.

A zero output coefficient supplies the lower bound directly. Otherwise the actual product of the two generating functions crosses the nonpositive real axis on the ray of angle pi/m. A trigonometric coefficient certificate gives the sharp bound; a crossing of radius greater than one is transported by reversing the output at the fixed width 2m+1. The attaining output equals t/2 at zero, 3t/2 at m, and t elsewhere. The theorem asserts no classification of all equality cases. Source and literature boundaries are recorded in Problems/metya-mukherjee-independent-convolution-l1.md.

## References

- Truth anchor: `D5/S3/TotalVariation/IndependentConvolutionL1Minimum.fullL1`
- Truth anchor: `D5/S3/TotalVariation/IndependentConvolutionL1Minimum.ordinaryConvolution`
- Truth anchor: `D5/S3/TotalVariation/IndependentConvolutionL1Minimum.result`
