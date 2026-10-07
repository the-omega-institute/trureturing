# Logarithmic Convolution from Absolute Coefficient Mass

## Abstract

Absolute coefficient mass controls a signed logarithmic Dirichlet convolution at every real cutoff.

**Theorem 1.1 (Two absolute moments and an exact mass error bound).**

$$\forall g\in \operatorname{ArithmeticFunction}\left(\mathbb{R}\right), \operatorname{Summable}\left(n\mapsto \left|\operatorname{g}\left(n\right)\right|\right)\Rightarrow \operatorname{Summable}\left(n\mapsto \left|\frac{\operatorname{g}\left(n\right)}{n}\right|\right)\land \operatorname{Summable}\left(n\mapsto \left|\frac{\operatorname{g}\left(n\right)\operatorname{log}\left(n\right)}{n}\right|\right)\land \forall y\in \mathbb{R}, 1\le y\Rightarrow \left|K_{g}(y)-U_{g}y\operatorname{log}\left(y\right)+(U_{g}+V_{g})y\right|\le M_{g}(1+\operatorname{log}\left(y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LogConvolutionMassExpansion.logarithmic_convolution_mass_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terence Tao (2026). *Bounds on the partial sums of the logarithm in Mathlib*. URL: <https://github.com/leanprover-community/mathlib4/blob/0826a5e4ff8877949060d03ce8955545bfb2b47f/Mathlib/Analysis/SpecialFunctions/Log/Sum.lean>.

*Commentary.*

Let g be a real ArithmeticFunction and assume only that the sum of |g(n)| over all natural indices is finite. The carrier gives g(0)=0. The quotients at index zero use Lean's real division convention and equal zero; the logarithmic term there is also zero. Coefficients may have either sign. Define the mass, two signed weighted sums, and the summatory convolution by:$M_{g}= \sum_{n\in \mathbb{N}}\left|\operatorname{g}\left(n\right)\right|, U_{g}= \sum_{n\in \mathbb{N}}\frac{\operatorname{g}\left(n\right)}{n}, V_{g}= \sum_{n\in \mathbb{N}}\frac{\operatorname{g}\left(n\right)\operatorname{log}\left(n\right)}{n}, K_{g}(y)= \sum_{0< n\le \lfloor y\rfloor}\operatorname{DirichletConvolution}\left(g, \log\right)(n)$

Both displayed weighted series converge absolutely. For every real y>=1, the theorem gives the displayed two-term expansion with error at most M_g(1+log y). The cutoff is the natural floor of y. No inverse identity, positive coefficient condition, stronger logarithmic moment hypothesis, or assumed remainder estimate occurs in the theorem.

The proof bounds both absolute weights by |g(n)|. The existing summatory Dirichlet convolution identity rewrites the cutoff sum as a finite sum of g(n) log(floor(y/n)!). For 1<=x<=y, the classical integral bounds for partial logarithmic sums give |log(floor x)!-(x log x-x)|<=1+log y. For 0<x<1, the floor is zero and x(1-log x)<=1; x=0 is handled directly. Coefficients outside the cutoff multiply a zero factorial logarithm. The weighted main terms and the absolutely summable error can therefore be combined by the existing infinite-sum APIs. The triangle inequality bounds the total signed error by the entire absolute mass.

Three private scalar suppliers are minimal ports of Terence Tao's Mathlib/Analysis/SpecialFunctions/Log/Sum.lean at immutable revision 0826a5e4ff8877949060d03ce8955545bfb2b47f, under Apache-2.0. The pinned Mathlib lacks that file. Its factorial identity and upper/lower real-cutoff logarithmic sum bounds supply the scalar estimate; they do not state this generic convolution theorem. The live convolution, moment and infinite-sum composition is repository work using those classical suppliers. No borrowed-proof originality or separate open-problem resolution is claimed. The ports should be retired when equivalent declarations enter the project pin.

The generic result alone does not identify constants of the actual golden Binet inverse or the derivative of its literal Dirichlet series. Those require a separate application with the actual absolute-tail gap and a proved series/derivative bridge.

## References

- Truth anchor: `D5/S3/Arith/LogConvolutionMassExpansion.logarithmic_convolution_mass_expansion`
