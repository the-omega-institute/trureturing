# A sharper positive cone for the original odd-wrap quotients

## Abstract

Finite binomial product estimates sharpen the positive odd-wrap return cone to t at least p for odd p at least five.

**Theorem 1.1 (The original count difference is strictly positive for t>=p and odd p>=5).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyOddWrapPositiveCone.actual_positive_odd_wrap_cone`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyOddWrapPositiveCone.actual_positive_odd_wrap_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p,t be integers, with p>=5 odd and t>=p. The theorem uses original_return_pair from the single-crossing module: its components are the signed coordinate-word return counts for the complete original (1,9) and (3,3) relation lattices at m=6t-1 and length (p*m).toNat. It proves W19<W33 throughout this cone. Composite odd p are included. The earlier unique-threshold theorem still covers all odd p>=3; this sharper sufficient cone bounds the threshold above by p.

First set t=p, a=3p^2 and n=p(6p-1). Write A=choose(n,a), B=choose(n,a+p), D=choose(n,a+4p). The new endpoint estimate proves A/B<199/100 and B/D>100. Positivity of B and D gives A+D<2B. The exact original odd-wrap counts W19=2(A+D) and W33=4B therefore give the strict actual comparison at t=p.

Put R=6p^2-p+1 and x_i=(p+2i+1)/R for 0<=i<p. Multiplying the existing adjacent-index binomial recurrence gives A/B as the finite product of (1+x_i)/(1-x_i). For p>=5, each x_i is between zero and 1/10, and their sum is at most 25/73. The existing finite logarithm remainder bound at order two gives log((1+x)/(1-x))<=2x+2x^3/3+2x^5/(1-x^2)<=(4967/2475)x. Thus log(A/B)<=4967/7227<11/16. The existing finite exponential upper bound at order four proves exp(11/16)<199/100.

For the remaining block, B/D is a product of 3p adjacent ratios. Each factor is at least 1+c_i, where c_i=(3p+2i+1)/(3p^2), 0<=c_i<=3/5, and the sum of the c_i is exactly six. The existing inequality 2c/(c+2)<=log(1+c) gives a lower bound (10/13)c term by term. Hence log(B/D)>=60/13. The existing finite exponential lower bound with eleven terms proves exp(60/13)>100. All constants are checked by exact rational arithmetic in the proof.

Finally take the unique threshold from actual_odd_wrap_single_crossing. The strict positive endpoint at t=p forces that threshold to be at most p, since every admissible smaller t before the threshold has negative difference. For t>p the already proved strict-positive suffix applies; the endpoint covers t=p itself. The proof uses finite sums and products together with established logarithm and exponential inequalities, and requires no limiting approximation.

Together with actual_early_odd_wrap_sign, this bounds the unique threshold by floor((2p+1)/3)<T<=p for every odd p>=5. At the threshold the comparison is nonnegative, so it cannot lie in the earlier strict negative cone 3t<=2p+1. The upper endpoint is included: these results do not imply T<p. For p=3 the original unique-threshold theorem remains applicable, while this sharper upper bound is not asserted.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyOddWrapPositiveCone.actual_positive_odd_wrap_cone`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyOddWrapSingleCrossing](BajnokBeattyOddWrapSingleCrossing.md)
