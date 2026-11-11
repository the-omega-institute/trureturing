# Quantitative finite circle cover

## Abstract

A finite block of a circle rotation meets every open interval of the specified length when the explicit small-denominator obstructions are absent.

This document records the finite-window theorem and its exact hypotheses. The source keeps the bounded integer block and explicit finite obstruction family. All occurrences of natural or integer variables inside real expressions use the canonical real casts. The ceiling is the integer ceiling Int.ceil, so H = ceil(4/w) is an integer. No irrationality hypothesis is imposed.

**Theorem 1.1 (The fully quantified finite window theorem).**

$$\forall theta \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall w \in \mathbb{R},\; \forall N \in \mathbb{N},\; (0 < w) \Rightarrow ((\frac{4}{w} \le N) \Rightarrow ((\forall h \in \mathbb{Z},\; \forall a \in \mathbb{Z},\; (1 \le h) \Rightarrow ((h \le \operatorname{ceil}\left(\frac{4}{w}\right)) \Rightarrow (\frac{1}{N} < \left|h \cdot theta - a\right|))) \Rightarrow (\exists b \in \mathbb{N},\; (N \le b) \land ((b \le 2 \cdot N) \land (\exists ell \in \mathbb{Z},\; (t < b \cdot theta - ell) \land (b \cdot theta - ell < t + w))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/QuantitativeFiniteCircleCover.quantitative_finite_circle_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use Real.exists_rat_abs_sub_le_and_den_le with n=N. It supplies a reduced rational r=p/q, 1<=q<=N, and |theta-r|<=1/((N+1)q). Multiplication by q gives |q theta-p|<=1/(N+1)<=1/N. The stated obstruction hypothesis therefore excludes q<=H, so q>H>=4/w. No upper bound on w is used.

For x=t+w/2-N theta, put j=round(qx). Rat.reduced and Int.isCoprime_iff_nat_coprime give integers u,v with up+vq=1. Take k=(uj mod q).toNat, d=(uj)/q using Euclidean integer division, and ell=-(vj+pd). Then 0<=k<q and kp-ell q=j. Hence |kp/q-ell-x|<=1/(2q). The proof constructs both k and ell; it does not replace the finite window by qualitative density.

Since k<q, perturbing the rational grid costs at most k|theta-r|<=1/(N+1)<=1/N. The total error is at most 1/(2q)+1/N < w/8+w/4=3w/8<w/2. Setting b=N+k yields N<=b< N+q<=2N and t<b theta-ell<t+w, including rational theta.

Research attribution: the completed Pro input non-dyadic-actual-price-power-followup.answer.txt, finite-circle lemma (28), gives this reduced-denominator grid argument. Its intended actual application is theta=alpha_3/alpha_2, N_e=floor(kappa*zeta*Tbar_e^(nu-sigma)*Lbar_e^2), w_e=zeta*taubar_(sigma,e)/64, and H_e=ceil(4/w_e). The covering lemma applies only after its budget and finite nonresonance premises have been established for those actual parameters. The original all-B/all-record/RH power-scale goal remains open.

## References

- Truth anchor: `D5/S3/Arith/QuantitativeFiniteCircleCover.quantitative_finite_circle_cover`
