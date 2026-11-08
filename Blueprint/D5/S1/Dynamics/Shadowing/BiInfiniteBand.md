# Bi-infinite Scalar Transition Bands

## Abstract

Local scalar barriers and positive progress force a finite consecutive transition band over all integer times.

Let x map the integers to the reals, and let a, b and eta be real numbers. Define B={k : a<x(k)<b}. The predicate ScalarBandProgress(x,a,b,eta) consists of four local conditions: the lower cap is backward invariant; the upper cap is forward invariant; a lower-cap value cannot jump directly to the upper cap; and every middle value advances by at least eta. Explicitly, for every integer k these conditions are:

$\begin{aligned}\forall k\in \mathbb{Z}, x(k+1)\le a\Rightarrow x(k)\le a\\\forall k\in \mathbb{Z}, b\le x(k)\Rightarrow b\le x(k+1)\\\forall k\in \mathbb{Z}, x(k)\le a\Rightarrow x(k+1)<b\\\forall k\in \mathbb{Z}, a<x(k)\land x(k)<b\Rightarrow x(k)+eta\le x(k+1)\end{aligned}$

**Theorem 1.1 (Finite band and the two cap alternatives).**

$$\begin{aligned}x:\mathbb{Z}\to \mathbb{R}, a,b,eta\in \mathbb{R}, N\in \mathbb{N},\\ScalarBandProgress(x,a,b,eta)\land 0<eta\land b-a<Neta\Rightarrow\\B finite\land\\((\forall k\in \mathbb{Z}, x(k)\le a)\lor (\forall k\in \mathbb{Z}, b\le x(k))\lor\\(\exists l,r\in \mathbb{Z},l\le r\land r-l<N\land\\B=[l,r]\land\\(\forall k\in \mathbb{Z}, k<l\Rightarrow x(k)\le a)\land (\forall k\in \mathbb{Z}, r<k\Rightarrow b\le x(k))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/BiInfiniteBand.classify` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here [l,r] denotes the integer interval. Between two markers, the backward lower barrier and forward upper barrier force every intervening time to remain marked. Induction then gives x(i+n)>=x(i)+n eta throughout a marked block. Two marked endpoints differ in value by less than b-a, so their time difference is less than N. Fixing one marker bounds all markers in a finite integer interval; its minimum and maximum give the exact block and the two cap tails. If there is no marker, the no-jump condition propagates the lower cap forward as well as backward, so the entire sequence lies in one cap. The statement makes no boundedness assumption on x outside the band and no assumption that the errors or transitions have finite support.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/BiInfiniteBand.classify`
