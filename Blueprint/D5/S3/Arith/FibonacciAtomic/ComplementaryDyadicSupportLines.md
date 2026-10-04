# Complementary Dyadic Cost Laws

## Abstract

An exact dyadic law refutes a proposed support bound on every complementary simplex; a strict high-side affine transformation preserves the tail series up to scale.

**Definition 1.1 (The two-mass vector).**

$$(\forall a: \mathbb{N}, (\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), ((\operatorname{val}\left(i\right) < (2^{(a - 1)} + 1) \Rightarrow \operatorname{eval}\left(\operatorname{pstar}\left(a\right), i\right) = \frac{1}{2^{a}}) \land (\neg(\operatorname{val}\left(i\right) < (2^{(a - 1)} + 1)) \Rightarrow \operatorname{eval}\left(\operatorname{pstar}\left(a\right), i\right) = \frac{(2^{a} - 2)}{\left(2^{a}\right)^{2}}))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.counterexampleLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write B=2^a and m=B+1. On labels with value less than 2^(a-1)+1, pstar(a) has mass 1/B; on the remaining labels it has mass (B-2)/B^2. The subtraction in the natural exponent is truncated at zero. For a>=3 the multiplicities are B/2+1 and B/2. The residual R and cost L are reused from Dyadic Cost Support Lines: R(p,d)=2^d-sum_i floor(2^d p(i)) and L(p)=sum_d R(p,d)/2^d. The real tsum has its usual Lean convention outside the summable domain.

**Theorem 1.2 (A counterexample for every exponent).**

$$(\forall a: \mathbb{N}, (3 \le a \Rightarrow (((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 \le \operatorname{eval}\left(\operatorname{pstar}\left(a\right), i\right)) \land \sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{eval}\left(\operatorname{pstar}\left(a\right), i\right) = 1) \land (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(\operatorname{pstar}\left(a\right), d\right)}{2^{d}}\right) \land (\operatorname{min}\left(\operatorname{pstar}\left(a\right)\right) = \frac{(2^{a} - 2)}{\left(2^{a}\right)^{2}} \land (\operatorname{L}\left(\operatorname{pstar}\left(a\right)\right) = \frac{(a + 1) \cdot (2^{a} - 1)}{2^{a}} \land ((2^{a} \cdot (a + 2) \cdot \operatorname{min}\left(\operatorname{pstar}\left(a\right)\right) - \operatorname{L}\left(\operatorname{pstar}\left(a\right)\right)) = \frac{((2^{a} - a) - 3)}{2^{a}} \land (0 < \frac{((2^{a} - a) - 3)}{2^{a}} \land \neg((\forall P: \operatorname{Fin}\left((2^{a} + 1)\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 \le \operatorname{eval}\left(P, i\right)) \land \sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{eval}\left(P, i\right) = 1) \Rightarrow 2^{a} \cdot (a + 2) \cdot \operatorname{min}\left(P\right) \le \operatorname{L}\left(P\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.complementary_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural a>=3, the vector is nonnegative and has total mass one. Its smallest coordinate is (B-2)/B^2, its series converges, and its cost is (a+1)(B-1)/B. With A=B(a+2), the gap A min(pstar)-L(pstar)=(B-a-3)/B is strictly positive. Consequently the universal inequality L(p)>=A min(p) on this real simplex is false.

At depths d<a every floor is zero. At depths a+j with j<a the large-atom floor is 2^j and the small-atom floor is 2^j-1, including j=a-1. Thus R(pstar,a+j)=B/2-2^j, and all residuals from depth 2a-1 onward vanish. The resulting finite geometric sum gives the exact cost. The inequality 2^a>a+3 holds for the whole range a>=3.

This refutes the universal bound on m=2^a+1 stated in Whitebox section 70.1. The Mersenne bounds in section 67.10 concern m=2^h-1 and have different coefficients, so the conclusions are compatible.

**Definition 1.3 (The strict high-side transformation).**

$$(\forall a: \mathbb{N}, (\forall p: \operatorname{Fin}\left((2^{a} + 1)\right) \to \mathbb{R}, (\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), \operatorname{eval}\left(\operatorname{T}\left(a, p\right), i\right) = (\left(2^{a}\right)^{2} \cdot \operatorname{eval}\left(p, i\right) - (2^{a} - 1)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.highSideMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T_a(p)(i)=B^2 p(i)-(B-1) is an affine map on all real vectors. Its probability-law and cost identities below require the strict condition min(p)>t0=(B-1)/B^2. The notation iterate(T_a,k,p) means T_a applied k times to p.

**Theorem 1.4 (Scaling, finite exit, and the fixed point).**

$$(\forall a: \mathbb{N}, (3 \le a \Rightarrow (\forall p: \operatorname{Fin}\left((2^{a} + 1)\right) \to \mathbb{R}, ((((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 \le \operatorname{eval}\left(p, i\right)) \land \sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{eval}\left(p, i\right) = 1) \land \frac{(2^{a} - 1)}{\left(2^{a}\right)^{2}} < \operatorname{min}\left(p\right)) \Rightarrow (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(p, d\right)}{2^{d}}\right) \land ((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 < \operatorname{eval}\left(\operatorname{T}\left(a, p\right), i\right)) \land (\sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{eval}\left(\operatorname{T}\left(a, p\right), i\right) = 1 \land (\operatorname{min}\left(\operatorname{T}\left(a, p\right)\right) = (\left(2^{a}\right)^{2} \cdot \operatorname{min}\left(p\right) - (2^{a} - 1)) \land (\operatorname{Summable}\left(d: \mathbb{N} \mapsto \frac{\operatorname{R}\left(\operatorname{T}\left(a, p\right), d\right)}{2^{d}}\right) \land (\operatorname{L}\left(p\right) = ((((a + 2) - \frac{a}{2^{a}}) - \frac{2}{\left(2^{a}\right)^{2}}) + \frac{\operatorname{L}\left(\operatorname{T}\left(a, p\right)\right)}{\left(2^{a}\right)^{2}}) \land (((\operatorname{L}\left(p\right) - (2^{a} \cdot (a + 2) + 2 \cdot \left(2^{a}\right)^{2}) \cdot \operatorname{min}\left(p\right)) + 2 \cdot (2^{a} - 1)) = \frac{((\operatorname{L}\left(\operatorname{T}\left(a, p\right)\right) - (2^{a} \cdot (a + 2) + 2 \cdot \left(2^{a}\right)^{2}) \cdot \operatorname{min}\left(\operatorname{T}\left(a, p\right)\right)) + 2 \cdot (2^{a} - 1))}{\left(2^{a}\right)^{2}} \land ((\neg((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), \operatorname{eval}\left(p, i\right) = \frac{1}{(2^{a} + 1)})) \Rightarrow \exists k: \mathbb{N}, ((\forall j: \mathbb{N}, (j < k \Rightarrow \frac{(2^{a} - 1)}{\left(2^{a}\right)^{2}} < \operatorname{min}\left(\operatorname{iterate}\left(\operatorname{T}\left(a\right), j, p\right)\right))) \land ((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 < \operatorname{eval}\left(\operatorname{iterate}\left(\operatorname{T}\left(a\right), k, p\right), i\right)) \land (\sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{eval}\left(\operatorname{iterate}\left(\operatorname{T}\left(a\right), k, p\right), i\right) = 1 \land (0 < \operatorname{min}\left(\operatorname{iterate}\left(\operatorname{T}\left(a\right), k, p\right)\right) \land \operatorname{min}\left(\operatorname{iterate}\left(\operatorname{T}\left(a\right), k, p\right)\right) \le \frac{(2^{a} - 1)}{\left(2^{a}\right)^{2}}))))) \land ((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), \operatorname{eval}\left(p, i\right) = \frac{1}{(2^{a} + 1)}) \Rightarrow (\operatorname{T}\left(a, p\right) = p \land \operatorname{L}\left(p\right) = \frac{(2^{a} \cdot (a + 2) + 2)}{(2^{a} + 1)}))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.complementary_high_side_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a>=3 and p be any nonnegative real vector of total mass one with t=min(p)>t0. Put q=T_a(p), s=min(q), H0=a+2-a/B-2/B^2, C=B(a+2)+2B^2 and d0=2(B-1). Then q is strictly positive with total mass one, s=B^2 t-(B-1), both cost series converge, L(p)=H0+L(q)/B^2, and L(p)-Ct+d0=(L(q)-Cs+d0)/B^2.

Every coordinate of p lies strictly between t0 and 1/B. Floors before depth a are zero; at depth a+j with j<a, every floor is 2^j-1. Their prefix contribution is H0. At depth 2a+e the floor equals (B-1)2^e+floor(2^e q(i)), hence R(p,2a+e)=R(q,e). Splitting the convergent series establishes the scaling identities.

For a nonuniform p there is a finite k such that all earlier iterates remain above t0, the kth iterate is still a strictly positive probability law, and its minimum lies in (0,t0]. Its minimum is 1/(B+1)-(B^2)^j(1/(B+1)-t) at step j. Exponential growth and t<1/(B+1) give finite exit. The uniform vector is a fixed point and has cost (B(a+2)+2)/(B+1). Neither the boundary-jump statement 70.41 nor the second-support statement 70.42 is asserted here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.complementary_counterexample`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.complementary_high_side_scaling`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.counterexampleLaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.highSideMap`
- Dependency: [D5/S3/Arith/FibonacciAtomic/DyadicSupportLines](DyadicSupportLines.md)
