# Return-Distance Subshifts and Exact-Length QFT

## Abstract

The actual compact two-sided binary return-distance subshift and its ordinary finite-word language.

The alphabet is the two-element subtype of the natural numbers {0,1}, with the inherited discrete metric. Configurations have all integer coordinates. ReturnLegal(D,x) requires the difference q-p to belong to D for every consecutive pair of one coordinates. Finite supports obey the same return-distance restriction; singleton supports and the all-zero configuration are always legal. The set is closed because the assertion that fixed p,q are consecutive ones is a finite clopen cylinder condition. All integer shifts preserve the rule. The bundled object is Mathlib FullShift.Subshift; ReturnPoint is its carrier subtype. Mathlib PiCountable.metricSpace supplies a metric with the product uniformity, and closedness in the compact finite-alphabet product gives compactness.

**Theorem 1.1 (A closed condition on the actual product).**

$$\begin{aligned}\forall D: \operatorname{Set}(\mathbb{Z}),\\\operatorname{IsClosed}(\operatorname{carrier}(\operatorname{returnDistanceSubshift}(D)))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ReturnDistanceSubshift.return_legal_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every forbidden consecutive-pair condition depends only on the finite integer interval between its endpoints. The complement of each such cylinder is closed, and the legal set is their intersection.

ReturnWordOccurs(w,x,t) means x(t+j)=w[j] for every j smaller than the length of w. ReturnLanguage(D,w) means that w occurs at some integer coordinate of an actual ReturnPoint(D), with no bound or one-sided restriction on that point. ReturnQuasiFiniteType(D) is the original Definition 3.5: one M works for every n at least M and every pair of language words u,v; if there is a language word w of length exactly n with uw and wv in the language, there is a language word z of length exactly n with uzv in the language. This definition does not use a bounded-length replacement or another quasi-finite-type convention.

**Theorem 1.2 (Long forbidden intervals rule out exact-length QFT).**

$$\begin{aligned}\forall D: \operatorname{Set}(\mathbb{Z}),\\(\forall n: \mathbb{N},\exists H: \mathbb{N},\forall d: \mathbb{N},H < d \Rightarrow d \le H+n+1 \Rightarrow \neg (\operatorname{int}(d) \in D)) \Rightarrow \\\neg \operatorname{ReturnQuasiFiniteType}(D)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/ReturnDistanceSubshift.forbidden_intervals_not_quasi_finite_type` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a proposed threshold M choose n=max(M,1) and an interval (H,H+n+1] containing no allowed return. Take u to be one followed by H zeros, w to be n zeros, and v to be one. Singleton-support configurations prove actual occurrence of u,v,w,uw,wv. In any putative occurrence of uzv with length(z)=n, the terminal v guarantees a next one after the initial one. The least positive return lies strictly above H and at most H+n+1. Its consecutive-pair legality contradicts the forbidden interval. The first-return argument uses the least natural positive index, preserving all intervening coordinates.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/ReturnDistanceSubshift.forbidden_intervals_not_quasi_finite_type`
- Truth anchor: `D5/S1/Dynamics/Shadowing/ReturnDistanceSubshift.return_legal_closed`
- Dependency: [D5/S1/Dynamics/Shadowing/ReturnDistanceSupport](ReturnDistanceSupport.md)
