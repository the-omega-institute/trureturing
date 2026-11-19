# Original reciprocal endpoint exposure

## Abstract

One-sided pure endpoint comparison exposes the original endpoint.

Let V be an arbitrary finite dimensional real normed space, C its original closed pointed generating convex cone, and u an original linear functional strictly positive on every nonzero element of C. The original normalized base is K={x in C:u(x)=1}; P is all of ext(K). An original proper effect is a linear f satisfying 0<=f<=u on every cone vector. The original comparison T_p(y) is the infimum of f(y) over ALL proper f with f(p)=1. Every linear functional is continuous in finite dimension, so the continuous-dual representation used in the proof preserves this entire effect domain.

**Theorem 1.1 (A single endpoint and its complete original fibres).**

$$\forall V \in Type,\; [\operatorname{NormedAddCommGroup}\left(V\right)][\operatorname{NormedSpace}\left(\mathbb{R}, V\right)][\operatorname{FiniteDimensional}\left(\mathbb{R}, V\right)]\forall C \in \operatorname{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \left(\operatorname{IsClosed}\left(C\right) \land \left(\left(\forall x \in V,\; \left(x\in C \land x\neq 0\right) \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right) \land \operatorname{span}\left(\mathbb{R}, C\right) = \operatorname{top}\left(\operatorname{Submodule}\left(\mathbb{R}, V\right)\right)\right)\right) \Rightarrow \left(\forall p \in \operatorname{pure}\left(C, u\right),\; \left(\forall x \in \operatorname{pure}\left(C, u\right),\; \operatorname{comparison}\left(C, u, p, x\right) \le \operatorname{comparison}\left(C, u, x, p\right)\right) \Rightarrow \left(\exists h \in \operatorname{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \operatorname{proper}\left(C, u, h\right) \land \left(\left\{y \mid y \in \operatorname{base}\left(C, u\right) \land \operatorname{apply}\left(h, y\right) = 0\right\} = \left\{p\right\} \land \left(\operatorname{confirms}\left(C, u, p, u - h\right) \land \left(\left\{y \mid y \in \operatorname{base}\left(C, u\right) \land \operatorname{apply}\left(u - h, y\right) = 1\right\} = \left\{p\right\} \land \operatorname{IsExposed}\left(\mathbb{R}, \operatorname{base}\left(C, u\right), \left\{p\right\}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/ReciprocalEndpointExposure.reciprocal_endpoint_exposure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any original pure p and assume only T_p(x)<=T_x(p) for every original pure x. There is one actual original proper linear h whose zero fibre in the WHOLE K is {p}. Its actual proper complement u-h confirms p and has value-one fibre {p}; that singleton is an exposed subset of the original K. No exclusion-ball, weak-pair, global reciprocity, least-effect, spectrality or compact-pure-set premise is used. The theorem also covers a singleton K and dimension one. Existence of the normalized point already rules out a zero carrier, so an extra nontriviality hypothesis is unnecessary.

Use the original ContinuousFrameSum.effects_compact theorem, whose hypotheses are only strict positivity and generation. Intersect the entire original effect interval with evaluation zero at p to obtain the compact convex set G. It contains zero. Choose h in its intrinsic interior, which is its interior relative to its affine span. Since zero belongs to G, that affine span is its linear span. A relative ball at h and a uniform norm bound on G provide a>0 with h-a g in G for every g in G. Thus g<=c h on the whole cone with c=1/a. Taking g=u-f for every original confirmer f of p and using the original infimum gives 1-c h(y)<=T_p(y) on all K. This is uniform scalar domination, without asserting that c h is proper or that a least confirmer exists. A zero span or zero h causes no division by a norm or by max(h).

Suppose the zero fibre Z contains y different from p. A linear functional ell separates y and p. Let alpha=max_Z ell>ell(p), and A=max_K ell-min_K ell. For t=n+1 choose an extreme point x_n of the exposed maximum face of ell-t h. Exposed-face extreme-point transfer makes x_n an ORIGINAL pure point. Maximality gives t h(x_n)<=ell(x_n)-alpha and 0<=h(x_n)<=A/t. Let m=max_K(ell-t h), b=min_K(ell-t h), and d=m-b. Since ell is nonconstant on Z, d>0. Construct the actual original linear effect e=((ell-t h)-b u)/d. Original cone_bound proves 0<=e<=u on the entire cone; e(x_n)=1. The one-sided premise at x_n and the original infimum bound imply 1-c h(x_n)<=e(p). The identities d(1-e(p))=m-ell(p) and d<=A+t yield 0<alpha-ell(p)<=c(A h(x_n)+ell(x_n)-alpha).

Compactness of K supplies a convergent subsequence x_n tending to v in K. The A/t bound gives h(v)=0, so v belongs to Z. Maximality gives ell(x_n)>=alpha, while the definition of alpha gives ell(v)<=alpha. Hence ell(v)=alpha, and the last positive lower bound tends to zero, a contradiction. The limit v need not be pure; the proof uses neither closedness of P nor continuity in the first comparison argument. Thus the entire zero fibre is {p}. On K, u=1 identifies the complement's entire value-one fibre with this zero fibre. The same complement is a continuous linear exposing functional. When K is a singleton, the contradiction branch is empty and the construction remains valid, including G={0}.

This proves the complete Theorem 114.3 of Quantum Origin IX, through its original estimate IX114.12. The displayed equation IX114.3 belongs to a different statement. Under PR, apply this theorem directly at each p, using the corresponding equality as the one-sided inequality. This gives exposedness of every original pure point without introducing another mathematical declaration. Relative-interior existence, compact subsequence extraction, exposed-face transfer and finite-dimensional dual separation are pinned library tools; the uniform original zero-effect domination and the penalized comparison contradiction are the live new derivation. No literature priority or physical realization is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/ReciprocalEndpointExposure.reciprocal_endpoint_exposure`
- Dependency: [D5/S3/Quantum/Foundation/ContinuousFrameSum](ContinuousFrameSum.md)
