# Exact preparation and uniform separation at a reflected graph port

## Abstract

Four-vertex port preparation

**Definition 1.1 (Raw port).**

$$b={}(1, 0, 0, 0)^{T}$$

*Formalization.* `D5/S3/Observer/Linear/FourVertexPortPulses.port` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actuator injects at vertex zero of the labelled graph.

**Definition 1.2 (Centered target).**

$$x=\frac{1}{\sqrt{14}}{}(-3, 0, 1, 2)^{T}$$

*Formalization.* `D5/S3/Observer/Linear/FourVertexPortPulses.target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target has unit Euclidean norm and zero total mass.

**Definition 1.3 (Reflection).**

$$U=I-\frac{1}{3}vv^{T}$$

*Formalization.* `D5/S3/Observer/Linear/FourVertexPortPulses.reflection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The hidden direction is v=(0,1,−2,1) in vertex order. The reflection fixes the port and the target.

**Definition 1.4 (Labelled graph pair).**

$$\forall M,\gamma,q: \mathbb{R}, L(M, \gamma, q, false)=\frac{M}{8}P+E(\gamma)+\frac{q}{2\sqrt{3}}(vh^{T}+hv^{T}) \land L(M, \gamma, q, true)=UL(M, \gamma, q, false)U^{T}$$

*Formalization.* `D5/S3/Observer/Linear/FourVertexPortPulses.laplacian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let P project off the constant vector. The vector h is (0,−1,0,1) in vertex order. The signed star E adds the rank-one edge Laplacian for edge (0,i) with coefficient gamma times v_i divided by two. The false label gives the uniform generator (M/8)P plus E and the hidden coupling. The true label gives its conjugate by the reflection.

**Definition 1.5 (Raw signed endpoint).**

$$\forall L:\mathbb{R}^{4\times4}, S:Finset(\mathbb{R}), w:\mathbb{R} \to \mathbb{R}, endpoint(L, S, w)=\sum_{t\in S}w(t) \exp(-tL) b$$

*Formalization.* `D5/S3/Observer/Linear/FourVertexPortPulses.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here L is a four by four real matrix and S is a finite set of real ages.

**Theorem 1.6 (Four distinct raw ages are necessary and sufficient).**

$$\begin{gathered}\forall M,\gamma,q: \mathbb{R}, 0<M\land 0<\gamma\le\frac{M}{256}\land 0<q\le\frac{\gamma^{2}}{M} \longrightarrow \\{}(\forall r:Bool,PosSemidef(L(M, \gamma, q, r))\land (\forall i,\sum_{j}L(M, \gamma, q, r)(i, j)=0)\land (\forall i,j,i\neq j\Rightarrow 0<-L(M, \gamma, q, r)(i, j)))\land \\{}(\forall r:Bool,S:Finset(\mathbb{R}),w:\mathbb{R} \to \mathbb{R},endpoint(L(M, \gamma, q, r), S, w)=x\Rightarrow 4\le\lvert S\rvert\land \sum_{t\in S}w(t)=0)\land \\{}(\forall S:Finset(\mathbb{R}),\lvert S\rvert=4\Rightarrow \exists w:\mathbb{R} \to \mathbb{R},\sum_{t\in S}w(t)=0\land (\forall r:Bool,endpoint(L(M, \gamma, q, r), S, w)=x))\land \\{}(\forall T:\mathbb{R},0<T\Rightarrow \exists S:Finset(\mathbb{R}),w:\mathbb{R} \to \mathbb{R},\lvert S\rvert=4\land (\forall t\in S,0<t\land t\le T)\land \sum_{t\in S}w(t)=0\land (\forall r:Bool,endpoint(L(M, \gamma, q, r), S, w)=x))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FourVertexPortPulses.exact_four_ages` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two matrices are positive semidefinite, have zero row sums, and give strictly positive conductances at every pair of distinct vertices. The same signed recipe works on the two labelled graphs because the reflection fixes both the input port and the target.

The determinant equation for the centered Jacobi block gives one root in each of the intervals (−2 gamma,−gamma), (0,gamma/2) and (gamma,2 gamma). After shifting by M/8 the three roots give positive rates with nonzero port coordinates. Dividing the corresponding target coordinates by the port coordinates gives signs negative, positive, negative in increasing order of rate.

The scalar pulse response vanishes at rate zero by mass conservation. The three centered values give two further distinct zeros by continuity. The exponential zero bound prohibits this response with fewer than four distinct ages, including when age zero or arbitrary real pulse weights are allowed.

At any four distinct ages the exponential interpolation system is invertible by the same zero bound. Prescribing the zero mass mode and the three centered ratios gives the exact endpoint. Ages T/4, T/2, 3T/4 and T provide one choice in every positive horizon.

`D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound`

**Theorem 1.7 (At most three ages leave a uniform positive distance).**

$$\begin{gathered}\forall M,\gamma,q: \mathbb{R}, 0<M\land 0<\gamma\le\frac{M}{256}\land 0<q\le\frac{\gamma^{2}}{M} \longrightarrow \\{}\exists \varepsilon: \mathbb{R},0<\varepsilon\land (\forall r:Bool,S:Finset(\mathbb{R}),w:\mathbb{R} \to \mathbb{R}, \\{}\lvert S\rvert\le3\Rightarrow (\sum_{t\in S}w(t)=0\lor (\forall t\in S,0\le t))\Rightarrow \varepsilon\le maxnorm(endpoint(L(M, \gamma, q, r), S, w)-x))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/FourVertexPortPulses.three_age_uniform_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same positive radius applies to both graph labels, every finite design with at most three distinct ages, and arbitrary real weights at nonnegative ages. For zero total input the ages may be any real numbers. The norm is the largest absolute error over the four physical vertices.

Normalize each spectral row by its port coordinate and compose the rows for the reflected label with the reflection. The constant row reads total input and the other three read the exponential response at the positive rates. Let C be one plus the sum of the absolute entries of both normalized row matrices. An admissible radius is the smallest absolute target coordinate among the three positive rates divided by 2C.

Inside that radius the row-sum estimate controls all four coordinate errors. Subtract the conserved mass from one existing weight. At a nonnegative age the resulting change at each positive rate is bounded in absolute value by that mass error. With zero total input the correction vanishes. The corrected response has a zero at rate zero and keeps the three strict target signs. Two further distinct zeros violate the exponential zero bound.

`D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound`

## References

- Truth anchor: `D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound`
- Truth anchor: `D5/S3/Observer/Linear/FourVertexPortPulses.endpoint`
- Truth anchor: `D5/S3/Observer/Linear/FourVertexPortPulses.exact_four_ages`
- Truth anchor: `D5/S3/Observer/Linear/FourVertexPortPulses.laplacian`
- Truth anchor: `D5/S3/Observer/Linear/FourVertexPortPulses.port`
- Truth anchor: `D5/S3/Observer/Linear/FourVertexPortPulses.reflection`
- Truth anchor: `D5/S3/Observer/Linear/FourVertexPortPulses.target`
- Truth anchor: `D5/S3/Observer/Linear/FourVertexPortPulses.three_age_uniform_distance`
- Dependency: [D5/S3/Analytic/ExponentialSum/DescartesRule](../../Analytic/ExponentialSum/DescartesRule.md)
