# Actual History Transfer and Signed Coefficient Extraction

## Abstract

Actual History Transfer and Signed Coefficient Extraction

**Definition 1.1 (edgeTilt).**

$$\forall M,k:Nat, \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall x,y:\operatorname{Vertex}(M), \operatorname{edgeTilt}(m, zp, zm, x, y)=\operatorname{markedFactors}(m, zp, zm, x, y)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.edgeTilt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor is the product over all marked rows j of zplus(j) when the departure is inl(m(j)) and the destination parity is 1, and zminus(j) when that departure has destination parity -1; each other factor is 1.

**Definition 1.2 (sparse).**

$$\forall M,k:Nat, \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall a:\operatorname{Fin}(k)\to Complex, \forall x:\operatorname{Vertex}(M), \operatorname{sparse}(m, a, x)=\operatorname{markedSum}(m, a, x)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.sparse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

markedSum is the finite sum of a(j) over indices for which x = inl(m(j)); all other summands are zero. This definition allows repeated marks.

**Theorem 1.3 (count monomial).**

$$\forall M,k,s:Nat, \forall e:\operatorname{Experiment}(), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall o:\operatorname{Obs}(M, s, e), \operatorname{countMonomial}(e, m, zp, zm, o)=\operatorname{edgeProduct}(e, m, zp, zm, o)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.count_monomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

countMonomial is the product over j of zplus(j)^count(e,o,m(j),1) times zminus(j)^count(e,o,m(j),-1). edgeProduct is the product over the s edges of edgeTilt at their ordered endpoints. Natural powers include zero tilts and zero counts.

**Theorem 1.4 (edgeTilt eq affine).**

$$\forall M,k:Nat, \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {\operatorname{injective}(m)} \Rightarrow \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall x,y:\operatorname{Vertex}(M), \operatorname{edgeTilt}(m, zp, zm, x, y)=\operatorname{affineTilt}(m, zp, zm, x, y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.edgeTilt_eq_affine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With u(j) = (zplus(j)+zminus(j))/2-1 and v(j) = (zplus(j)-zminus(j))/2, affineTilt equals 1+sparse(m,u,x)+sparse(m,v,x) chi(y). Distinct marks make at most one departure row active.

**Theorem 1.5 (sparse sum).**

$$\forall M,k:Nat, \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall f:\operatorname{Vertex}(M)\to Complex, \forall a:\operatorname{Fin}(k)\to Complex, \operatorname{stateSparseSum}(f, m, a)=\operatorname{markedWeightedSum}(f, m, a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.sparse_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left side is the sum over all x of f(x) sparse(m,a,x); the right side is the sum over all j of f(inl(m(j))) a(j). No injectivity condition is needed.

**Definition 1.6 (endpointWeight).**

$$\forall X:Type, [\operatorname{Fintype}(X)] \forall c:Complex, \forall K:X\to X\to Complex, \forall n:Nat, \forall y:X, \operatorname{endpointWeight}(c, K, n, y)=\operatorname{endingHistorySum}(c, K, n, y)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpointWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite state type X, endpointWeight(c,K,n,y) is c times the sum over all functions o : Fin(n+1) -> X ending at y of the product of K on the n consecutive ordered edges.

**Theorem 1.7 (endpoint zero).**

$$\forall X:Type, [\operatorname{Fintype}(X)] \forall c:Complex, \forall K:X\to X\to Complex, \forall y:X, \operatorname{endpointWeight}(c, K, 0, y)=c$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpoint_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A length-zero path has mass c at each endpoint, including when c is zero.

**Theorem 1.8 (endpoint next).**

$$\forall X:Type, [\operatorname{Fintype}(X)] \forall c:Complex, \forall K:X\to X\to Complex, \forall n:Nat, \forall y:X, \operatorname{endpointWeight}(c, K, n+1, y)=\operatorname{endpointConvolution}(c, K, n, y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpoint_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

endpointConvolution is the sum over x of endpointWeight(c,K,n,x) K(x,y). Appending the final state is a bijection of complete histories.

**Theorem 1.9 (endpoint total).**

$$\forall X:Type, [\operatorname{Fintype}(X)] \forall c:Complex, \forall K:X\to X\to Complex, \forall n:Nat, \operatorname{endpointSum}(c, K, n)=\operatorname{historySum}(c, K, n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpoint_total` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

endpointSum sums endpointWeight over all final states. historySum is c times the sum of the edge-product weights of every complete length-n history.

**Theorem 1.10 (tilt norms).**

$$\forall k:Nat, \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall R:Real, {\operatorname{tiltRadius}(zp, zm, R)} \Rightarrow \forall j:\operatorname{Fin}(k), \operatorname{norm}(\frac{\operatorname{eval}(zp, j)+\operatorname{eval}(zm, j)}{2}-1)\leq R+1 \land \operatorname{norm}(\frac{\operatorname{eval}(zp, j)-\operatorname{eval}(zm, j)}{2})\leq R$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.tilt_norms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

tiltRadius means both coordinate vectors have norms at most R at every index. The symmetric tilt has norm at most R+1 and the antisymmetric tilt has norm at most R.

**Theorem 1.11 (marked sum norm).**

$$\forall k:Nat, \forall D:Real, \forall a:\operatorname{Fin}(k)\to Complex, {(k=1 \lor k=2) \land 0\leq D \land \operatorname{coordinateBound}(a, D)} \Rightarrow \operatorname{norm}(\operatorname{sum}(a))\leq (2) \cdot (D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.marked_sum_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

coordinateBound means norm(a(j)) <= D for every j. One or two rows cost at most 2D in the sum norm.

**Theorem 1.12 (profile sum zero).**

$$\forall M,q:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1} \Rightarrow \operatorname{profileSum}(r, S)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.profile_sum_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

profileSum is the sum over all 2M native states of b(r,S,x). This is the zero-mean compensated profile of the finite stochastic model.

**Definition 1.13 (Symmetric tilt).**

$$\forall k:Nat, \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall j:\operatorname{Fin}(k), \operatorname{tiltU}(zp, zm, j)=\frac{\operatorname{eval}(zp, j)+\operatorname{eval}(zm, j)}{2}-1$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.tiltU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each marked positive departure state has two arbitrary complex tilt coordinates, one for each destination parity. The symmetric coordinate is their half-sum minus one.

**Definition 1.14 (Antisymmetric tilt).**

$$\forall k:Nat, \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall j:\operatorname{Fin}(k), \operatorname{tiltV}(zp, zm, j)=\frac{\operatorname{eval}(zp, j)-\operatorname{eval}(zm, j)}{2}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.tiltV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The antisymmetric coordinate is half the difference of the positive and negative destination tilts.

**Definition 1.15 (Total-mass drift).**

$$\forall M,q,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{driftA}(r, S, m, zp, zm)=\frac{\sum_{j:\operatorname{Fin}(k)} (\operatorname{tiltU}(zp, zm, j)+(\operatorname{b}(r, S, \operatorname{inl}(\operatorname{eval}(m, j)))) \cdot (\operatorname{tiltV}(zp, zm, j)))}{(2) \cdot (M)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.driftA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The drift A averages u_j + b_j v_j over the 2M states. Here b_j is the native compensated profile at the marked positive state: b is r on positive support states, -c on the positive complement, and zero on negative states; c = rq/(M-q). Marks may lie in the support or its complement.

**Definition 1.16 (Endpoint-parity drift).**

$$\forall M,q,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{driftB}(r, S, m, zp, zm)=\frac{\sum_{j:\operatorname{Fin}(k)} (\operatorname{tiltV}(zp, zm, j)+(\operatorname{b}(r, S, \operatorname{inl}(\operatorname{eval}(m, j)))) \cdot (\operatorname{tiltU}(zp, zm, j)))}{(2) \cdot (M)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.driftB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The drift B averages v_j + b_j u_j over the same state space. The compensating profile has zero total mass and vanishes on negative states.

**Definition 1.17 (Actual count generating function).**

$$\forall M,q,k,T:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{actualPGF}(r, S, m, zp, zm, T)=\sum_{o:\operatorname{Obs}(M, T, \operatorname{path}())} (\operatorname{probability}(r, \operatorname{path}(), S, o)) \cdot (\prod_{j:\operatorname{Fin}(k)} ({\operatorname{eval}(zp, j)}^{\operatorname{count}(\operatorname{path}(), o, \operatorname{eval}(m, j), 1)}) \cdot ({\operatorname{eval}(zm, j)}^{\operatorname{count}(\operatorname{path}(), o, \operatorname{eval}(m, j), -1)}))$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.actualPGF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum ranges over all complete histories of T transitions, with the native uniform-start path mass. The positive and negative exponents count departures from each marked state followed by the corresponding destination parity. These counts share one history. A history is a function from Fin(T+1) to Fin(M) + Fin(M). Its mass w_T is (2M)^(-1) times the product of (1 + b(x) chi(y))/(2M) over its T edges, where chi is 1 on positive states and -1 on negative states. C_j^+ and C_j^- count edges whose departure is the positive state m(j) and whose destination chi is respectively 1 and -1. The symbol z denotes the pair (z^+, z^-). Natural powers include zero tilt coordinates and use the convention zero to the zeroth power equals one.

**Definition 1.18 (Forward endpoint state).**

$$\forall A,B:Complex, \operatorname{forwardState}(A, B, 0)=\operatorname{vector}(1, 0) \land \forall t:Nat, \operatorname{forwardState}(A, B, t+1)=\operatorname{rowTransfer}(\operatorname{forwardState}(A, B, t), \operatorname{forwardMatrix}(A, B))$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.forwardState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row-coordinate state begins at (1,0). At each step its first coordinate becomes (1+A)x+A y and its second becomes B x+B y. The coordinates are the total and parity coefficients of the actual tilted endpoint density.

**Definition 1.19 (Forward transfer matrix).**

$$\forall A,B:Complex, \operatorname{forwardMatrix}(A, B)=\operatorname{matrix}(1+A, B, A, B)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.forwardMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entries, listed in row order, are 1+A, B, A, B. At zero drift this is the projection onto the first coordinate.

**Theorem 1.20 (Actual path transfer identity).**

$$\forall M,q,T,k:Nat, \forall r:Real, 1\leq q<M \land 0<r<1 \land \operatorname{compensation}(M, q, r)<1 \Rightarrow \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \operatorname{injective}(m) \Rightarrow \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{actualPGF}(r, S, m, zp, zm, T)=\operatorname{first}(\operatorname{forwardState}(\operatorname{driftA}(r, S, m, zp, zm), \operatorname{driftB}(r, S, m, zp, zm), T)) \land \operatorname{actualPGF}(r, S, m, zp, zm, T)=\operatorname{entry}({\operatorname{forwardMatrix}(\operatorname{driftA}(r, S, m, zp, zm), \operatorname{driftB}(r, S, m, zp, zm))}^{T}, 0, 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.actual_marked_path_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural T, including zero, and every complex tilt, actualPGF equals both the first coordinate of forwardState and the (0,0) entry of the T-th power of forwardMatrix. A and B are the compensated drifts of the same fixed support and marked rows. The proof sums actual complete-history weights through their endpoint density. No bound on the tilts and no restriction to one or two rows is required for this exact identity.

**Theorem 1.21 (finite count poisson relative).**

$$\forall Omega:Type, [\operatorname{Fintype}(Omega)] \forall k:Nat, \forall kappa,Czero,L,epsilon:Real, \forall w:Omega\to Real, \forall cp,cm:Omega\to \operatorname{Fin}(k)\to Nat, \forall muplus,muminus:\operatorname{Fin}(k)\to Real, \forall np,nm:\operatorname{Fin}(k)\to Nat, {0<kappa \land 1\leq Czero \land 1\leq L \land 0\leq epsilon \land (k=1 \lor k=2) \land \operatorname{positiveMeanLowerBounds}(kappa, L, muplus, muminus) \land \operatorname{coordinateCountBound}(np, nm, Czero, L) \land \forall zp,zm:\operatorname{Fin}(k)\to Complex, {\operatorname{tiltRadius}(zp, zm, \frac{(2) \cdot (Czero+1)}{kappa})} \Rightarrow \operatorname{norm}(\operatorname{countPGF}(w, cp, cm, zp, zm)-\operatorname{poissonPGF}(muplus, muminus, zp, zm))\leq (epsilon) \cdot (\operatorname{signedPoissonScale}(muplus, muminus, zp, zm))} \Rightarrow \lvert \frac{\operatorname{P}(w, cp, cm, np, nm)}{\operatorname{Q}(muplus, muminus, np, nm)}-1 \rvert\leq (((epsilon) \cdot ({(\operatorname{exp}(2)) \cdot (\operatorname{sqrt}((2) \cdot (pi))+1)}^{4})) \cdot ({Czero+1}^{2})) \cdot ({L}^{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.finite_count_poisson_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Omega is an arbitrary finite history carrier. w is an arbitrary real weight; nonnegativity is not required. cp and cm are natural count vectors. positiveMeanLowerBounds means that each muplus(j) and muminus(j) is positive and at least kappa L/2. coordinateCountBound means every prescribed coordinate is at most Czero L. tiltRadius bounds both complex tilt vectors coordinatewise. countPGF is the weighted sum of the count monomials; poissonPGF is exp(sum_j(muplus(j)(zp(j)-1)+muminus(j)(zm(j)-1))). signedPoissonScale is exp of the real part of that same exponent. P sums w over the simultaneous exact-count event. Q is the product over both signs and all j of exp(-mu) mu^n/n!. The displayed constant uses pi, the circle constant. The proof extracts coefficients on a product torus at positive radii (n+1)/mu, then applies the factorial estimate including n=0. It permits zero tilts and rare original point masses.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.actualPGF`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.actual_marked_path_transfer`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.count_monomial`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.driftA`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.driftB`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.edgeTilt`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.edgeTilt_eq_affine`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpointWeight`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpoint_next`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpoint_total`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.endpoint_zero`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.finite_count_poisson_relative`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.forwardMatrix`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.forwardState`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.marked_sum_norm`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.profile_sum_zero`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.sparse`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.sparse_sum`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.tiltU`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.tiltV`
- Truth anchor: `D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient.tilt_norms`
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint](../../Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.md)
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes](../SequentialDecisionRisk/FiniteSupportSelectionBayes.md)
