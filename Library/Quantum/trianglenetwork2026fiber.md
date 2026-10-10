---
bibkey: trianglenetwork2026fiber
title: "Triangle-network source independence and fiber geometry"
authors:
  - trureturing contributors
year: 2026
type: theory-interface
status: working-note
---

# Triangle-network source independence and fiber geometry

This note records the typed bridge between the classical triangle-local carrier and the Auric FIB readout geometry.

## Core objects

The classical source law is a product over the three edges:

\[
\mu_{\alpha\beta\gamma}
=
\mu_\alpha\otimes\mu_\beta\otimes\mu_\gamma,
\]

while the response kernels are two-edge local:

\[
A(a|\beta,\gamma),\quad
B(b|\gamma,\alpha),\quad
C(c|\alpha,\beta).
\]

The observed law is their multilinear contraction. The source product condition is a hidden-layer condition. It is not the same as conditional independence of two visible features.

The five-mode FIB law has coordinates

\[
(X,Y,Z,\kappa)
=
(\mathbb E x,\mathbb E y,\mathbb E z,\mathbb E[xy])
\]

with \((X,Y,Z)\) as the pyramid quotient and \(\kappa\) as the joint-coupling fiber. The exact reconstruction is

\[
p_{25}=\kappa,\quad
p_2=X-\kappa,\quad
p_5=Y-\kappa,\quad
p_3=Z,\quad
p_0=1-X-Y-Z+\kappa.
\]

The conditional-independence surface is \((1-Z)\kappa=XY\). This is a local feature relation, not the three-source product law.

## Main conclusion

The appropriate common object is a fibered incidence geometry:

\[
\text{three-edge product source}
\to
\text{two-edge response}
\to
\text{three-coordinate quotient}
\]

with information lost into \(\kappa\), higher moments, or an inflation lift. A triangle-local nonlocality proof is a failed global lift, even when all retained low-order projections are individually legal.

## Literature status

- Fritz embeds CHSH into the triangle with two classical input-bit sources and one entangled source.
- Renou et al. (2019) prove the four-output \(P_u\) family non-trilocal for \(u_{\max}^2<u^2<1\), with \(u_{\max}^2\approx0.785\). Their reasonable physical noise threshold was open.
- Pozas-Kerstjens, Gisin, and Renou (2023) prove separated parameter intervals for continuous RGB4 families by inflation.
- Gitton and Renner (2025) prove the exact noiseless EJM distribution non-classical with symmetry-reduced inflation and an exact integer certificate. Their purified affine visibility proxy has \(3/7\le v_*<383/512\), with the EJM point at \(v=3/4\). This proxy is not the independent-source Werner path.
- Boreiri, Ulu, Brunner, and Sekatski (2025) give rigorous sufficient noisy regions for a specified TBSM family: roughly \(0.544\%\) independent source white noise, roughly \(80\%\) dephasing, and a total-variation nonlocal ball of roughly \(0.24\%\). These are certificate regions, not exact transitions and not automatically the RGB4 maximally-entangled point.

## Repository anchor

The finite predicate IsTriangleLocal is already present in D5/S3/Quantum/Entanglement/TriangleSymmetricLocalRefutation.lean. It formalizes the triple integral over independent uniform edge variables and two-edge response functions. TriangleInequalityL1Refutation.lean reuses it to refute a proposed inequality using an explicit local model. These modules establish the classical source-product layer. They do not formalize EJM, Fritz, Renou noise, inflation certificates, or physical quantum source noise.

The companion theory document is

docs/develop/theory/TRIANGLE_NETWORK_SOURCE_INDEPENDENCE_AND_FIBER_GEOMETRY.md

and gives the finite fiber identities, the global-gluing interpretation, typed noise models, exact certificate visibility formula, and a finite Lean roadmap. No new Lean theorem is claimed by this note.
