---
bibkey: davison2009dalembertmonoids
authors: Thomas M. K. Davison
year: 2009
title: "D'Alembert's functional equation on topological monoids"
doi: 10.5486/PMD.2009.4440
url: https://publi.math.unideb.hu/paper/1385
claim: "A continuous f on a topological group G with f(e)=1 and f(xy)+f(xy^-1)=2f(x)f(y) is (1/2)tr of a continuous homomorphism G -> SL2(C)."
strata_touched: []
license: citation-only
triage: anchor
---

# Continuous d'Alembert functions on topological groups

Publ. Math. Debrecen 75 (2009), no. 1-2, 41-66. The main theorem is stated
for a topological monoid $M$ with neutral element $e$: a continuous
$f\colon M\to\mathbb C$ with $f(e)=1$ satisfying

$$
f(xyz)+f(xzy)=2f(x)f(yz)+2f(y)f(zx)+2f(z)f(xy)-4f(x)f(y)f(z)
$$

has the form $f=\tfrac12\operatorname{tr}\circ h$ for a continuous homomorphism
$h\colon M\to\mathrm{Mat}_2(\mathbb C)$. The consequence used here: if $G$ is a
topological group and $f\colon G\to\mathbb C$ is continuous with $f(e)=1$ and

$$
f(xy)+f(xy^{-1})=2f(x)f(y)\qquad(x,y\in G),
$$

then $f=\tfrac12\operatorname{tr}\circ h$ for a continuous homomorphism
$h\colon G\to\mathrm{SL}_2(\mathbb C)$. Any solution that is not identically zero
has $f(e)=1$ (put $y=e$).

## Bearing on the round-trip comparison law

For a comparison $\kappa(x,y)=\varphi(x^{-1}y)$ on a group, the correlation
$\psi=2\varphi-1$ satisfies the two-variable equation above in the unit-quaternion
model $\psi(g)=\operatorname{Re}g$. The round-trip law
$\kappa(w,[x,w,x])=(2\kappa(w,x)-1)^2$ is only its diagonal case
$\psi(a^2)=2\psi(a)^2-1$. If the two-variable equation is taken as an axiom, the
classification of continuous solutions is this theorem together with the compact
case in [davison2008dalembert](davison2008dalembert.md); that route claims nothing
new. The diagonal case alone admits further solutions: on $\mathrm{SO}(3)$ the
function $\psi=\cos\alpha$ ($\alpha$ the rotation angle) is continuous, equals $1$
only at the identity and satisfies $\psi(a^2)=2\psi(a)^2-1$, but for the rotations
$a,b$ by $\pi/2$ about two orthogonal axes,
$\psi(ab)+\psi(ab^{-1})=-1\neq0=2\psi(a)\psi(b)$. The derivation of the full
equation from the diagonal case under the further comparison hypotheses is the
subject of [issue #31739](https://github.com/the-omega-institute/trureturing/issues/31739).

[Publisher record](https://publi.math.unideb.hu/paper/1385)
