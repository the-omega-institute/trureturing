---
bibkey: schnaubelt2026datko
authors: Roland Schnaubelt
year: 2026
title: Evolution Equations, Lemma 4.4
doi: null
url: https://iana.math.kit.edu/downloads/iana3/schnaubelt/Skripten/evgl-skript.pdf
claim: Finite Lp orbit norms for every vector of a real or complex Banach C0 semigroup imply uniform exponential stability.
strata_touched:
  - D5/S3/Quantum/Analysis/DatkoStability
license: citation-only
triage: anchor
---

# Datko orbit integrability and exponential stability

Schnaubelt's lecture notes *Evolution Equations*, version March 19, 2026,
Lemma 4.4, printed pages 95-96, treat real or complex scalars and
1 <= p < infinity. The proof constructs the bounded truncated orbit maps
x maps to the Lp class of the indicator of [0,n] times T(t)x. Individual
finite orbit norms make this family pointwise bounded; uniform boundedness
gives one constant for all finite-window energy estimates. The semigroup
law then gives decay of operator norms, and Proposition 4.2 gives
exponential stability. The notes' general convention excludes the zero
Banach space. The formal contraction-semigroup statement also includes
that degenerate case, without using a nonzero vector or norm(identity)=1.

For contractions and p=2, the same finite-window estimate immediately
gives T*norm(S(T)x)^2 <= C*norm(x)^2. Choosing tau=4*C+1 gives
norm(S(tau)) <= 1/2. Natural-time iteration and the floor of t/tau give
M=2 and omega=log(2)/tau at every nonnegative time. Conversely the squared
exponential envelope is integrable on the positive half-line. These are
classical implications; no literature priority is claimed.

Trinh Viet Duoc, *Extending a theorem of Datko for evolutionary families*,
arXiv:2009.04178v1, page 1, recalls the squared-energy equivalence with
an initial-time-uniform bound depending on x. For a semigroup,
U(t,s)=T(t-s), time translation reduces that condition to one positive-time
orbit energy for each x.

The formal proof reuses the existing real contraction-semigroup carrier,
Mathlib's Banach-Steinhaus theorem, general normed-target L2 criteria and
real exponential integrability. It introduces no Hilbert, dimension,
separability, compactness, spectrum, generator-domain or common-energy
hypothesis. The result gives no energy estimate for an individual heat
semigroup and asserts no uniform gap from merely individual positive rates.

## Verified locator

https://iana.math.kit.edu/downloads/iana3/schnaubelt/Skripten/evgl-skript.pdf

https://arxiv.org/pdf/2009.04178v1
