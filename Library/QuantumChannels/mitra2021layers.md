---
bibkey: mitra2021layers
authors: A. Mitra
year: 2021
title: "Layers of classicality in the compatibility of measurements"
doi: 10.1103/PhysRevA.104.022206
url: https://arxiv.org/abs/2101.05752v4
claim: "Section III.A asks whether the channels broadcasting an observable have a highest element or a lowest element under precomposition by nondisturbing channels."
strata_touched:
  - D5/S3/Quantum/Measurements/BroadcastingChannelExtremaRefutation
license: citation-only
triage: anchor
---

# Mitra, layers of classicality

A. Mitra, *Layers of classicality in the compatibility of measurements*,
Phys. Rev. A **104**, 022206 (2021).

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.104.022206

Source: https://arxiv.org/abs/2101.05752v4

The page numbers below are the printed page numbers of the arXiv v4 PDF.

## Broadcasting channels and observables

Section II.B, p. 2: “A CPTP map Θ : S(Hin) → S(Hout) is called a quantum
channel, where Hin and Hout are two Hilbert spaces [15].”

Definition 1, p. 2: “A channel Λ : S(H) → S(H_A ⊗ H_B) with H_A = H_B = H
is called a broadcasting channel.”

Definition 3, p. 3: “An observable A ∈ O_X^d is broadcast by a broadcasting
channel Λ ∈ C_broad^d if for all ρ ∈ S(H), x ∈ X” followed by equation (5):

$$
\operatorname{Tr}[\rho A(x)]
=\operatorname{Tr}[\Lambda(\rho)A(x)\otimes I]
=\operatorname{Tr}[\Lambda(\rho)I\otimes A(x)].
$$

## Nondisturbing channels and the precomposition order

Definition 8, p. 5: “A channel Θ : S(H) → S(H) is nondisturbing with respect
to an observable A if for all ρ ∈ S(H),” followed by equation (22):

$$
\operatorname{Tr}[\rho A(x)]=\operatorname{Tr}[\Theta(\rho)A(x)]
\quad\forall x\in\Omega_A.
$$

Its equivalent Heisenberg form is equation (23), Θ*(A(x)) = A(x).
The order uses Λ′ = Λ ∘ Θ with Θ nondisturbing for A. Proposition 4 states
that this precomposition preserves broadcasting of A.

## The two Section III.A questions

Section III.A, p. 5, following Proposition 4:

> For an observable, in this way, one can get the set of different broadcasting channels that broadcast the observable. It is an open question whether this set has the highest element i.e., a broadcasting channel in this set from which all other broadcasting channels that can broadcast the observable, can be constructed through concatenation with nondisturbing channels. It is also an open question whether this set has the lowest element i.e., a broadcasting channel in this set which can be constructed from all other broadcasting channels that broadcast the observable through concatenation with nondisturbing channels.

The Conclusions, p. 9, repeat: “Firstly, it is not known whether the set of all
broadcasting channels that broadcast a particular observable has the greatest
or the lowest element.”

## Finite-matrix encoding

The input carrier is `Fin d`, the output carrier is `Fin d × Fin d`, and outcomes
are `Fin m`. Observables use the frozen `IsPOVM` predicate. States use the
frozen `IsDensity` predicate. Channels use finite Kraus operators with
completeness Σ KᴴK = I and the frozen `MatrixMap.of_kraus K K` action.
The universal assertion says that every observable with a nonempty broadcasting
set has a highest or a lowest element. Its refutation supplies one observable
for which both answers are negative.

## Refutation and scope

For d = 3 and m = 2, take P = diag(1,1,0), Q = I − P,
A₀ = (3/4)P + (1/4)Q and A₁ = I − A₀. Three channels prepare the mutually
orthogonal matrix units at (0,0), (1,1) and (0,1) on the P sector, and the matrix
unit at (2,2) on the Q sector. Nondisturbing precomposition fixes these channels.
Two different fixed channels exclude a lowest element. A common upper bound
would distinguish three orthogonal outputs from states supported in the
two-dimensional P sector; the positive trace bounds give 3 ≤ 2.

The Lean result concerns this instance. The rank-r family, sharp observables,
and the qubit extremum questions remain open here.
