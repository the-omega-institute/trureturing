---
bibkey: amiriarrazola2016hiddenmatching
authors: Ryan Amiri and Juan Miguel Arrazola
year: 2016
title: Quantum money with nearly optimal error tolerance
doi: 10.1103/PhysRevA.95.062334
url: https://arxiv.org/abs/1610.06345v1
claim: Equation (21) conjectures mean two-marginal cloning fidelity at most one half plus 1/n for the uniform hidden-matching sign ensemble in positive even dimension.
strata_touched:
  - D5/S3/Quantum/QuantumChannels/AmiriArrazolaHiddenMatchingCloningBound
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.95.062334

Source: https://arxiv.org/abs/1610.06345v1

## Source statement

Ryan Amiri and Juan Miguel Arrazola, *Quantum money with nearly optimal error tolerance*,
arXiv:1610.06345v1. Equation (21) is on PDF page 8, and its conjecture sentence is on page 9:

> which we have verified numerically for n ≤ 14 and we conjecture holds for any n.
> From now on, we simply assume that n ≤ 14.

The displayed assertion is $\overline F \le \frac12+\frac1n$.

Equation (4), PDF page 3:

> In hidden matching QRGs the set of possible inputs is the set of all n-bit strings,
> each chosen with equal probability, where n is an even number. Alice encodes her
> input into the n-dimensional pure state

$$
|\phi_x\rangle=\frac1{\sqrt n}\sum_{i=1}^n(-1)^{x_i}|i\rangle.
$$

Section II A 2, PDF page 6:

> In reference to Fig. 4, we refer to these states as the white states, and start by considering a single such state, φ_{xⁱ} := |φ_{xⁱ}⟩⟨φ_{xⁱ}|, contained in the coin.

> For simplicity, we drop the superscript on the n-bit strings xⁱ in all that follows.

Equation (11), PDF page 7:

> We want to find the channel that maximises

$$
\overline F=\frac1{2^n}\sum_x
\frac{\langle\phi_x|\eta_x|\phi_x\rangle+
\langle\phi_x|\tau_x|\phi_x\rangle}{2},
$$

> where η_x = Tr_Z[Ψ(|φ_x⟩⟨φ_x|)] and τ_x = Tr_Y[Ψ(|φ_x⟩⟨φ_x|)].

## Scope

The repository theorem proves this upper bound for every even n ≥ 2 and every
completely positive trace-preserving complex linear map into two n-dimensional factors.
The coordinates Fin n relabel 1 through n; all Fin n → Fin 2 inputs occur once.
There is no covariance or exchange-symmetry assumption on the channel.
The journal version's agreement with arXiv v1 and exhaustive novelty are
ASSUMED-UNVERIFIED.

## Exact experiment

The finite exact checks are in the-omega-institute/trureturing-experiments,
commit d59d32e482c8839c620c1f23b91c322619ab257c,
`docs/reports/amiri-arrazola-hidden-matching-cloning/`.
The recorded command is `python3 check.py`, exit 0, with final line `ALL_CHECKS_OK`.
The script SHA-256 is c39d61cdd8a5343f016ddbd3302d3667b44c9f717b818039538f91a1f5881303.
These checks concern finite dimensions and support no additional uniform sharpness claim.
