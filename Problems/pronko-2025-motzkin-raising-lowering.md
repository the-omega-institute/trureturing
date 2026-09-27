---
slug: pronko-2025-motzkin-raising-lowering
bibkey: pronko2025motzkin
doi: 10.48550/arXiv.2504.00835
url: https://arxiv.org/abs/2504.00835v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.result
---

# Pronko's raising and lowering operators of the periodic Motzkin chain

## Problem

Pronko (arXiv:2504.00835v3, Nucl. Phys. B 1017 (2025) 116963) studies the
periodic Motzkin spin-1 chain
`H^periodic = Σ_{i=1}^{N-1} Π_{i,i+1} + Π_{N,1}` with `Π = U + D + F` and
conjectures:

> There exist raising and lowering operators satisfying \eqref{Sigmavec} and
> \eqref{SpmH}, and they are given by
> $\Sigma^\pm=\sum_{r_1,\dots,r_N\in\{-2,-1,0,1,2\},\ r_1+\dots+r_N=\pm 1} s_1^{r_1}\cdots s_N^{r_N}$

where \eqref{Sigmavec} asks `Σ^± v_{S^z} = c_±(S^z) v_{S^z ± 1}` with
`c_±(S^z) ≠ 0` for `S^z ≠ ±N` and `Σ^± v_{±N} = 0`, and \eqref{SpmH} asks
`[Σ^±, H^periodic] = 0`. Issue #10569 fixes the readings: the ground state
`v_m` is the sum of the basis words of height `m` (`u`, `f`, `d` count
`+1`, `0`, `−1`), as in Conjecture 1; `Π_{i,j}` acts with its first factor
on site `i`; `N ≥ 2`.

## Motivation

The paper verifies the conjecture symbolically up to `N = 6`.
`D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.result` proves it for
every `N ≥ 2`.

## Gap

Issue #10569 preregisters the proof route and the literature check. Pronko's
later Fredkin paper (arXiv:2507.18291) remarks that its methods can be
generalized but gives no proof of the Motzkin case; Sengoku and Watanabe
(arXiv:2608.17548) prove Conjecture 1 of the paper and still refer to the
raising and lowering operators as conjectural. The repository has only the
Fredkin-chain modules `PronkoFredkin*`. `not-found-in-searched-scope`.

## Route

1. An ordered product of operators acting on distinct sites has as entries
   the products of the local entries.
2. The entry of `s^r` at `x, y` is `1` when `ht(x) = ht(y) + r` and `0`
   otherwise, so for basis words `a, b` exactly one exponent vector,
   `r_i = ht(a_i) − ht(b_i)`, contributes, and `Σ^±` has entry `1` at `a, b`
   when `S(a) = S(b) ± 1` and `0` otherwise:
   `Σ^± = Σ_m |v_{m±1}⟩⟨v_m|`.
3. Each of `U`, `D`, `F` pairs two basis states with the same height sum
   with opposite signs, so every row of `Π` sums to zero over each height
   class; every two-site term, and `H`, annihilate each `v_m`, and `H` is
   symmetric. Hence `H Σ^± = 0 = Σ^± H`.
4. `Σ^± v_m = T_{N,m} v_{m±1}`, with `T_{N,m}` the number of words of height
   `m`, positive for `|m| ≤ N`, and `v_{±(N+1)} = 0`.

## Falsifier

The proof would fail if some exponent vector other than `ht(a) − ht(b)`
contributed to an entry of `Σ^±`, or if a row of `Π` had a nonzero sum over
a height class.

## Evidence

Exact matrix computation for `N = 2, …, 5` (issue #10569): `[Σ^±, H] = 0`,
the null space of `H` has dimension `2N + 1`, and the entries of `Σ^+` are
`[S^z(a) = S^z(b) + 1]`; dropping the `±2` terms gives a nonzero commutator.

The canonical source is
`D5/S3/Quantum/Dynamics/PronkoMotzkinRaisingLowering.lean`.
Its public declarations are `ht`, `sp`, `sm`, `spow`, `rv`, `site`, `Sig`,
`S`, `ket`, `proj`, `piProj`, `twoSite`, `H`, `v`, `claim`, and `result`. The
frozen module state has statement identity
`sha256:c376d2c300355670fac5c5751bfba47f5613e77b2e8fc1059867856fad0f729a`.
The result declaration has statement identity
`sha256:83942de874ef383fa798b4b9150d6b274df6ea5c03773ddd67248accc8ad2161`.
The Freeze event is
`sha256:be8d599ec2b4b590da0355282109ec7bb1098eea82ebc3a0ae0d5e30c3d72d1a`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #10569 before the
probe. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the entry formula of step 2 and the annihilation of
step 3 are new propositions on the live proof path. Its admission basis is
`open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The equivalent residue form of `Σ^±` (eq. `Sigmapm`) is the same sum by the
definition of the coefficient of `λ^{-1}` and is not stated separately. The
bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
