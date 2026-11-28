---
slug: tamura-yamagami-2026-hadamard-sojourn-rigidity
bibkey: tamurayamagami2026sojourn
doi: 10.48550/arXiv.2609.05033
url: https://arxiv.org/abs/2609.05033v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Walks/HadamardSojournRigidity.exactUniform_rigidity
---

# Hadamard sojourn rigidity in the direction basis

## Problem

Tamura and Yamagami, *Hadamard Rigidity of Positive Sojourn Time Distributions for Rotation Coins*, Section 5:

> As a future problem, it is natural to extend the result to general unitary coins with two internal states.

Section 5 also asks how variation of the initial state affects exact uniformity and discusses global phase, diagonal unitary transformations, and changes of basis. [arXiv v1](https://arxiv.org/html/2609.05033v1#S5).

## Motivation

Theorem 3.1 treats a real rotation coin with the single initial vector `(1,i)/√2`. It characterizes the Hadamard angle by exact uniformity at time eight, equivalently at every time `4m` with `m ≥ 2`. For a general coin, the operational question is which entry moduli in the walk's direction basis give the uniform law and whether the test depends on the initial state.

## Gap

Issue #35030 fixes the direction basis and asks for a classification for all complex unitary coins and all unit initial vectors, including `m = 1` in the all-time condition. Konno's Theorem 3.2 and the amplitude expansion preceding Corollary 3.3 supply the prior Hadamard coefficients. Their scalar Gram matrices already imply initial-state independence for the standard Hadamard coin. The general-coin necessity for each initial vector is the rigidity gap. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/35030) · [Konno](https://arxiv.org/abs/1102.5587).

## Route

Factor the coin as `D R E` with diagonal unitaries `D` and `E` and real coin `R = [[c,s],[s,−c]]` with `c,s ≥ 0` and `c²+s² = 1`. Each return word has equally many left and right steps. At fixed length its product acquires a common unit phase and transforms by multiplication with `Eᴴ` on the left and `E` on the right. Thus each squared weight for the original coin on `φ` equals the corresponding real-coin weight on `Eφ`.

If `G_k` is the length-eight return amplitude for `R`, then `G₂ᴴG₂ + G₆ᴴG₆ − 2G₄ᴴG₄ = 2c⁴s⁶(c²−s²)²(c²+s²)I₂`. Exact uniformity requires a positive count-four weight, which rules out `c = 0` and `s = 0`. Equality of the three weights then gives `c = s` for every unit input. For sufficiency, the Catalan generating series gives the balanced return coefficient `(−1)^m Cat(m−1)/4^m` times `[[1,1],[−1,1]]` at each supported count and zero elsewhere. Its Gram matrix gives identical positive weights for every unit input.

## Falsifier

A unitary coin and a unit initial vector for which a stated equivalence fails would refute the classification. The uniformity predicate requires a positive total weight, ordinary real normalization, mass `1/(2m−1)` on the even counts `2,4,…,4m−2`, and zero at every other natural count. Degenerate coins are within the quantified domain.

## Evidence

`D5/S3/Quantum/Walks/HadamardSojournRigidity.exactUniform_rigidity` proves that time-eight exact uniformity is equivalent to every entry having modulus `1/√2`, and that balance is equivalent to exact uniformity at every time `4m` with `m ≥ 1`. The public statement uses the ordered products of row-projected steps and the positive-interval rule in the paper's Section 2. The Reg mirror observes the four entry moduli.

## Triage

Tier 1 source question. The fixed-basis statement of #35030 is proved. Its decisive new implication is the necessity for all unit inputs obtained from the time-eight matrix identity and phase transport.

### What the settlement shows

- **Proved** by `D5/S3/Quantum/Walks/HadamardSojournRigidity.exactUniform_rigidity`. A time-eight uniform law for any one unit initial state forces the same coin to give uniform laws at every positive multiple of four for every unit initial state. This extends the characterization in Theorem 3.1 to all unitary two-state coins with the stated direction projectors.
- **Open in this dossier.** Section 5's broader discussion of changes of basis goes beyond the fixed-projector result. Transporting the projectors with the basis preserves the walk conventions. Conjugating the coin alone while keeping the projectors fixed can change entry moduli and thus time-eight uniformity.

## ASSUMED-UNVERIFIED

The title and repository searches establish a bounded literature reading. Global priority remains unverified.
