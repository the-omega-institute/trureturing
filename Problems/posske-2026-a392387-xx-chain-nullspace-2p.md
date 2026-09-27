---
slug: posske-2026-a392387-xx-chain-nullspace-2p
bibkey: posske2026a392387
doi: null
url: https://oeis.org/A392387
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/XXChainNullspaceCount.result
---

# The nullspace of the periodic XX chain on twice a prime number of sites

## Problem

OEIS A392387 (Thore Posske, 2026) is the nullspace dimension of the periodic
spin-1/2 XX Heisenberg chain on `n > 1` sites. Its COMMENTS give the count

> Also, the number of subsets K of {1,...,n} such that the sum of cosines of
> the angles in {(2j + (1 + (-1)^|K|)/2 )*Pi/n | j in K} is zero.

and its FORMULA section records

> Conjecture: a(2*p) = 2*(6^((p-1)/2)+1) for odd prime p.

Issue #10063 fixes the readings: the formal object is this subset count, the
combinatorial description common to the entry and to Hu, Gerken and Posske
(arXiv:2602.15098, appendix on the XX model); its identification with the
dimension of the zero-energy subspace is the source's Jordan–Wigner reading and
is not formalized; the empty set is counted; `p` ranges over odd primes and
`n = 2p`.

## Motivation

The appendix of arXiv:2602.15098 rephrases the nullspace degeneracy of the XX
chain as the number of choices of distinct momenta with vanishing total energy
and calls the counting of such vanishing sums of roots of unity "an unsolved
mathematical problem". The frozen declaration
`D5/S3/Quantum/SpinChains/XXChainNullspaceCount.result` settles it for chains
of `2p` sites: the zero-energy subspace has dimension `2(6^((p−1)/2) + 1)` for
every odd prime `p`, two states from odd fermion number and `2·6^((p−1)/2)`
from even fermion number.

## Gap

Issue #10063 preregisters the conjecture and its literature check. The entry
(revision 52, 2026-02-20) lists this formula as a conjecture next to the proved
characterization `a(p) = 2` exactly for primes `p`; the source paper gives only
a brute-force table for `n ≤ 22`; MathDB returns no entry for "A392387", and
the repository had no declaration or dossier for it. These readings are
`not-found-in-searched-scope`; they do not establish an exhaustive worldwide
literature search or priority.

## Route

Write `p = 2m + 1`. A subset `K ⊆ {1, …, 2p}` is determined by its class-state
function on the residues `r` modulo `p`: which of the two elements of
`{1, …, 2p}` congruent to `r`, one even and one odd, lie in `K`. Let `z(r)` be
the number of taken even elements minus the number of taken odd elements of
the class `r`, `η` the primitive `p`-th root of unity with `−η = e^{iπ/p}`, and
`ω = e^{iπ/(2p)}`. The cosine sum of `K` is the real part of
`Z = Σ_r z(r) η^r` when `|K|` is odd and of `ωZ` when `|K|` is even.

The only rational linear relation among `1, η, …, η^{p−1}` is that their sum
vanishes, because the cyclotomic polynomial `Φ_p` is the minimal polynomial of
`η`. Hence `Re Z = 0` exactly when `z(r) + z(−r) = 2z(0)` for all `r`, and
`Re(ωZ) = 0` exactly when `z(−r) − z(r − 1) = z(0) − z(−1)` for all `r`; since
`r ↦ −1 − r` fixes `m`, the latter is the symmetry `z(r) = z(−1 − r)`.

For odd `|K|` the first relation forces `z` to be constantly `1` or constantly
`−1` (if `z(0) = 0`, then `z` is odd and `|K|` is even): the even elements and
the odd elements of `{1, …, 2p}`, two subsets. For even `|K|`, count the
symmetric class-state functions over the fundamental domain `0, …, m − 1` of
`r ↦ −1 − r`: each of the `m` pairs of classes has `6` states with equal `z`,
and the parity of `|K|` forces the fixed class `m` to be empty or full, `2`
states. The total is `2 + 2·6^m`.

## Falsifier

A zero-sum subset outside the two classes above, or a missing one, would change
the count; the equivalences with the relations on `z` exclude both. A rational
relation among `1, η, …, η^{p−2}` would break the characterization; the degree
`p − 1` of `Φ_p` excludes it. A proof that `a(2p)` differs from
`2(6^((p−1)/2) + 1)` for some odd prime would contradict the kernel-checked
theorem.

## Evidence

Enumeration of all subsets with floating-point cosine sums (zero test
`|Σ| < 10⁻⁹`, no sums in `[10⁻⁹, 10⁻⁶)`) reproduces the entry's DATA for
`n = 2, …, 20` and gives `a(6) = 14`, `a(10) = 74`, `a(14) = 434` and
`a(22) = 15554`, each split as `2` odd-size and `2·6^m` even-size subsets.

The canonical source is
`D5/S3/Quantum/SpinChains/XXChainNullspaceCount.lean`. Its public declarations
are `nullspaceCount`, `claim`, and `result`. The frozen module state has
statement identity
`sha256:8c612fc929792c7b8f53472c4bed5c5bdc4eae4a24cc913ae117958da5dd1565`.
The result declaration has statement identity
`sha256:4cfdd0cdb4dbd00412e214229b820c9258ec4566b5cbbcdfa7bd735919c308f0`.
The Freeze event is
`sha256:edc55918d549053a26fe09fcdf107c9d474ea4d8635eedd6f73c86c299c9ba90`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `proved` for the quoted conjecture. The public theorem
has `proof_shape: content`; its local steps characterize the zero-sum subsets
by the relations on `z` and count them through an explicit bijection with
pairs of class states over a fundamental domain. `admission_basis:
open-problem-resolution` under preregistration issue #10063. There is no atom
and no digestion coverage edge. The result is a uniform theorem for every odd
prime, not a bounded enumeration, checker, numeric reduction or certified
instance, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The identification of the subset count with the dimension of the zero-energy
subspace of the XX chain is the source's Jordan–Wigner reading; the
Hamiltonian, the transformation and the fermion-parity-dependent momentum
quantization are not formalized. The bounded literature check does not
establish exhaustive worldwide novelty, priority, or the absence of an
independent proof.
