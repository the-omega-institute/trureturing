---
slug: borda-kuhlmann-rincon-2026-dicke-clifford-product-obstruction
bibkey: bordakuhlmannrincon2026magic
doi: 10.48550/arXiv.2607.18400
url: https://arxiv.org/abs/2607.18400v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/DickeCliffordProductObstruction.result
---

# Nontrivial Dicke states cannot become total products under Clifford gates

## Problem

A. Borda Kuhlmann and J. Rincón, *Magic-protected entanglement and
Clifford-irreducible structure in magic state space*, arXiv:2607.18400v1,
Appendix F.2, Remark F.1 (printed page 16), state:

> (Dicke states and the fundamental property of W-magic). Let |ψ⟩ = |D^n_k⟩
> be a nontrivial Dicke state, with 0 < k < n and n > 2, and let C ∈ C_n be
> an arbitrary n-qubit Clifford gate. Then, for any total product state
> |ϕ_1⟩ ⊗ · · · ⊗ |ϕ_n⟩, C|ψ⟩ ≠ ⊗_{j=1}^{n}|ϕ_j⟩.
> That is, nontrivial Dicke states are expected to exhibit the fundamental
> property of W-magic in Definition V.1.

The same subsection says: “Although we do not provide a general proof,
previous Clifford-orbit computations and our numerical searches indicate
that no Clifford operation maps nontrivial Dicke states to total product
states.” Definition A.1 specifies the normalizer of the Pauli group in
SU(2^n), with scalar phases 1, −1, i and −i.

The formal claim quantifies every natural n and k with 2 < n and 0 < k < n,
every such special-unitary normalizer, and arbitrary normalized local complex
qubit amplitudes, including all local phases. Dicke amplitudes are
1/√(n.choose k) on the Hamming-weight-k layer. Total products have amplitude
∏j ϕ_j(x_j). The conclusion compares complete complex vectors.

## Motivation

The frozen declaration
`D5/S3/Quantum/Information/DickeCliffordProductObstruction.result`
proves the universal total-product obstruction. The result supplies an
analytical proof of Remark F.1, beyond the source's finite orbit searches.
The DickeCertificate foundation reuses existing bitstring-indexed states,
operators and phased Pauli group; DickeCertificate supplies the Dicke
expectation certificate.

## Gap

Issue #12575 preregisters the Tier 1 named assertion, source quotation,
full quantified statement, literature check and invariant route before
any Lean probe. The directly read v1 PDF leaves the general assertion
unproved. The issue's INSPIRE citing-work check reports arXiv:2609.27128
and arXiv:2607.14222 without a Dicke settlement; that check is
orchestrator-reported. The search result is absence in the searched scope,
not exhaustive priority or an assertion that no other proof exists.

## Route

Clifford conjugation permutes Hermitian Pauli words up to sign. It preserves
both N, the number of unit-modulus expectations, and integrality of all
expectations after multiplication by a fixed positive integer B.

For Dicke states, B = n.choose k works. Their unnormalized weight-layer
indicator has Gaussian-integer expectations, which are real by Hermiticity.
Weight-layer exchange rigidity forces the flip and sign masks of an
eigen-Pauli word to be constant. Only I^n and Z^n remain, together with
X^n and Y^n when n = 2k. Therefore N ≤ 2 off the balanced layer and N ≤ 4
on it. These bounds concern the same Dicke vector as the denominator.

For a normalized product with integral B-scaled Pauli expectations, each
local Bloch vector is rational. Its primitive integer coordinates satisfy
a²+b²+c²=d² with d > 0. A primitive denominator cannot be two; denominator
one yields a nonidentity unit-expectation Pauli. Tensoring Bézout identities
proves ∏j d_j divides B. If s denominators equal one, choosing either the
identity or the local unit Pauli at each such site gives N ≥ 2^s, while
∏j d_j ≥ 3^(n−s). Both estimates use that same product state.

The count bound forces s ≤ 2. For n ≥ 4, Pascal induction gives
n.choose k < 3^(n−2), contradicting the denominator lower bound and
∏j d_j ≤ B. At n = 3 the layer is unbalanced, so s ≤ 1 and 9 ≤ B ≤ 3 is
impossible.

## Falsifier

A proof of only sampled Clifford orbits, a selected family of products,
or separate bounds lacking a common realization would not settle this
claim. The proof must include every phased Pauli normalizer, all local
normalized complex vectors and every nontrivial layer. No expectation,
rigidity, denominator or purity certificate is supplied as an extra
hypothesis of result. The local lemmas are inline proof steps, with no
additional public companion theorem in the settling module.

## Evidence

The public surface comprises eight DickeCertificate definitions,
`DickeCertificate.dicke_certificate`, the quantified `claim` and the single
settling `result`. Each public declaration has a Scribe description.
Reproduction:

```sh
make lean LEAN_TARGETS="D5.S3.Quantum.Information.DickeClifford.DickeCertificate D5.S3.Quantum.Information.DickeCliffordProductObstruction"
```

The proof uses only propext, Classical.choice and Quot.sound. It adds no
axiom and uses no sorry or native_decide. The Scribe resolution is Proved
and refers to the frozen settling declaration.

## Triage

Tier 1 externally published named problem; preregistration #12575;
resolution proved. The settling result has proof_shape content and
admission_basis open-problem-resolution. DickeCertificate is content with
admission_basis escape-witness. Utility
is none: these are definitions and arbitrary-n structural proofs, not
positive finite-instance certificates, bounded enumeration, checkers or
numerical-reduction algorithms.

### What the settlement shows

**Proved in the delivered chain:** the decisive mechanism is the joint
Clifford invariance of the Pauli unit count and a binomial common integer
denominator, opposed to N_product ≥ 2^s and the primitive denominator
product ≥ 3^(n−s). The Dicke certificate proves the upper counts two or
four, not exact equality or a least denominator. The balanced case n = 2k
and the three-qubit W states (k = 1 or k = 2) are included in result.

**Proved on the live path of result:** conjugation and the product
obstruction use unitarity and Pauli normalization; determinant one is not
used after extracting unitarity. The source's SU restriction is retained
in the public claim. A separate public statement for a broader unitary
normalizer is not delivered.

**Computed:** exact rational enumeration yields N = 2 and least common
Pauli denominator 3 for (n,k) = (3,1) and (3,2), and N = 4 and least common
denominator 3 for (4,2), despite the binomial common denominator B = 6
in the last case. These finite calculations are independent numerical
evidence, not additional Lean theorems. The following command reproduces
the values by summing Pauli phases on the same weight layer:

```sh
python3 - <<'PYVALUES'
from itertools import product
from math import comb, lcm
from fractions import Fraction
for n, k in [(3, 1), (3, 2), (4, 2)]:
    layer = {x for x in product(range(2), repeat=n) if sum(x) == k}
    values = []
    for p in product(range(4), repeat=n):
        total = [0, 0, 0, 0]
        for x in layer:
            y = tuple(b ^ (q in (1, 2)) for b, q in zip(x, p))
            if y not in layer:
                continue
            exponent = sum(2*b if q == 3 else 3+2*b if q == 2 else 0
                           for b, q in zip(x, p)) % 4
            total[exponent] += 1
        assert total[1] == total[3]
        values.append(Fraction(total[0] - total[2], comb(n, k)))
    print(n, k, comb(n, k), sum(abs(v) == 1 for v in values),
          lcm(*(v.denominator for v in values)))
PYVALUES
```

Pauli labels 0,1,2,3 encode I,X,Y,Z. The output rows are
`3 1 3 2 3`, `3 2 3 2 3`, `4 2 6 4 3` in order n,k,B,N,least denominator.

**Open:** exact-count equality for every n,k and the exact least Dicke
Pauli denominator are not separate conclusions of this delivery.
Clifford irreducibility across every bipartition, qudit Dicke states,
other permutation-symmetric families and membership in the source's
full W-magic class of Definition V.1 require their own statements and
literature checks. The total-product obstruction alone does not settle
them.

**Open boundary for the source's other results:** Remark F.1's universal
total-product assertion now has the delivered proof. The source's other
results retain their own hypotheses; any stronger use that needs full
Definition V.1 or every-bipartition irreducibility is not justified by
this theorem alone.

## ASSUMED-UNVERIFIED

The Lean kernel does not authenticate publications or establish exhaustive
novelty. The issue's citing-work scan is orchestrator-reported. The reported
related thesis argument was not obtained here and remains
ASSUMED-UNVERIFIED. Information-escape registration is paused under
CLAUDE.md §3.9.
