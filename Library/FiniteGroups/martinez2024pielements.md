---
bibkey: martinez2024pielements
authors: Juan Martínez
year: 2024
title: "On the commuting probability of π-elements in finite groups"
doi: 10.1002/mana.202300338
url: https://arxiv.org/abs/2307.09868v3
claim: "Section 4, printed page 16, asks whether Theorem A holds with the reciprocal of the largest prime dividing the order of the fixed element."
strata_touched:
  - D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1002/mana.202300338

Source: https://arxiv.org/abs/2307.09868v3

## Source question

The final paragraph of §4, printed page 16 of arXiv:2307.09868v3, says:

> As we mentioned in the Introduction, it remains as an open question whether Theorem A holds with $\leq 1/q$, where $q$ is the largest prime dividing $o(x)$.

Theorem A, printed page 2, says:

> Let $G$ be a finite group, let $\pi$ be a set of primes and let $p$ be the smallest prime in $\pi$. If $x \in G_{\pi}\setminus O_{\pi}(G)$, then
> $$\frac{|C_{G}(x)_{\pi}|}{|G_{\pi}|} \leq \frac{1}{p}.$$

The fixed-element interpretation, §2, printed page 4, says:

> It is important to remark that given $x$, a $\pi$-element of $G$, the proportion $$\frac{|C_G(x)_{\pi}|}{|G_{\pi}|}$$ is exactly the fixed point ratio of $x$, where we consider the action of $G$ on $G_{\pi}$ by conjugation.

The Introduction, printed pages 1–2, introduces the notation:

> where $G_{\pi}$ is the set of all $\pi$-elements in $G$.

The source uses the standard notions of pi-elements and the normal pi-core.
The Lean expression for pi-elements requires every prime divisor of the element
order to belong to pi, including the identity. A pi-subgroup has the analogous
prime support condition on its cardinality. The pi-core is the supremum of
normal pi-subgroups. The fixed-element fraction counts centralizing pi-elements
and divides by the number of pi-elements in the whole group, using rational
cardinal quotients. These explanatory definitions are not additional quotations.
The largest prime is expressed by existence of a prime divisor dominating all
prime divisors, over arbitrary actual finite groups with carriers in Type.

## Scope

The repository refutation uses DihedralGroup 3 × DihedralGroup q with pi = {2,q}
and x = (sr 0, r 1). For each prime q ≥ 5 its pi-core is 1 × DihedralGroup q,
its pi-element count is 8q, its centralizing pi-element count is 2q, and its
fraction is 1/4. The final contradiction uses q = 5. This refutes the question,
without refuting the source's Theorem A with the smallest prime in pi.
Theorem B assumes that F*(G) is a pi-prime-complement group; neither that theorem
nor the separate smallest-prime-dividing-order question is settled here.

The arXiv revision supplies the quoted text. The journal text and completeness
of the bounded literature screen are ASSUMED-UNVERIFIED. Related published
dihedral product constructions are not claimed new.

The independent exact experiment is in
`the-omega-institute/trureturing-experiments`, commit
`a7fc2e0a94fb37115555794184d7d7934db2b8a3`,
`docs/reports/martinez-largest-order-prime-commuting/check.py`, SHA-256
`f36fd2bde944e7b3e106b9852df5bc8240ff66a9b5ad68e74fe002495abaeba4`.
The recorded command `python3 -u check.py` exited 0 with `ALL_CHECKS_OK` for
q = 5, 7, 11, 13, 17, 19, 23, 29, 31. Finite experiment output does not prove
the parametric family. This citation-only note includes no program or proof
copied from the source.
