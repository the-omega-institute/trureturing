---
bibkey: kuperberg2026oddvas
authors: Greg Kuperberg
year: 2026
title: Odd Vassiliev invariants vanish at four loops
doi: 10.48550/arXiv.2608.11334
url: https://arxiv.org/abs/2608.11334v1
claim: Defines the rational connected Jacobi quotients with commuting colored legs, gives their symmetric-power coefficient description and connected sum, proves odd vanishing for uncolored four-loop diagrams, and explicitly asks whether the marked four-loop population (1, ell-1) always vanishes for odd ell.
strata_touched: []
license: citation-only
triage: anchor
---

# Odd Vassiliev invariants vanish at four loops

Greg Kuperberg, *Odd Vassiliev invariants vanish at four loops*,
arXiv:2608.11334v1. The primary article's Theorem 1.1 establishes
$\mathcal{P}_{4,\ell}=0$ for odd $\ell$ in the uncolored AS/IHX quotient.
Section 2.1 defines the colored quotient by AS, IHX, and CL. Ordinary
legs of different colors commute; numbered anchors do not commute with
ordinary legs or with each other. A distinguished leg of a singleton
ordinary color is therefore different from an anchor.

Section 3.1, Lemma `l:sympow`, identifies commuting leg populations with
tensor products of symmetric powers of relative first cohomology.
The relative subset consists of the true numbered anchors.
Equation `e:gamma4` gives the common central contraction underlying
IHX coefficient transport; `e:dual` and Section 3.3 describe the dual
weight-polynomial viewpoint. Section 3.2, Lemma `l:consum`, gives
connected sum at a singleton ordinary color. Corollary `c:odd12`
establishes odd vanishing at one and two loops with arbitrary ordinary
colors. The three-loop discussion explicitly retains nonzero
$\mathcal{P}_{3,(\ell,\ell,\ell)}$ when $\ell$ is odd.

In Section 7, “Five or more loops,” the source says:

> We do not know whether $\mathcal{P}_{4,(1,\ell-1)}$ always vanishes.

Here $\ell$ is odd. The same paragraph identifies the remaining bridge
skeleton as a tetrahedron with a tadpole and points out that
$\mathcal{P}_{3,(1,1,1)}$ does not vanish.

The [two-color exposition](../../docs/develop/theory/MARKED_TWO_COLOR_FOUR_LOOP_JACOBI_VANISHING.md)
uses these definitions and coefficient strategy inside its proof. Its
stable auxiliary domain is $g\geq1$ or at least two true numbered
anchors; its one-anchor genus-zero strut and colored-Y counterexamples
explain why the unrestricted auxiliary wording of `l:sympow` is not
used. The two-color argument is not attributed to Kuperberg's uncolored
Theorem 1.1, and it does not use arbitrary-color genus-three odd vanishing
or the scalar leg-by-digon and leg-by-triangle lemmas.

## Verified locator

- Primary article: https://arxiv.org/abs/2608.11334v1.
- Primary HTML: https://arxiv.org/html/2608.11334v1.
- Primary TeX SHA256: `18da8ad7d658cad15bee133f902728c5d9d249b2f6c87b561798e1cf4fe74ead`.
- Definitions: §2.1; coefficient contraction: §2.2, `e:gamma4`;
  coefficient presentation: §3.1, `l:sympow`; socket gluing: §3.2,
  `l:consum`; duality: `e:dual` and §3.3; small genera: §4,
  `c:odd12`; explicit marked question: §7, “Five or more loops.”
