---
bibkey: bitonti2026sidorenko
authors: Veronica Bitonti, Emma Hogan, Jonathan A. Noel and Dmitry Tsarev
year: 2026
title: Sidorenko Inequalities in Oriented Graphs
doi: 10.48550/arXiv.2611.23222
url: https://arxiv.org/abs/2611.23222v1
claim: "Definition 1.2 gives a relative anti-Sidorenko inequality for every oriented host, and Question 5.3 asks for a connected example with 3 modulo 4 arcs."
strata_touched:
  - D5/S3/Combinatorics/ExtremalDensity/RelativeAntiSidorenkoArcCount
license: citation-only
triage: anchor
---

# Relative Sidorenko inequalities for oriented graphs

## Verified locator

DOI 10.48550/arXiv.2611.23222. The pinned first arXiv version is dated 17 November 2026. The v1 PDF has SHA-256 digest f08d11339f492cd4cc092b2a62c45d15ac7b3a9763ce29746c430700a559b16a. [Pinned arXiv record](https://arxiv.org/abs/2611.23222v1) · [Pinned PDF](https://arxiv.org/pdf/2611.23222v1)

Definition 1.2 compares the number of homomorphisms into an oriented host to the number into its underlying simple graph. Its anti-Sidorenko direction is $\operatorname{hom}(\vec H,\vec G)\le 2^{-e(H)}\operatorname{hom}(H,G)$ for every oriented host $\vec G$. In the source an oriented graph has no loops and at most one arc per unordered pair, and the two counts are counts of adjacency-preserving maps. [Definition 1.2](https://arxiv.org/html/2611.23222v1#S1.E2)

Question 5.3 on p. 25 asks the following.

> Does there exist a connected relatively anti-Sidorenko oriented graph $\vec{H}$ whose number of arcs is congruent to $3$ modulo $4$?

[Question 5.3](https://arxiv.org/html/2611.23222v1#S5.E3)

## Prior constructions

Theorem 1.6 obtains relatively anti-Sidorenko examples of every positive chromatic number. The proof partitions extensions of a fixed image of a new vertex by every possible orientation of the incident arcs and applies AM–GM. Remark 3.10 describes one- and two-terminal extensions using every orientation of the new arcs. With $v$ vertices and $e$ arcs in the copied pattern, the corresponding arc counts are $2^v(e+v)$ and $1+2^{2v}(e+2v)$. Theorem 1.7 establishes relative anti-Sidorenko for perfectly balanced oriented trees. Section 5 reports that their constructions cover every residue except three modulo four and attributes the residue-three tree obstruction to Nie and Wei in reference [29], a personal communication. [Theorem 1.6](https://arxiv.org/html/2611.23222v1#S1.E6) · [Remark 3.10](https://arxiv.org/html/2611.23222v1#S3.E10) · [Theorem 1.7](https://arxiv.org/html/2611.23222v1#S1.E7) · [Section 5](https://arxiv.org/html/2611.23222v1#S5)

In their public preprint, *Sidorenko inequalities and symmetry-forcing for graph orientations*, Jiaxi Nie and Fan Wei define $D_t$ using every sign vector at the $t$ terminals of $K_{t,2^t}$. At $t=2$ this gives the eight-arc $K_{2,4}$ with four private vertices. Equation (18) averages the sign factors at fixed terminal images, and Theorem 1.7 uses AM–GM. In §5 the proof of Proposition 1.8 adds one directed edge between the two terminals of that copy. Symmetry of the sign product lets them average the edge with its reversal in the two-terminal integral. This gives a nine-arc example containing a triangle. In a finite host's step kernel the integral factors are the normalized counts of the four sign-class intersections. [Nie–Wei arXiv:2611.15027v1](https://arxiv.org/abs/2611.15027v1) · [Definition 3](https://arxiv.org/html/2611.15027v1#Thmdefinition3) · [Equation (18)](https://arxiv.org/html/2611.15027v1#S5.E18) · [Proposition 1.8](https://arxiv.org/html/2611.15027v1#S1.Thmthm8)

The construction answering Question 5.3 reuses that sign product. Its distinctive step is to identify one terminal of each of two copies and to add a directed edge between the other terminals. Their identical conditional profiles allow reversal averaging at each image of the common root. The resulting seventeen-arc core has the form needed to multiply by the fixed-root bound for a balanced two-arc star. The witness and its scope are recorded in the dossier. [Problem dossier](../../Problems/bitonti-hogan-noel-tsarev-2026-question-5-3.md)

## Source licenses

Bitonti et al. v1 is CC BY-NC-SA 4.0. Nie–Wei v1 is CC BY-NC-ND 4.0. This note uses source locators, attribution, a short quotation of the problem, and independent mathematical description. The front matter describes the note's citation-only use. [Bitonti et al., v1 record](https://arxiv.org/abs/2611.23222v1) · [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/) · [Nie–Wei, v1 record](https://arxiv.org/abs/2611.15027v1) · [CC BY-NC-ND 4.0](https://creativecommons.org/licenses/by-nc-nd/4.0/)
