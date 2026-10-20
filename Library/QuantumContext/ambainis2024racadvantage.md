---
bibkey: ambainis2024racadvantage
authors: Andris Ambainis; Dmitry Kravchenko; Sk Sazim; Joonwoo Bae; Ashutosh Rai
year: 2024
title: "Quantum advantages in (n,d)↦1 random access codes"
doi: 10.1088/1367-2630/ad9bdf
url: https://arxiv.org/abs/1510.03045v4
claim: "For (n,d)↦1 random access codes with shared randomness, the paper proves that majority-encoding-identity-decoding is an optimal classical strategy, constructs quantum strategies with two measurement settings that beat it in the cases computed, and conjectures that quantum advantages appear in (n,d)↦1 random access codes in general."
strata_touched:
  - D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage
license: citation-only
triage: anchor
---

# Quantum advantages in (n,d)↦1 random access codes

Andris Ambainis, Dmitry Kravchenko, Sk Sazim, Joonwoo Bae and Ashutosh Rai, arXiv:1510.03045v4 (quant-ph), 2024-12-20; published in New J. Phys. 26 (2024) 123023. Quotations are from the v4 TeX source.

The scenario (Section 2):

> In this section, let us summarize the scenario of RACs. We consider RAC protocols by assuming that two parties can access \emph{shared randomness}. A sender, Alice, prepares a message of length $n$ uniformly at random,

> randomly and uniformly. With a selection of $j$, Bob attempts to guess the $j$-th letter, $x_j$, in the message in Eq. (\ref{eq:msg}). To this end, two parties are supposed to deliver a single system in one direction from Alice to Bob, where the system is $d$-dimensional and either classical or quantum.

The figure of merit (Section 2, Eq. (4)):

> \overline{\mathrm{P}}_{\mathcal{S}}   &=& \frac{1}{nd^n}\sum_{x \in X^n}\sum_{j=1}^n \mathrm{P}[\mathcal{S}(x,j)=x_j]  \label{eq:gue}

Classical strategies (Section 3.1):

> In a deterministic strategy, first Alice encodes her words $x = x_1 x_2 \ldots x_n \in X^n$ by applying some deterministic function

The open question (Section 5):

> We conjecture that the quantum advantages would appear in $(n,d) \mapsto 1$ RACs in general and leave it as an open question. The problem also addresses minimal resources, i.e., two measurement settings, to achieve quantum advantages in information theory.

## Verified locator

- URL: https://arxiv.org/abs/1510.03045v4 (v4, 2024-12-20; source `qracs.tex`, md5 `a723d4fe05c966840473e9a9e6c3c3a8`): the scenario (l. 225, 233), the figure of merit (l. 267), deterministic and shared-randomness strategies (l. 280–300), and the open question (l. 956).
- DOI: 10.1088/1367-2630/ad9bdf (New J. Phys. 26, 123023). The published text was not read.
