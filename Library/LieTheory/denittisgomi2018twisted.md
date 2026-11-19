---
bibkey: denittisgomi2018twisted
authors: Giuseppe De Nittis and Kiyonori Gomi
year: 2018
title: On the K-theoretic classification of dynamically stable systems
doi: 10.1142/S0129055X1950003X
url: https://arxiv.org/abs/1804.10111v2
claim: The unitary and antiunitary implementation extension has scalar phase kernel and a sign action that inverts phases on antiunitaries; its full extension is twisted and its unitary restriction has central kernel.
strata_touched: []
license: citation-only
triage: anchor
---

# Phase extensions with unitary and antiunitary implementers

The primary text is [arXiv:1804.10111v2](https://arxiv.org/html/1804.10111v2),
version of 8 October 2018, §3.1, equations (3.2)–(3.4). Remark 3.1
discusses the topology and the unitary/antiunitary sign. The year
identifies the arXiv source; the DOI identifies the journal article
in *Reviews in Mathematical Physics* **31** (2019), 1950003.

In finite complex dimension, fix a conjugation $\kappa$ and write
$U^{\pm}(n)=U(n)\cup U(n)\kappa$. The sign homomorphism is $+1$
on unitaries and $-1$ on antiunitaries. The quotient by scalar
phases $\mathbb T=\{zI:|z|=1\}$ is the ray-symmetry group, which
in this fixed-conjugation notation is $PU(n)\rtimes\mathbb Z_2$.
For every implementer,

$$
W(zI)W^{-1}=z^{\sigma(W)}I.
$$

This is the phase action in equation (3.4). Antiunitaries invert
the circle, so the full extension is twisted rather than generally
central. Restriction to unitary implementers has central scalar
kernel. Fixing $\kappa$ does not choose a phase representative for
every ray symmetry.

The exact consumers are [VIII, Theorem 117.1, Proposition 117.2 and
Proposition 118.2](../../docs/develop/theory/QUANTUM_ORIGIN_BILATERAL_POSITIVE_RESET_RIGIDITY_AND_SCALE_OBSTRUCTION_VIII.md).
They work in finite-dimensional compact matrix topology, where the
sign is continuous. The source owns the mature extension structure;
the consumers separately assemble a closed graph of compatible
implementers for the actual original compact group $H$. Surjectivity
of $\pi$ gives uniqueness of the original action attached to an
implementer. Injectivity of the **entire** pure labeling proves the
kernel exactly $\mathbb T$, since a kernel implementer fixes every
source ray. Compact-to-Hausdorff quotient topology gives
$\widetilde G/\mathbb T\cong H$.

The sign descends to $H$ and is trivial on $H^0$. Thus the preimage
$G$ of $H^0$ is a compact subgroup of $U(n)$, with central scalar
kernel and quotient $G/\mathbb T\cong H^0$. The full $H$ may still
have antiunitary implementers. Neither this restriction nor the
ambient semidirect-product description asserts a splitting of the
original-$H$ extension, a global continuous or homomorphic phase
section, or unitary implementation of every original gate word.

No Krein-space classification, K-theory result, infinite-dimensional
contractibility or physical dynamics conclusion is used. The source
does not already supply the consumer's original-$H$ compatible
graph or its whole-domain projection hypotheses. This note contains
only citations and narrow paraphrases; its citation-only designation
does not license redistribution of the paper or its source.
