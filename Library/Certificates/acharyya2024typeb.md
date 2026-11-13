---
bibkey: acharyya2024typeb
authors: Amrita Acharyya
year: 2024
title: "Type B Set partitions, an analogue of restricted growth functions"
doi: 10.61091/ars162-14
url: https://arxiv.org/abs/2404.14439v1
claim: "Conjecture 20: rcb_B(f(π)) = ros_B(π) + k(k−1) for all π in S_B(⟨n⟩,k)."
strata_touched:
  - D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation
license: CC-BY-4.0
triage: anchor
---

# Acharyya's type B partition pointwise identity

Amrita Acharyya, *Type B Set partitions, an analogue of restricted growth
functions*, arXiv:2404.14439v1 (19 April 2024), published in *Ars Combinatoria*
162 (2025), 191–204, DOI 10.61091/ars162-14. The fixed arXiv version is the
primary statement locator; the journal version labels the same pointwise
assertion Conjecture 3.16.

## Original source and license

- Immutable version record: https://arxiv.org/abs/2404.14439v1
- Versioned full text: https://arxiv.org/html/2404.14439v1
- Versioned PDF: https://arxiv.org/pdf/2404.14439v1
- Journal DOI: https://doi.org/10.61091/ars162-14
- Journal article: https://combinatorialpress.com/ars-articles/volume-162/type-b-set-partitions-an-analogue-of-restricted-growth-functions/

The arXiv version record links CC BY 4.0, and the journal page links the same
license, https://creativecommons.org/licenses/by/4.0/. Attribution belongs to
Amrita Acharyya. This note preserves a short source quotation and a mathematical
mapping; it imports no source software. The source definitions credit Sagan
and Swanson for standard signed partitions and are used with that attribution.

## Full pointwise question

Conjecture 20 states:

> We have that $rcb_B(f(π)) = ros_B(π) + k(k-1)$ for all
> $π ∈ S_B(⟨n⟩,k)$.

Definition 7 specifies all standard type B partitions of the signed interval
$⟨n⟩=\{-n,\ldots,-1,0,1,\ldots,n\}$ into $2k+1$ nonempty blocks.
The zero block contains zero and is closed under negation. For $1≤i≤k$,
$S_{2i}=-S_{2i-1}$, its positive absolute minimum belongs to $S_{2i}$,
and $0=m_0<m_2<\cdots<m_{2k}$. Here $m_i=\min\{|s|:s∈S_i\}$
and $M_i=\max\{|s|:s∈S_i\}$.

Definition 12(1) counts the pairs $(s,S_j)$ with $s∈S_i$ for some $i<j$
and $s≥m_j$. Definition 12(4) counts the same earlier-block pairs with
$0<s≤M_j$. These are signed, inclusive comparisons. Definition 13 fixes zero,
replaces positive $i$ by $n+1-i$, and replaces $-i$ by $-(n+1-i)$.
Lemma 19 defines $f$ as this complementation followed by standardization.
Standardization orients every nonzero block pair with its positive minimum
in the even block and sorts every pair by its absolute minimum, retaining
the zero block first.

The following generating-function equality is a separate assertion. The
pointwise counterexample does not settle it. General preservation and
involution of the implemented map are not separately proved by this delivery.

## Corresponding certificate and boundary

The general-domain Lean claim retains every natural $n,k$ and every standard
signed partition; its designated result is literally `Not claim`. The one
witness is $n=3,k=1$ and $\{0\}/\{-1,2,3\}/\{1,-2,-3\}$.
After complementation and full standardization its blocks are
$\{0\}/\{3,-2,-1\}/\{-3,2,1\}$. The complete ros pairs are
$\{(2,2),(3,2)\}$; the complete rcb pairs of the image are $\{(3,2)\}$.
Thus the universal pointwise equation would give $1=2$.
The owning Blueprint gives the complete domain, algorithm, formulas and proof.
The Lean theorem checks the implemented model; independent source-fidelity
review is pending. No second result, global priority claim, or publication
settlement is asserted here.

The result has `proof_shape: bind-only` and intended
`admission_basis: open-problem-resolution` under issue #30070. Existing finite
set and cardinality infrastructure is reused; no escape witness is claimed.
This source note is categorized with kernel-checkable refutation certificates.
