---
slug: bojic-2026-rule-150-local-lcm
bibkey: bojic2026semisimple
doi: null
url: https://arxiv.org/abs/2611.33216v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150.semisimpleOrder_lcm
---

# Bojić’s Rule 150 local semisimple-order identity

## Problem

Ana Bojić, *Semisimple–Unipotent Decomposition and the Exact Order of a Linear Cellular Automaton over F₂*, arXiv:2611.33216v1 (23 November 2026), §2.3, “The Gap Addressed by This Paper,” in the paragraph beginning “Kaneko’s (6) result is, in this respect, an elementary special case, obtained without factoring”. The open identity is stated in the following sentence, with mathematical typography restored from the text extraction.

> The general order formula developed in this paper (Theorem 8.19, Section 8) is stated for all $n$ with $3\nmid n$; whether it reduces to Kaneko’s result exactly when $q=2^k-1$ depends on whether the local semisimple orders $m_i$ satisfy $\operatorname{lcm}(m_2,\ldots,m_r)=q$ for that family—a number-theoretic fact that has not been verified in this paper and is not claimed here.

For all $k,m\in\mathbb N$, set $q=2^k-1$ and $n=2^m q$, and assume $3\nmid q$. This implies $k>0$ because $3\mid 0$. Since 3 is coprime to $2^m$, this is the paper’s invertibility condition $3\nmid n$. For each distinct monic irreducible factor $f$ of $X^q-1$ over $\mathbb F_2$ other than $X+1$, take the semisimple part of the actual Rule 150 multiplier $G=1+X+X^{n-1}$ in $\mathbb F_2[X]/(f^{2^m})$. The LCM of the multiplicative orders of these parts is $q$. At $k=1$ we have $q=1$, the index set is empty and the LCM is 1. Theorem 8.19 gives a separate global period formula for $q=1$.

## Motivation

Theorem 4.7 identifies the cyclic update with multiplication by $G$. Theorem 5.2 gives the invertibility condition, and Proposition 8.2 and Theorem 8.4 give the multiplicities and CRT factors. Theorem 8.8 characterizes the odd-order semisimple component of each local multiplier. For $q>1$, Theorem 8.19 uses the orders on the factors other than $X+1$ as the odd factor of the maximal period. Substituting the local identity into that formula gives the global period $2^m q$ for the admissible Mersenne family with $q>1$.

## Gap

The published version leaves the exact local LCM identity open in §2.3. Its §9.2 reduces each local semisimple order to the multiplicative order of the residue of $G$ modulo $f$. Its example at $n=7$ evaluates one member of the Mersenne family. The asserted identity ranges over every admissible $k$ and every thickness exponent $m$.

## Route

In each primary quotient the Lean construction raises the image of $G$ to $(2^k)^m$. Under the given hypotheses that power is the unique odd-order unit with the required unipotent cofactor, and its order equals the order of $G$ modulo $f$. Frobenius gives $q$ as a common residue exponent. If $d$ is the LCM of the orders, then $X^q-1$ divides $(1+X+X^2)^d-X^d$. The latter polynomial is nonzero and has degree at most $2d$. Since $d$ divides $q$, the positive odd quotient $q/d$ is at most 2 and therefore equals 1.

## Falsifier

A pair $k,m\in\mathbb N$ with $3\nmid (2^k-1)$ for which the LCM of the specified native primary semisimple orders differs from $2^k-1$ would refute the identity. Source correspondence requires the actual cyclic multiplier, the primary thickness $2^m$, exclusion of precisely the trivial factor $X+1$, and the empty LCM at $q=1$.

## Evidence

The named Lean declaration is
`D5.S3.StatisticalMechanics.CellularAutomata.BojicRule150.semisimpleOrder_lcm`.
The staged Scribe `OpenProblemResolutionClaim` uses this dossier’s slug and the `Proved` kind. Its formal target is the single declaration listed in the front matter. The staged Library note records the versioned paper and the exact §2.3 locator. The Lean lemmas `semisimplePart_spec` and `semisimplePart_order` establish the local source correspondence used by the LCM proof.

## Triage

`theorem`. This is the local identity identified by Bojić in §2.3. The formal proof quantifies over all admissible $k,m$ and supplies the empty-index boundary via the empty LCM convention. Tracking issue [#34396](https://github.com/the-omega-institute/trureturing/issues/34396).

## ASSUMED-UNVERIFIED

The versioned paper establishes the historical source wording. Worldwide priority and the current status of independent solutions are outside the verification recorded here. Canonical status depends on deposit of the dossier and resolution of the named current frozen Lean declaration by the repository’s compiled-report consumer.
