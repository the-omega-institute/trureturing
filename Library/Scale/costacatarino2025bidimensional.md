---
bibkey: costacatarino2025bidimensional
authors: Eudes Antonio Costa; Paula M.M.C. Catarino
year: 2026
title: On Matrices with Bidimensional Fibonacci Numbers
doi: 10.2478/amsil-2025-0014
url: https://journals.us.edu.pl/index.php/AMSIL/article/download/22306/18885
claim: "The unnumbered conjecture in section 4, page 73, asserts that every bidimensional Fibonacci matrix of order 2 has nonzero determinant at all nonnegative indices."
strata_touched:
  - D5/S1/Recurrence/CostaCatarinoBidimensionalFibonacci
license: citation-only
triage: anchor
---

# On Matrices with Bidimensional Fibonacci Numbers

## Verified locator

DOI: 10.2478/amsil-2025-0014

Source: https://journals.us.edu.pl/index.php/AMSIL/article/download/22306/18885

Journal version: *Annales Mathematicae Silesianae* 40(1), 59–76 (2026).
Online publication: 22 September 2025. No arXiv version was located in the
literature screen recorded in issue #22448; completeness of that screen is
ASSUMED-UNVERIFIED.

## Source definitions

Definition 2.1, p. 63:

> For integers \(m\geq0\) and \(n\geq0\), the bidimensional Fibonacci numbers \(\{f_{(m,n)}\}_{m,n\geq0}\) are defined recursively by

\[
f_{(m,n)}:=f_{(m-1,n)}+f_{(m-2,n)},\quad\text{for all }n\text{ and }m\geq2,
\]

\[
f_{(m,n)}:=f_{(m,n-1)}+f_{(m,n-2)},\quad\text{for all }m\text{ and }n\geq2,
\]

> with initial terms \(f_{(0,0)}=0\), \(f_{(1,0)}=1\), \(f_{(0,1)}=i\), \(f_{(1,1)}=1+i\), where \(i\) is the imaginary unit and \(i^2=-1\).

Lemma 2.5, p. 64:

> For non-negative integers \(n\) and \(m\), the bidimensional Fibonacci numbers are described as follows:

\[
f_{(m,n)}=f_m f_{n+1}+i f_{m+1}f_n. \tag{2.6}
\]

Here the scalar sequence is the ordinary Fibonacci sequence, beginning
\(0,1,1,2,3,5,\ldots\). The source attributes this closed form to
Oliveira–Alves–Paiva [34, Theorem 9].

Definition 3.1, p. 67:

> For all non-negative integers \(m\) and \(n\), the bidimensional Fibonacci matrices \(\{\mathcal F_{(m,n)}\}_{m,n\geq0}\) are given by

\[
\mathcal F_{(m,n)}:=
\begin{bmatrix}
f_{(m+2,n+2)}&-f_{(m+1,n+1)}\\
f_{(m+1,n+1)}&-f_{(m,n)}
\end{bmatrix}, \tag{3.1}
\]

> where \(\{f_{(m,n)}\}_{m,n\geq0}\) is the bidimensional Fibonacci sequence.

## Conjecture

Unnumbered Conjecture, end of §4, p. 73:

> Let \(\{\mathcal F_{(m,n)}\}_{m,n\geq0}\) be the sequence of bidimensional Fibonacci matrices of order 2. For all non-negative integers \(m\) and \(n\), the determinant is non-vanishing, that is, the determinant satisfies:

\[
|\mathcal F_{(m,n)}|\neq0.
\]

The bars denote determinant. The encoded claim additionally asserts existence
of the recursively specified sequence and quantifies over every sequence
satisfying the two recurrences and all four initial values. Both axes and
the diagonal remain in the natural-index domain.

The source's printed Proposition 4.6 axis formula disagrees with its own
Definition 3.1 and Example 4.1 at \((1,0)\). That formula is not used by the
settlement; its matrix definition is retained.
