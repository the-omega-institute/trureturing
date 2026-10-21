---
slug: mandel-robins-2019-minimal-rational-foic-faces
bibkey: mandel2019dragging
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/InterlaceFan/Result.result
url: https://arxiv.org/abs/1908.03208
---

# Minimal rational faces of the fan of interlace certs

## Problem

A. Mandel and S. Robins, *Dragging the roots of a polynomial to the unit circle*,
arXiv:1908.03208v3, Section 10, Problem 3:

> What are the minimal faces of the FOIC that contain rational points? Most rays clearly do not (except in darga 6). On the other hand, Section 9.2 gives several examples of faces that do. Are there interlace rational polynomials in those minimal faces?

For $n\ge2$, write $J=\{0,\ldots,\lfloor n/2\rfloor\}$ and
$O_d=\{j\in J:n/\gcd(n,j)=d\}$ for $d\mid n$. For nonempty $S\subseteq J$,
let $F_S$ be the closed face where every index in $S$ attains the maximum
of the interlace functionals of equation (12). The classification concerns
nonzero rational points; zero belongs to every closed face.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Darga and sigma coordinates | `n ≥ 2`, `x : Fin (n / 2) → ℝ` | Coordinate k represents sigma index k+1. |
| Interlace certs and fan faces | `I`, `certIdx`, `interlaceNumber`, `face` | Equations (12)–(15), Proposition 5.5, and the Interlace Formula. |
| Rational points | `IsRationalPt`, `HasRatPt` | Nonzero rational coordinates. |
| Minimal rational faces | Second conjunct of `claim` | Maximal cert sets are exactly the complements of individual order classes. |
| Interlace rational points in those faces | Third conjunct of `claim` | Every nonzero rational point has strict inequality on the omitted class and rational maximum. |

## Motivation

The result is `D5/S3/Arith/InterlaceFan/Result.result`. It identifies the rational
structure of the fan and answers the existence question throughout every
minimal rational face. The proof route was derived with the assistance of the
ChatGPT Pro model.

## Gap

The pinned rational-face criterion, maximal-certificate classification and
rational-interlace assertion constitute the formal target. Face dimensions,
the count of distinct geometric faces and relative-interior terminology are
geometric consequences described below, rather than additional Lean statements.
Literature completeness and priority are unverified.

## Route

A rational polynomial taking a rational value at one primitive root takes the
same value at every root of that order, by cyclotomic minimal-polynomial
divisibility. The order-one cert gives a rational initial value. Meeting every
order class therefore forces all functional values to coincide, and Fourier
injectivity forces the coordinate vector to vanish.

Ramanujan sums construct rational coordinates with values
$\bigl(\varphi(d)-n[j\in O_d]\bigr)/2$. Thus every cert outside $O_d$ is maximal
and every cert in $O_d$ is strictly smaller. This gives the rational-face
criterion, and inclusion of finite cert sets gives maximality. In the
order-one exceptional case, the weighted zero-sum identity expresses the
common maximum as a rational multiple of the rational zero-index value.

## Falsifier

For $n\ge2$, a nonempty cert set admitting a nonzero rational point while meeting
every order class, a maximal such set other than $J\setminus O_d$, or an
irrational interlace number at a nonzero rational point of a classified minimal
face would contradict `result`.

## Evidence

`D5/S3/Arith/InterlaceFan/Result.result` is the exact pinned `claim`. The supporting
Fourier module gives injectivity, the weighted hyperplane and exact cert-set
realization. The cyclotomic module gives rational value propagation and explicit
Ramanujan witnesses. Polynomial coefficients are rational: for even $n$, the
middle sigma coordinate is halved so the reciprocal polynomial coefficient is
the unhalved Ramanujan sum.

The witnesses' cert sets and interlace numbers were numerically tested for all
$2\le n\le40$ and $d\mid n$, comprising 157 cases. These floating-arithmetic
checks are outside the Lean development and are not part of the formal proof.

The integration theorem's four-slot registration is unavailable at the named
claim boundary: the source selector requires a claim definition and its theorem
to have the same module owner. Here `Defs.claim` and `Result.result` have distinct
owners; the inspector diagnostic is `unclassified_form:source.definition_owner`
(IE-C050). No validated registration for `result` is asserted.

## Triage

- **PROVED (formalized).** A nonempty $S\subseteq J$ admits a nonzero rational point exactly when it misses an order class. The maximal such cert sets are exactly $J\setminus O_d$, $d\mid n$. Every nonzero rational point of the corresponding face has cert set exactly $J\setminus O_d$ and rational interlace number. Explicit rational Ramanujan-sum witnesses have interlace number $\varphi(d)/2$; the value follows directly from their formal functional values and the nonempty complement.
- **PROVED (mechanism, formalized).** Rational evaluations propagate on root-order classes by cyclotomic irreducibility. The evaluation map is an isomorphism onto a weighted hyperplane. A rational value propagates through an order class; when a maximizing set meets every class, its value at index zero is rational, so propagation forces every index to maximize. This does not assert that all values at rational coordinates are rational or constant on order classes.
- **PROVED (paper proof, not formalized as dimension or counting theorems).** In weighted evaluation coordinates, a proper nonempty face $F_S$ is an orthant with $|J\setminus S|$ coordinates: subtract all values from the common maximum and use the weighted zero-sum relation to recover that maximum. Hence $\dim F_{J\setminus O_d}=|O_d|$. Pairing primitive residues j and n-j gives size one for $d\in\{1,2\}$ and $\varphi(d)/2$ for $d\ge3$. The nonempty, disjoint order classes give $\tau(n)$ distinct minimal rational faces. A ray contains a nonzero rational point exactly when it is a classified face with $|O_d|=1$. The strict inequalities in `claim` place every nonzero rational point in the relative interior under this orthant identification.
- **COMPUTED (floating arithmetic).** The cert sets and interlace numbers of the witnesses agree with the formulas in all 157 cases described in Evidence. These are numerical checks outside the formal proof.
- **OPEN.** Problem 4, concerning exact rational polynomials outside $C_0$ and $C_{n/2}$, and Problem 6, concerning a rational-arithmetic algorithm for interlace certs.
- **OPEN (literature completeness).** Searches covered the arXiv API phrases “interlace cert” and “dragging the roots”; repository D5, Problems, Library and Blueprint references to the title, FOIC and arXiv identifier; GitHub interlace references; and Formal Conjectures references to Mandel. The source and arXiv:2609.34551v1 were read; the latter cites the source without treating FOIC faces. A reported terminology citation in arXiv:2110.14100 was not read. No answer to the problem was found in that scope. Citation indexes were not exhaustively checked; this is not a priority certification.

## ASSUMED-UNVERIFIED

Literature completeness, priority and exhaustive coverage of subsequent papers
are unverified. The floating-arithmetic readings have the finite scope stated
above. No geometric dimension, totient-class cardinality or ray-classification
Lean theorem is claimed. The `result` registration remains unavailable at the
claim-owner boundary described in Evidence.
