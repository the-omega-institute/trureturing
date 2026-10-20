---
slug: svinin-2015-discrete-polynomial-identity
bibkey: svinin2015discrete
doi: 10.1088/1751-8113/49/9/095201
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.result
url: https://arxiv.org/abs/1505.06394v2
---

## Problem

A. K. Svinin, *On integrals for some class of ordinary difference equations
admitting a Lax pair representation*, arXiv:1505.06394v2, Conjecture 1,
Eq. (48), asks whether

$$
\langle S,T\rangle_s^r(i)=\sum_{j=0}^{r-2}(-1)^j
u(i+r-j-2)u(i+s+j)S_{s+j+2}^{r-j-2}(i)T_{s-r+j}^{j}(i+r-j)
$$

is an identity for every $r\ge1$, $s\ge r-1$ and $i\in\mathbb Z$ in the
specialization $(h,n)=(1,1)$. The source says: “Unfortunately, by now we can prove this conjecture only for
r = 1, 2, 3.” The settlement is Proved, under preregistration
[#19287](https://github.com/the-omega-institute/trureturing/issues/19287).
The coefficient field is an arbitrary function $u:\mathbb Z\to R$ into any
commutative ring $R$.

### Statement echo

| Source clause | Lean counterpart | Correspondence |
| --- | --- | --- |
| Eq. (4): strictly increasing tuples $0\le\lambda_1<\cdots<\lambda_r\le s-1$ | `T` | Maps `Fin r → Fin s.toNat`, filtered by `StrictMono`; factor $a$ has offset $a$. |
| Section 2.3: weakly increasing tuples with descending offsets | `S` | The `Monotone` filter and integer offset $r-1-a$ reproduce the factor pattern. The printed first-offset $k$ is read as $r$. |
| Section 3: $(h,n)=(1,1)$ | `T`, `S` | The lattice increments in the two literal sums are one. |
| Section 3.4: alternating binary operation | `bracket` | The sum has indices $j=0,\ldots,r$ and exactly the source's degree, subscript and lattice shifts. |
| Conjecture 1, Eq. (48), all degrees | `claim`, `result` | All rings, functions, degrees $r\ge1$, subscripts $s\ge r-1$ and lattice points are quantified. |
| Degree-zero and nonpositive-subscript conventions | `T`, `S` | Empty products are one; positive-degree maps into `Fin 0` do not exist. Natural subtraction is truncated; lattice arithmetic uses integers. |

No nonvanishing, field-inverse, characteristic or integral-domain hypothesis is
added. For $r=1$ the right-hand side is empty. The Library note
`Library/RecurrenceComposition/svinin2015discrete.md` gives the verbatim source
expressions and locator.

## Motivation

The frozen settling declaration is
`D5/S1/Recurrence/Algebraic/SvininDiscretePolynomialIdentity.result`.
It establishes the prerequisite that the source uses for subsequent relations
between difference-equation families and first integrals in the same
specialization. It proves the entire quantified identity rather than a finite
list of degrees.

## Gap

The source proves only $r\le3$. The literature screen recorded on #19287
inspected arXiv:2106.00539v2, 2307.05866, 2502.06908v1 (Remark 5.12),
2604.13115v1, 2606.24925 and 2605.29722, together with
Hone–Kouloukas–Quispel (2018), Hone–Roberts–Vanhaecke (2024) and
Flajolet (1980). Usmani (1994) was unread. No general proof was identified in
that searched scope; completeness and priority are ASSUMED-UNVERIFIED.

## Route

Partition weighted monotone and strictly monotone tuples according to whether
their first coordinate is zero. Explicit inverse correspondences give the left
Pascal recurrences. Reversing both tuple coordinates and the input lattice
gives the right recurrences. Let $Q^p_s(i)=S^p_s(i)$ for $p\le1$, and for
$p\ge2$ put

$$Q^p_s(i)=S^p_s(i)-u(i+p-2)u(i+s)S^{p-2}_{s+2}(i).$$

The recurrences telescope to
$\langle Q,T\rangle^r_s(i)=\langle Q,T\rangle^r_{s-1}(i+1)$ for $s\ge r$.
At $s=r-1$, every term with positive $T$-degree vanishes. The remaining
$Q^r_{r-1}(i)$ is a finite-window function invariant under translation for
every input function. Cut off that input to zero beyond its observation
window; a disjoint translated window then sees only zero. Locality and shift
invariance make the boundary zero. Induction on $s-r+1$ and expansion of the
quadratic correction yield Eq. (48). No division occurs.

## Falsifier

A commutative ring, function $u$, degree $r\ge1$ and integers $s\ge r-1,i$
violating the displayed identity would contradict `result`. Noncommutative
coefficients or other coprime $(h,n)$ lie outside its statement. The finite
symbolic experiment below checks only its stated range and supplies no
unbounded inference.

## Evidence

`D5.S1.Recurrence.Algebraic.SvininDiscretePolynomialIdentity.result` is the
kernel-checked theorem of `claim`. The axiom closure of every public
declaration is contained in {propext, Classical.choice, Quot.sound}.
The module has no D5 imports; its prerequisites are pinned Mathlib.

Experiment: [symbolic polynomial check](https://github.com/the-omega-institute/trureturing-experiments/tree/dafb15a7b6763e3fe0f10914f8e2fb2b135b3c8d/docs/reports/svinin-2015-discrete-polynomial-identity-48).
The command `git -C /Users/auric/trureturing-experiments show dafb15a7b6763e3fe0f10914f8e2fb2b135b3c8d:docs/reports/svinin-2015-discrete-polynomial-identity-48/check.py > /tmp/op-svinin48-experiment.py && python3 /tmp/op-svinin48-experiment.py`
exits 0. The script SHA-256 is
`4518365271cf5f20710ae33baffdb21dda8c9458caa449d3a4a47f5492fb1838`.
It verifies polynomial equality in independent $u_k$ for $r=1,\ldots,5$ and
$s=r-1,\ldots,r+3$, at $i=0$: 25 cases, all true, `RESULT PASS`.

The escape audit for the sole public theorem `result` is unfinished:
[#19360](https://github.com/the-omega-institute/trureturing/issues/19360).
The dependent infinite-family registration lacks a complete typed source
reconstruction, source-to-law bridge, whole-family variation and role
sensitivity, and actual observational dependence. No Reg registration or
`declared_validated` status is claimed.

## Triage

### What the settlement shows

1. **Proved (kernel-checked).** Telescoping makes the corrected convolution
   invariant under $(s,i)\mapsto(s-1,i+1)$. Evidence: private `bracket_shift`,
   instantiated by `bracket_Q_zero`, with the Pascal recurrences derived from
   `mono_pascal` and `strict_pascal`.
2. **Proved (kernel-checked).** At $s=r-1$, all positive-degree $T$ factors in
   the convolution vanish (`T_vanish`); the residual boundary is zero by
   finite-window locality and shift invariance (`Q_boundary`). These are
   consumed in `bracket_Q_zero`.
3. **Proved (kernel-checked).** The identity holds in every commutative ring,
   including zero divisors and zero input values, without division.
   Evidence: the complete telescope of public `result`.
4. **Proved (kernel-checked).** The locality component requires only
   Zero-valued input and output types, without ring structure.
   Evidence: private `local_translation_invariant_zero`, used by `Q_boundary`.
5. **Source-level consequence; not separately formalized.** The source's
   downstream difference-equation equivalences and first-integral statements
   are conditional on Conjecture 1. This theorem supplies that prerequisite
   for $(h,n)=(1,1)$. Those separate implications and their other hypotheses
   are not kernel-checked here; the evidence for their dependency is the
   source's argument.
6. **Open.** General coprime $(h,n)$, noncommutative coefficients and wider
   recurrence systems are outside this claim. Their literal source-to-
   recurrence correspondence and remaining proof obligations are unresolved.

The continuant/inverse-entry interpretation is a source-level explanatory
route; no continuant, walk-bijection or top-matching-coefficient theorem is
asserted as kernel-checked in this module. The symbolic range in Evidence is
computed; it is distinct from the unbounded theorem in item 3.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are ASSUMED-UNVERIFIED.
The finite search does not establish the absence of a differently represented
owner or an uninspected proof. The source's downstream equivalences and first
integrals are not separately formalized. The escape audit remains unfinished
under #19360. No claim is made for the extensions listed as open in Triage.
