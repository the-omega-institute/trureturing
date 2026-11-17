---
slug: op-ferudun2610s2
bibkey: ferudun2026inversepowerline
doi: 10.48550/arXiv.2610.06944
url: https://arxiv.org/abs/2610.06944v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/InversePowerLineEquilibria.result
---

# Inverse-power line equilibria for all real exponents greater than two

## Problem

Ferudun, *Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic
Progressions*, arXiv:2610.06944v1, Remark 5.3 (p. 8), asks whether the conclusion
of Theorem 1.2 holds for $s>2$:

> We make no claim for $s>2$; whether the conclusion of Theorem 1.2 holds
> there remains open.

For every real $s>2$, an equilibrium exists, and a set $X\subseteq\mathbb R$
is an equilibrium exactly when $X=\{\alpha n+\beta:n\in\mathbb Z\}$ for
some real $\alpha>0$ and $\beta$. Here equilibrium has the source's literal
absolute-convergence convention. No global upper or positive lower gap bound
is assumed.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Real $s>2$ | `InversePowerLineEquilibria.claim` quantifies over real `s` with `2 < s` | Full real range |
| At least two particles | `InversePowerLineBasics.IsSEquilibrium` uses `X.Nontrivial` | Literal condition |
| Local finiteness | Every `X ∩ Set.Icc u v` is finite | All closed bounded intervals |
| Finite total force | Magnitude `Summable` on the subtype of points of `X` different from `x` | Absolute convergence, no principal value |
| Zero net force | Signed `HasSum` with value zero on the same subtype | Unordered zero sum |
| Arithmetic progression | `InversePowerLineBasics.arithmeticProgression` is the range of the affine map on all integers | Positive scale and arbitrary real translation |
| Converse | The iff in `claim`; `progression_equilibrium` holds for all $s>1$ | No weakening |
| Existence | Explicit existential conjunct, supplied by `equilibrium_exists` | The equilibrium class is nonempty |

The predicate and progression are the preregistered literal definitions. The
integer enumeration is a proof device, not an extra hypothesis. Real-valued
`energy` represents the source energy only in the summable applications proved
here; it does not represent extended infinite energy for a nonsummable series.

## Motivation

The preregistration is [#27202](https://github.com/the-omega-institute/trureturing/issues/27202).
The settling declaration is
`D5.S3.StatisticalMechanics.InversePowerLineEquilibria.result`.
The source note is `Library/Asymptotics/ferudun2026inversepowerline.md`.
All five modules have `generality: G`, `utility: none`, and
`admission_basis: escape-witness`.

## Gap

The source proves the classification for $1<s\le2$. Its full-network energy
estimate for $s>2$ encounters small gaps. The settlement uses induced networks
on reciprocal-gap sublevels, where the gaps are bounded below, rather than
assuming a global bound.

The literature screen in #27202 reports no settlement of the all-$s>2$
statement in its searched scope. It includes the earlier Zenodo release
10.5281/zenodo.23113437, whose restricted sketch is unclaimed, and the related
Georgakopoulos–Kolountzakis line-equilibrium work. The source version is v1.
Unread fulltexts and incomplete search endpoints remain within the
`ASSUMED-UNVERIFIED` completeness boundary.

## Route

Increasing integer enumeration transports the absolutely convergent forces.
Adjacent-force comparison bounds neighbouring gap ratios. Positive symmetric
conductances make the gaps harmonic; multiplying by both endpoint gaps makes
the reciprocal gaps harmonic. Interval packing supplies a second-moment bound
and a linear window-mass bound on each reciprocal-gap sublevel. A compactly
supported coordinate cutoff then has induced energy tending to zero.

If a positive harmonic function is nonconstant, a proper positive sublevel has
strict exterior flux. The induced ground-state identity gives a strictly
positive lower bound on the energy of a function equal to one at a chosen
vertex, contradicting the cutoff bound. Reciprocal gaps are therefore constant.
Integer affine reconstruction gives the progression. The progression converse
uses absolutely convergent inverse-power sums and cancellation.

## Falsifier

A locally finite nontrivial real set with absolutely convergent zero forces at
some real $s>2$, but with nonconstant consecutive gaps, would contradict
`InversePowerLineEquilibria.result`. A finite truncation with a nonzero residual,
a principal-value configuration or unequal particle strengths does not meet
these hypotheses.

## Evidence

The settling theorem is `InversePowerLineEquilibria.result : claim`. The
supporting statements are in `InversePowerLineBasics`,
`InversePowerLineConductance`, `InversePowerLineNetwork` and
`InversePowerLinePowerPacking`. The decisive same-module content witness is
`InversePowerLineEquilibria.capacity_zero_of_second_moment_mass_bound`, a
private theorem consumed by the reciprocal-gap constancy argument.

The escape audit is unfinished under
[#27401](https://github.com/the-omega-institute/trureturing/issues/27401).
No four-slot registration is claimed validated. Full dependent-family source
reconstruction, equivalence, variation, sensitivity and observational-dependence
evidence is absent for the public theorem telescopes.

### Finite experiment

[Experiment directory at commit f4a41230ecfb85817d3a27660066d47d838fdd53](https://github.com/the-omega-institute/trureturing-experiments/tree/f4a41230ecfb85817d3a27660066d47d838fdd53/docs/reports/inverse-power-line-equilibria).
The script is `check.py`, SHA-256
`508aa1cb5ebbdf848600152655556be4f55c4bc6cb02fe1836ee9f73cf2da9be`.
The command
`git -C /Users/auric/trureturing-experiments show f4a41230ecfb85817d3a27660066d47d838fdd53:docs/reports/inverse-power-line-equilibria/check.py | python3 -`
exits 0. It checks 81 inverse-square distance pairs; 8,190 aligned truncation
residual cases for gap lists of lengths 2–5, entries 1–3 and integer exponents
2–6; 3,780 symmetric progression-force cases; 6,003 induced ground-state
identity cases on networks of at most three vertices; one local sublevel-flux
sign case; and 5,832 restricted near-energy and integral comparisons. The
specified non-equilibrium truncation has residual $-171647/216000$.
These are finite algebraic and truncation tests; they do not prove the infinite
rigidity theorem or its nonintegral exponent range.

## Triage

1. **Proved (kernel-checked):** the exact all-real $s>2$ inverse-power
   classification, without global gap bounds, by
   `InversePowerLineEquilibria.result`.
2. **Proved (kernel-checked):** the progression converse and explicit existence
   for every $s>1$, by `InversePowerLineBasics.progression_equilibrium` and
   `InversePowerLineBasics.equilibrium_exists`.
3. **Proved (kernel-checked):** abstract positive-harmonic constancy for complete
   positive conductances when every proper positive sublevel has zero induced
   capacity and the stated row sums converge, by
   `InversePowerLineNetwork.harmonic_constant_of_sublevel_capacity_zero`.
4. **Computed:** the finite checker validates only the finite algebraic and
   truncation tests in the experiment entry above, with the recorded command,
   exit 0 and script SHA-256.
5. **Open:** classification for arbitrary decreasing force laws is not proved.
6. **Open:** principal-value equilibria are outside the absolute-convergence
   convention and are not classified.
7. **Open:** a probabilistic recurrence characterization is not formalized;
   no literature-level open claim is made for that bridge.

### What the settlement shows

The decisive mechanism is zero induced capacity on proper reciprocal-gap
sublevels together with the strict exterior-flux energy obstruction. The
settlement removes the $s\le2$ restriction for inverse powers under the
source's absolute-convergence convention. It does not require recurrence of
the full transformed network. Combined with the source's stated theorem for
$1<s\le2$, it yields the full inverse-power classification for $s>1$; that
combined range is an application of the source theorem and this result, not
a separate Lean theorem in this module. The converse and existence already
hold for all $s>1$ in the compiled helpers. The abstract harmonic theorem has
the capacity and convergence hypotheses of item 3; neither arbitrary force
laws nor principal-value forces inherit it without additional bridges.
No dependent source assertion beyond the extended classification is claimed.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority remain ASSUMED-UNVERIFIED.
The source and literature checks are the orchestrator's reported readings in
#27202; the bounded screen is not an exhaustive novelty proof. The escape-audit
registration evidence in #27401 is unfinished. The finite experiment does not
certify any uniform infinite extension of its test ranges.
