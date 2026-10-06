---
slug: nersissian-2026-rule84-mod-three-center-column
bibkey: nersissian2026diagonalbases
doi: 10.48550/arXiv.2609.25078
url: https://arxiv.org/abs/2609.25078v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.result
---

# The Rule 84 center column modulo three

## Problem

Tigran Nersissian, *Diagonal Bases and Diagonal Periods of Elementary
Cellular Automata*, arXiv:2609.25078v1, Remark 6, page 12, states:

> (The outstanding Rule 84 case) The polynomial of Rule 84 is (a + b + ab)(1 + c). Modulo three, its center column begins 1, 1, 2, 2, 1, 2, 2, … and follows the repeating block (1, 2, 2) after the first entry for the tested times 0 ≤ t < 2048. All center values are also units modulo 9 and 27 on that range, as Corollary 2 predicts. An all-time proof of the observed pattern is not supplied here. If Rule 84 is universal modulo three, it is universal at every power of three; three could not be the sole exceptional modulus.

Section 19, page 42, states:

> The classification reduces the remaining single-seed universality question to the eight rules in E at odd primes. The observed Rule 84 pattern modulo three requires an invariant or an all-time recurrence proof. A finite nonzero prefix is insufficient.

This dossier anchors exactly that all-time pattern. Definition 1, page 4,
fixes the canonical positive-coefficient polynomial lift and the synchronous
integer-lattice orbit. For the modulus 3 and the single seed at zero, let
`A 0 x = if x = 0 then 1 else 0` and
`A (t+1) x = (a+b+a*b)*(1+c)`, where
`a = A t (x-1)`, `b = A t x` and `c = A t (x+1)` in `ZMod 3`.
The statement is
`A 0 0 = 1 ∧ ∀ s : ℕ, A (3*s+1) 0 = 1 ∧ A (3*s+2) 0 = 2 ∧ A (3*s+3) 0 = 2`.
It includes every natural time, with no time cutoff or extra hypothesis.

## Motivation

`D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.result`
proves the displayed pattern. Nonzero center values give the unit condition
needed by the source's all-window diagonal-basis universality criterion.
Universality here means unique coordinates for every finite target vector
in the diagonal family, as in the source; it is separate from computational
universality of the full automaton dynamics.

## Gap

Remark 6 supplies only a finite prefix and explicitly omits an all-time
proof. The preregistration in issue #12485 contains the quantified claim,
the finite invariant languages and the literature check before the Lean
probe. The checked v1 text, the companion arXiv:2609.25077, and the MathDB
queries recorded in #12485 supply no proof of this statement.
Repository and pinned Mathlib searches find no prior matching settlement:
`not-found-in-searched-scope`. This bounded check makes no worldwide
priority claim.

## Route

The half-plane `x < 0` remains zero by induction, since
`(0+0+0*0)*(1+c) = 0`. For positive time `t`, every length-seven window
starting at `x ≥ -5` belongs to a finite language indexed by `t mod 3`.
The phase languages have sizes 35, 37 and 38 and share 31 words.
The window at `x = -5` is `0000021`, `0000011` or `0000020` at phases
0, 1 or 2, respectively.

Every compatible length-nine word, whose three overlapping length-seven
windows belong to one phase language, maps under the local rule to a
length-seven word in the successor language. The boundary update uses the
proved zero left input and membership of the actual neighboring window to
constrain its right input. Kernel-checked finite closure certificates and
the time-one base establish the invariant by unbounded induction. The
sixth letter of the boundary window is the center value.

## Falsifier

An incorrect certificate would give a compatible length-nine word whose
image is outside the next language, or a boundary word with an admissible
right extension that fails to map to the next boundary word. A time with
center value different from the displayed three-phase pattern would
contradict the settling theorem.

## Evidence

The canonical source is
`D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.lean`.
Its public surface is `A`, `claim` and `result`; the two private theorems
are `zero_left` and `invariant_all`. The bulk and boundary certificates use
`decide +kernel` inside the live induction. The result has only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
The mathematical truth is carried by the Lean declarations and their
kernel-checked proof terms. Prime-power transfer and the source's
diagonal-basis criterion are not additional Lean declarations here.

## Triage

Tier 1 external named open problem, preregistered in #12485.
`admission_basis: open-problem-resolution`; `proof_shape: content` for
`result`, `zero_left` and `invariant_all`. The escape witness is the
all-time window-language invariant. Utility is `none`: the mathematical
conclusion is unbounded in time; the finite certificates support that
induction and are not separately delivered positive finite instances.

### What the settlement shows

- **Proved in this module:** the three-phase length-seven language and
  distinguished boundary word are forward invariant from time 1. The
  private `invariant_all` establishes this and is used by the public GID
  `D5/S3/StatisticalMechanics/CellularAutomata/Rule84ModThreeCenterColumn.result`.
  The zero half-plane supplies the boundary input; overlapping actual
  windows supply compatible bulk inputs. No finite time observation is
  used as a premise of the all-time conclusion.
- **Proved in this module:** the center column is 1 at time zero and
  repeats `(1, 2, 2)` from time 1 onward. The result covers the fixed
  canonical lift, modulus 3 and single seed; it does not assert a pattern
  for another modulus or seed, or a minimal period for the entire orbit.
- **Proved consequence using source results, not separately formalized
  here:** for each integer `a ≥ 1`, every center value of the canonical
  single-seed orbit modulo `3^a` is a unit, and its diagonal basis is
  universal for every finite window length. Polynomial reduction
  identifies its reduction modulo 3 with the orbit proved here, whose
  center value is always 1 or 2. Divisibility by 3 is therefore excluded
  at every time. The identity `p84(0,0,c)=0` gives triangularity; the
  source's Corollary 1 then gives universality, and Corollary 2 transfers
  the prime case to every positive power. This removes the all-time
  Rule 84/modulo-three gap in Remark 6 and Section 19. It does not assert
  that the higher-power center sequence has period three.
- **Open:** the remaining odd-prime cases of the source's eight-rule
  family E, including Rule 84 at odd primes other than 3. The modulus-3
  certificate does not give a certificate at a different prime.
- **Open:** extensions to other initial seeds, minimal window-language
  size, and exact center periods at higher powers of 3. The argument
  provides no classification or sharpness statement for these questions.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish exhaustive worldwide
novelty, priority or absence of an independent proof. The source's
Corollaries 1–2 are literature results and are not kernel-checked in this
module. Other seeds and moduli remain outside its formal statement.
