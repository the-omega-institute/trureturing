---
slug: oeis-a128057-three-term-recurrence
bibkey: mathar2014a128057
doi: null
url: https://oeis.org/A128057/internal
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence.result
---

# The A128057 three-term recurrence

## Problem

OEIS A128057 names the expansion of $(1+x)/\sqrt{1+4x^2}$ and attributes
this conjecture to R. J. Mathar:

> Conjecture: n*(5*n-9)*a(n) +4*a(n-1) +4*(5*n-4)*(n-2)*a(n-2)=0.

Work in $\mathbb Q[[X]]$. There exists exactly one $S$ with constant
coefficient one and $S^2=1+4X^2$. Its inverse has constant coefficient
one and satisfies both $SS^{-1}=1$ and $S^{-1}S=1$. Put
$A=(1+X)S^{-1}$ and $a(n)=[X^n]A$. The assertion is

$$n(5n-9)a(n)+4a(n-1)+4(5n-4)(n-2)a(n-2)=0$$

for every natural $n\ge2$. The source prints no onset: this is the
legal-lag interpretation for its offset-zero sequence, not a quoted
source hypothesis. Scalar subtraction is rational and signed; coefficient
indices use natural subtraction. The distinct four-term recurrence in
the entry is outside this assertion. Source attribution and license are
in `Library/RecurrenceAlgebraic/mathar2014a128057.md`.

## Motivation

The target is the exact shorter recurrence for the stated generating
function. A finite coefficient prefix or the established longer
recurrence does not establish this universal assertion.

## Gap

The bounded source and prior-work comparison is recorded in
https://github.com/the-omega-institute/trureturing/issues/30464.
The eleven listed OEIS revisions retain the shorter conjecture line.
Selected Ekhad–Yang–Zeilberger proof collections yielded no exact target
hit. Mathar's P-finite recurrence paper includes A128057 in Example 4 and
provides a general method; the inspected passages identified no explicit
settlement of this exact shorter recurrence. Global citation closure and
implicit settlement by general results remain unverified. These bounded
findings establish no worldwide priority claim.

## Route

Rescale the existing Catalan series by $-1$, obtaining $Xc^2+c=1$.
Then $B=1+2Xc$ satisfies $B^2=1+4X$, and $D=(Xc)'$ satisfies $BD=1$.
Expansion $X\mapsto X^2$ constructs the normalized root. Its constant
coefficient separates the two square-root branches. The inverse and
coefficient bridge give

$$a(2m)=a(2m+1)=b(m),\qquad b(m)=(-1)^m\binom{2m}{m}.$$

Apply the existing adjacent central-binomial identity:

$$(m+1)b(m+1)+2(2m+1)b(m)=0.$$

Splitting each legal index into even and odd cases and normalizing
rational polynomial arithmetic proves the printed three-term relation.
These classical identities and their applications are supporting steps,
not separate claims of new mathematics.

## Falsifier

A nonzero printed left side for the exact normalized source at any
$n\ge2$ refutes the assertion. A finite matching prefix cannot prove it.
Changing the root branch, generating function, lag range or recurrence
changes the target.

## Evidence

The frozen Lean address is
`D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence.result`.
The result includes existence and uniqueness, the normalized two-sided
inverse and the recurrence for every legal index. Its nine private
helper theorems are consumed on that proof's live path. Each theorem has
`proof_shape: bind-only`; the public result's admission basis is
`open-problem-resolution`, under the preregistered source assertion in
#30464. The module declares `utility: none`. No escape witness or new
general recurrence method is claimed. The scoped compiled evidence uses
only `propext`, `Classical.choice` and `Quot.sound`.

The retained Reg mirror proves the full-statement equivalence, variation,
whole-role sensitivity and actual observational dependence for all three
coefficient roles. Its source binding remains `declared_unresolved`:
`IE-C050 ClosedTruthReadout reason=forbidden_dependency
rule=source.unsafe_or_external site="Nat.mod; source_operand=Nat.mod"`.
The concrete missing evidence is an accepted current source-binding
bridge for the actual enrolled readout and all three selected coefficient
occurrences, whose role signature reaches `Nat.mod` through `Fin 3`.
https://github.com/the-omega-institute/trureturing/issues/30493 records
this unfinished audit under CLAUDE.md §3.9. No validated registration is
asserted.

## Triage

| Assertion | Mechanism and boundary |
| --- | --- |
| Normalized source | Proved existence, uniqueness and normalized two-sided inverse in rational formal power series |
| Coefficient pairing | Proved by the Catalan derivative and expansion bridge |
| Exact shorter recurrence | Proved for every natural $n\ge2$ by pairing and the adjacent central-binomial identity |
| Source-bound audit | Compiled audit terms; source binding remains unresolved at `Nat.mod`, linked to #30493 |
| Generalization | No new general recurrence theorem or broader family resolution is claimed |
| Other Mathar conjectures | Outside this result |
| Prior literature | Bounded comparison only; global and implicit prior settlement remain unresolved |

## ASSUMED-UNVERIFIED

The source-bound registration remains unfinished at the concrete bridge
above. Postfreeze independent reviews and native required CI are separate
publication obligations. Universal absence of earlier proofs is not
established by the bounded literature comparison.
