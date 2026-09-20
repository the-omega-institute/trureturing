---
bibkey: esposito2026globalnonexistence
authors: Giovanni Esposito
year: 2026
title: "Global Nonexistence of Odd Distinct Covering Systems"
doi: 10.5281/zenodo.18440762
url: https://zenodo.org/records/18440762
claim: "The author claims unconditional nonexistence of odd distinct covering systems; the extension implication used in Lemma 3.2 fails for the explicit finite example below."
strata_touched: []
license: "CC BY 4.0, according to the Zenodo record."
triage: "rejected(the stated allocation implication does not account for retained old classes)"
---

# A deficit set need not persist under radical extension

## Source and scope

The Zenodo record identifies version 1.0, publication date 31 January 2026,
and `Paper_I.pdf`. The retrieved manuscript itself is dated May 2026.
These are the two source dates, not an inferred revision history.
Metadata and all three PDF pages were read on 21 September 2026.
The PDF SHA-256 is
`9797688b82fefd76df386ec17bb5b9810993acb23e95d983f4f7cbd6be6728c4`.
The stable download is
https://zenodo.org/api/records/18440762/files/Paper_I.pdf/content.

Lemma 3.2, on pages 2–3, states:

> If D fails to cover U ⊆ G, then no extension of D by a new prime q
> can cover the lifted deficit U′ := U × Z/qZ ⊆ G′.

Its proof allocates each new modulus `qd` to one `q`-fibre and invokes
the insufficiency of every subset of `D` to cover `U`. For an extension
that retains the original `D` classes, the stated implication is false,
even when `D` is the complete set of nonunit divisors of the old period
and its insufficiency holds for **every** choice of old residues.
This note supplies a repository-derived counterexample to that implication.
It does not refute the conjectured nonexistence of odd distinct covering
systems, or assess the separate Papers D and H cited by the manuscript.

## Exact counterexample to the extension implication

Take

\[
 M=35,\qquad D=\{5,7,35\},\qquad
 U=\{0,1,2,3\}\subseteq\mathbb Z/35\mathbb Z,\qquad q=3.
\]

Here `q` is an odd prime outside the old radical `{5,7}`, as required
by the stated lemma; the lemma imposes no increasing-prime-order condition.
For each `d` in `D`, a residue class modulo `d` contains at most one
point of `U`: two distinct points differ by at most three, less than `d`.
Thus any choice of one class per old modulus covers at most three of
the four points. The capacity bound `3 < 4` also holds for every subset
of `D`.

Retain the old classes and add the following distinct odd moduli:

| Modulus | Residue |
|---:|---:|
| 5 | 0 |
| 7 | 1 |
| 35 | 2 |
| 3 | 0 |
| 15 | 8 |
| 21 | 10 |
| 105 | 3 |

These moduli are exactly the nonunit divisors of `105`, namely
`D ∪ {q} ∪ qD`. Via CRT, the lifted set consists of the twelve residues

\[
 U'=\{0,1,2,3,35,36,37,38,70,71,72,73\}\pmod {105}.
\]

The old `5`, `7`, and `35` classes cover, respectively, all three lifts
of `0`, `1`, and `2`. The remaining three lifts of `3` are covered by
the new classes:

\[
 3\equiv0\pmod3,\qquad
 38\equiv8\pmod{15},\qquad
 73\equiv10\pmod{21}.
\]

Consequently the extension covers every point of `U′`. The `105` class
is redundant and is included to show that even using every admissible
divisor once does not repair the implication. Omitting it gives the same
counterexample. The full period still has **36 uncovered residues**;
for example, `4` is uncovered. This is not an odd distinct covering system.

Exhaustive integer verification over all `5·7·35 = 1225` old residue
assignments gives maximum old coverage `3/4`. Direct checking of all
105 residues gives lifted coverage `12/12` and full-period coverage
`69/105`. The elementary argument above establishes the same relevant
claims without relying on enumeration. No new Lean verification is claimed.

## The invariant that a valid induction needs

Fix old residues `a` and write their covered set as `A(a)`. After the old
classes are retained, the remaining demand in each new fibre is

\[
 R(a)=U\setminus A(a),
\]

not all of `U`. The premise

\[
 \forall b,\quad U\not\subseteq A(b)
\]

does not imply that `R(a)` cannot be covered by a fresh subset of the
same divisor labels with newly chosen residues. In the example,
`R(a)={3}`, which one old divisor label can cover after changing its
residue; the different numerical moduli `qd` supply these fresh uses
without violating distinctness.

There is a valid narrower reading: if **only** the new classes `{q} ∪ qD`
are allowed to act on `U′`, each non-pure fibre receives a subset of `D`
and cannot cover `U`. That statement does not include the retained old
classes. If `U` instead denotes the actual survivor set of fixed old
classes, its required insufficiency under **all fresh residue choices**
has not followed from old noncoverage. Either reading leaves the proposed
induction without the needed invariant.

The proof also treats the first-power extension `G × Z/qZ`. Distinct
moduli `q^a d` with different `a` may share the same old cofactor `d`;
allocation across arbitrary new-prime heights needs an additional argument.
The finite counterexample already invalidates the retained-class
implication at height one, independently of that further obligation.

For unrestricted Erdős #7, the missing bridge remains a bound on the
**actual residual set under the same retained family**, with every
original modulus and prime-power depth accounted for. Insufficiency on
a larger test set alone is not that bound.
