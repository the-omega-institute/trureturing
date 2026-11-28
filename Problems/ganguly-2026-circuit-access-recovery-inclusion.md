---
slug: ganguly-2026-circuit-access-recovery-inclusion
bibkey: ganguly2026stabilizersecretsharing
doi: 10.48550/arXiv.2611.27300
url: https://arxiv.org/abs/2611.27300v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/GangulyCircuitAccess/Recovery.result
---

# Ganguly Section VI Problem 2 on circuit access and recovery

## Problem

Sayantan Ganguly, *Symplectic Matroids, Stabilizer Codes, and Quantum Secret-Sharing*, arXiv:2611.27300v2, Section VI, Problem 2, printed page 22, asks whether the circuit-authorized family of a finite simple graph is contained in its recovery family whenever the circuit family is a quantum access structure.

For a finite simple graph G on Fin(n) and a dealer d, the binary adjacency matrix M and the paired columns [I | M] define the circuit family. Circuit supports meet the dealer, project to player sets, and are upward closed. The quantum access condition requires a nonempty family whose members intersect pairwise, including a member with itself. Recovery of A means one CPTP map left-inverts the dealer-slice encoding followed by discarded-player trace on every logical matrix.

The preregistration is [issue #35163](https://github.com/the-omega-institute/trureturing/issues/35163), and the source question is [printed page 22](https://arxiv.org/pdf/2611.27300v2#page=22).

## Motivation

The question asks whether pairwise intersection of circuit supports forces operational recovery from every circuit-authorized player set. A negative answer separates the combinatorial access condition from the information carried by the reduced encoding.

## Gap

The source states the question and records inclusion for qualifying simple graph--dealer pairs through six vertices in Table I. The bounded literature screen attached to issue #35163 found no prior exact settlement in its searched sources. Priority outside that scope remains unverified.

## Route

Use the simple graph on vertices 0 through 6 with edges 01, 02, 04, 06, 12, 13, 16, 23, 25, 45, 46 and 56. Take dealer 4 and retained players A = {2, 5, 6}. The circuit relation with its single one at vertex 5 gives the circuit {2, 4, 5*, 6}, so A is authorized. The ten minimal supports used by the access proof are 026, 036, 056, 236, 256, 356, 0123, 0125, 0135 and 1235, and every pair intersects.

The unnormalized dealer columns have Gram matrix 64 I. Multiplying each column by 1/8 gives the isometric encoding. The full seven-qubit graph state has amplitude factor 1/sqrt(128), and Proposition 8(3) extracts the encoding columns by multiplying each dealer slice by sqrt(2).

For every retained pair of configurations, the mixed signed sum over the three discarded vertices is zero. Consequently the two distinct logical X eigenstate projectors have the same reduced matrix on A. Any function of that retained matrix, including the function induced by a CPTP recovery map, would have to return two distinct matrices from one input.

## Falsifier

A failure of the circuit witness, pairwise-intersection certificate, slice isometry, mixed-column cancellation, or logical-state distinction would invalidate the refutation. A smaller simple-graph witness satisfying the same antecedent would change the contextual size boundary.

## Evidence

The settling declaration is `D5.S3.Quantum.Information.GangulyCircuitAccess.Recovery.result`, whose compiled type is the literal negation of `D5.S3.Quantum.Information.GangulyCircuitAccess.Recovery.claim`. The current scoped report gives the module statement identity `sha256:2d89de495f5b976065e654f96dadee09f5492bec2ba98a267a74b33ba710fa2b` and the result statement identity `sha256:cd4f51774897d120a88d9c97809000068c61eef63de59503bdc2e2741a19d358`. The result's axiom closure is `Classical.choice`, `Quot.sound` and `propext`.

The result uses the checked seven-vertex authorization and quantum-access certificates, the reduced-density collision, and the ordinary-function obstruction to recovery. The separate checked witness correspondence supplies the isometry and shortened-code interpretation. The contextual lower-bound claim through six vertices is attributed to the paper, Table I, the dealer-component reduction, and the supplied finite enumeration. It is not a declaration in this delivery.

The reviewed source-bound registration disclosure is posted at [issue comment 7236279627](https://github.com/the-omega-institute/trureturing/issues/35163#issuecomment-7236279627). It names the nine unfinished audit targets and their concrete missing evidence. The Gram registration for `Combinatorial.witness_signed_gram` is the one locally validated registration. The other nine registrations remain unfinished, including the closed-truth source-binding diagnostic for `Combinatorial.witness_signed_cross_zero`.

## Triage

The named question is refuted by the frozen `Recovery.result` declaration. The utility is `kind=certified-instance; basis=refutes` with typed `claim` and `result`. The result is exempt from four-slot registration under the refutation rule. The nine other source-written public theorem registrations remain unfinished under the linked disclosure and are not reported as validated.

### What the settlement shows

The seven-vertex simple graph has a pairwise intersecting circuit family and an authorized set whose reduced encoding identifies two distinct logical inputs. The source's operational recovery implication therefore fails at seven vertices. The checked minimum-size boundary remains contextual evidence. The paper's six-vertex inclusion table and the supplied enumeration are outside the Lean result.

For this encoding and retained set, the collision rules out every recovery function of the retained matrix. Stronger conditions on the graph or the circuit-access antecedent that exclude this witness, alternate encodings, and the minimum-size claim as a standalone theorem are outside the scope of the result. The source's other results retain their stated hypotheses.

## ASSUMED-UNVERIFIED

The literature screen and priority statement are bounded by the searches recorded in issue #35163. The minimum-size assertion through six vertices is contextual evidence from the cited source and supplied enumeration. No claim of exhaustive worldwide novelty or priority is made.
