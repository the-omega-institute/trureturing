---
slug: golden-ratio-base4-dfao-minimality
bibkey: barnoffbrightshallit2024using
arxiv_id: 2405.02727
triage: active
motivation_gids:
  - D5/S0/Automata/TypedPartialDFAOOverBase
  - D5/S0/Automata/ZeroInvariantTypedDFAO
  - D5/S0/Automata/TypedStableRightCongruence
  - D5/S0/Certificates/RefutationEncoding
  - D5/S1/Digit/GoldenBase4AutomataOracle
  - D5/S1/Digit/PublishedGoldenBase4Problem
  - D5/S1/Digit/PublishedGoldenDFAStateLowerBound
---

# Minimality of the base-4 golden-ratio DFAO

## Problem

Let

\[
w_i = Z(4^i)
\]

be the canonical most-significant-first Zeckendorf word for `4^i`, and let

\[
d_i = \lfloor4^{i+1}\varphi\rfloor
      -4\lfloor4^i\varphi\rfloor\in\{0,1,2,3\}.
\]

Determine the least number of states needed by a DFAO that emits `d_i` on every
input `w_i`.

The published incomplete-data experiments additionally require:

1. state types compatible with the two-state Zeckendorf validity automaton;
2. a start-state zero loop;
3. output zero at the distinguished start state.

The corresponding fixed-instance target is to prove that no published-class
machine with at most 21 states is globally correct, and to verify a globally
correct 22-state upper machine.

## Machine classes

Three classes must remain distinct.

\[
\mathcal M_{\mathrm{free}}
 = \{M : M(w_i)=d_i\text{ for all }i\},
\]

\[
\mathcal M_{\mathrm{zero}}
 = \{M\in\mathcal M_{\mathrm{free}} : \delta(q_0,0)=q_0\},
\]

\[
\mathcal M_{\mathrm{published}}
 = \{M\in\mathcal M_{\mathrm{zero}} :
       M\text{ is Zeckendorf-typed and }o(q_0)=0\}.
\]

Thus

\[
\mathcal M_{\mathrm{published}}
\subseteq
\mathcal M_{\mathrm{free}}.
\]

An UNSAT certificate using the zero-loop and zero-anchor assumptions proves a
lower bound only for the published class unless a separate theorem removes
those assumptions. A lower bound for the wider free class automatically
applies to the published class.

## Frozen formal substrate

The repository now contains:

- exact canonical power words and exact base-four outputs;
- typed partial DFAO run semantics;
- an explicit anchored zero-invariant machine class;
- global and finite-prefix published model predicates;
- finite prefix occurrences and exact identifications;
- a typed stable-right-coloring relaxation forced by every identification;
- one-way refutation encodings `P -> SAT(F)`;
- exact encodings `P <-> SAT(F)` as a stronger optional interface;
- a finite-prefix LRAT-to-global-lower-bound theorem for the published class.

The key finite-to-infinite implication is

\[
\neg\exists M\in\mathcal M_{\mathrm{published}},
 |Q_M|\le k\land\operatorname{Fits}_N(M)
\Longrightarrow
\neg\exists M\in\mathcal M_{\mathrm{published}},
 |Q_M|\le k\land\operatorname{Correct}(M).
\]

No finite sample coverage theorem is needed. Every globally correct machine
must fit every genuine finite subsample.

## Refutation semantics

For lower bounds, an encoding only needs

\[
P\Longrightarrow\operatorname{SAT}(F).
\]

Together with a checked refutation of `F`, this yields `not P`. The converse is
needed only when a satisfying assignment is to be decoded into a verified
machine. This distinction permits relaxed formulas with spurious satisfying
assignments while preserving sound UNSAT conclusions.

## Stable-right-coloring route

Every exact finite identification induces a color map on prefix occurrences
that satisfies:

1. equal prefixes have equal colors;
2. same-colored parents have same-colored equal-symbol children;
3. same-colored leaves have equal outputs;
4. same-colored prefixes have equal Zeckendorf base runs.

Therefore a refutation of the stable-right-coloring relaxation already excludes
every exact machine on the same color carrier.

This is stronger than pairwise common-suffix conflicts because it retains the
global deterministic transition closure. It is still a relaxation because it
does not require decoding every satisfying assignment into a complete machine.

## Remaining open obligations

1. Reconstruct the published finite dictionary, including the zero anchor.
2. Prove byte-for-byte agreement between the imported dictionary and the exact
   arithmetic oracle.
3. Implement a concrete refutation encoder for each state and type budget.
4. Prove every published finite-prefix model induces a satisfying assignment.
5. Generate and kernel-check the known at-most-14 refutation.
6. Increase the verified lower bound through budgets 15 to 21.
7. Import and independently verify the 22-state transition/output table.
8. Prove its correctness on every `w_i`, separately from finite testing.

## Falsifiers

- A globally verified published-class DFAO with at most 21 states falsifies
  22-state published minimality.
- A globally verified free sparse DFAO with fewer states falsifies the stronger
  unrestricted target.
- A satisfying assignment to a relaxed CNF is only a search candidate. It is a
  falsifier only after decoding and global verification.
- One published machine that does not satisfy a proposed formula invalidates
  the formula's model-to-SAT theorem and therefore invalidates any lower bound
  based on that formula.

## Current claim boundary

The semantic and proof-carrying infrastructure is formalized. No concrete CNF,
LRAT refutation, verified 22-state upper table, or new numerical lower bound is
claimed by this registry entry.
