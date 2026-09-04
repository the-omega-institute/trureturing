# Golden-ratio sparse DFAO minimality

## 1. Scope

This volume records the mathematical reductions used to study the number of states required to output the base-four digits of the golden ratio from the canonical Zeckendorf encodings of the powers `4^i`.

The arithmetic specification is

\[
w_i = Z(4^i),
\qquad
 d_i = \lfloor 4^{i+1}\varphi\rfloor - 4\lfloor 4^i\varphi\rfloor.
\]

The Lean truth sources for these words and outputs already live in `GoldenBase4AutomataOracle` and `GoldenDFAOMinimalityTargets`. This volume does not introduce a second oracle.

## 2. Three distinct machine classes

The lower-bound problem must distinguish three nested classes.

\[
\mathcal M_{\mathrm{free}}
 = \{M : M(w_i)=d_i\text{ for every }i\},
\]

\[
\mathcal M_{\mathrm{zero}}
 = \{M\in\mathcal M_{\mathrm{free}} : \delta(q_0,0)=q_0\},
\]

\[
\mathcal M_{\mathrm{published}}
 = \{M\in\mathcal M_{\mathrm{zero}} :
     M\text{ respects the Zeckendorf base-state typing and }
     o(q_0)=0\}.
\]

Thus

\[
\mathcal M_{\mathrm{published}}
 \subseteq
\mathcal M_{\mathrm{free}}.
\]

A refutation established under the published zero-loop and zero-anchor conventions excludes only `published` machines unless a separate theorem removes those assumptions. Conversely, any lower bound proved for the wider free typed class automatically applies to the published class.

This boundary is now formalized by:

- `D5/S0/Automata/ZeroInvariantTypedDFAO.lean`;
- `D5/S1/Digit/PublishedGoldenBase4Problem.lean`.

## 3. Finite UNSAT still implies an infinite lower bound

For a finite prefix extent `N`, let

\[
\operatorname{Fits}_N(M)
\iff
\forall i<N,\ M(w_i)=d_i.
\]

Global correctness implies every finite fitting obligation:

\[
\operatorname{Correct}(M)
\Longrightarrow
\operatorname{Fits}_N(M).
\]

Therefore

\[
\neg\exists M\in\mathcal M_{\mathrm{published}},
  |Q_M|\le k\land\operatorname{Fits}_N(M)
\Longrightarrow
\neg\exists M\in\mathcal M_{\mathrm{published}},
  |Q_M|\le k\land\operatorname{Correct}(M).
\]

The finite sample does not need to cover every power. It only needs to be a genuine subset of the infinite specification.

## 4. Exact encodings and refutation encodings

For a mathematical model-existence proposition `P` and a propositional formula `F`, two interfaces must be separated.

An exact encoding proves

\[
P \Longleftrightarrow \operatorname{SAT}(F).
\]

A refutation encoding proves only

\[
P \Longrightarrow \operatorname{SAT}(F).
\]

The second direction is sufficient for a sound lower bound:

\[
P\Longrightarrow\operatorname{SAT}(F),
\qquad
\operatorname{UNSAT}(F)
\Longrightarrow
\neg P.
\]

This matters because a relaxed formula may merge several output symbols, omit totality constraints, or retain other spurious satisfying assignments. Such a formula can still produce a valid UNSAT lower bound. It cannot turn a SAT assignment into a verified DFAO without an additional SAT-to-model theorem.

The distinction is frozen in `D5/S0/Certificates/RefutationEncoding.lean`.

## 5. Stable right colorings as a structural relaxation

Let `P(S)` be the finite family of prefix occurrences in a labeled sample. Any deterministic typed machine induces a color map

\[
c : P(S)\to Q.
\]

It satisfies:

1. all empty-prefix occurrences receive the start color;
2. equal prefix words receive the same color;
3. if two parent prefixes have the same color, then equal-symbol extensions have the same color;
4. terminal prefixes with the same color have the same output;
5. prefixes with the same color induce the same state of the underlying Zeckendorf validity automaton.

These are the finite right-congruence constraints visible before one commits to a particular SAT variable layout. They form a relaxation of exact identification:

\[
\operatorname{Identification}(S,Q)
\Longrightarrow
\operatorname{StableRightColoring}(S,Q).
\]

Consequently

\[
\neg\operatorname{StableRightColoring}(S,Q)
\Longrightarrow
\neg\operatorname{Identification}(S,Q).
\]

The construction and the refutation implication are formalized in `D5/S0/Automata/TypedStableRightCongruence.lean`.

## 6. Corrected published-class certificate chain

The trusted lower-bound chain is now

\[
\boxed{
\begin{aligned}
&\text{published global machine}\
&\Longrightarrow\text{published finite-prefix model}\
&\Longrightarrow\text{satisfying assignment of a refutation encoding}\
&\xrightarrow{\text{kernel-checked LRAT contradiction}}\bot.
\end{aligned}}
\]

The corresponding Lean endpoint is `PublishedGoldenDFAStateLowerBound.no_global_model_at_most_of_prefix_refutation`.

A verified 22-state published upper machine and a refutation for all published machines with at most 21 states imply exact 22-state minimality inside the published class.

## 7. Current research boundary

This sprint changes the semantic and proof-theoretic boundary. It does not claim a new numerical state bound.

The next evidence-producing stage is:

1. reconstruct the published finite dictionary, including the zero anchor;
2. generate a one-way refutation encoding for every allowed type split;
3. prove that every published finite-prefix model satisfies the formula;
4. generate LRAT or another kernel-checkable contradiction certificate;
5. first reproduce the known at-most-14 exclusion;
6. then test budgets 15 through 21.

Any SAT result remains a candidate until its four-valued outputs and global correctness are independently verified. Any UNSAT result becomes a theorem only after the model-to-SAT implication and the proof certificate have both been checked.
