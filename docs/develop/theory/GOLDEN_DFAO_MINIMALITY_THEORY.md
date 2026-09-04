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
&\text{published global machine}\\
&\Longrightarrow\text{published finite-prefix model}\\
&\Longrightarrow\text{satisfying assignment of a refutation encoding}\\
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

## 8. Binary Zeckendorf first-return decomposition

The binary Zeckendorf validity automaton has two base states:

\[
B_0=\text{previous digit zero},
\qquad
B_1=\text{previous digit one}.
\]

Its legal transitions are

\[
B_0\xrightarrow{0}B_0,
\qquad
B_0\xrightarrow{1}B_1,
\qquad
B_1\xrightarrow{0}B_0,
\]

and there is no legal transition from `B_1` on input `1`.

Every legal word beginning at `B_0` therefore has a unique first-return factorization

\[
w=b_1b_2\cdots b_m e,
\]

where

\[
b_j\in\{0,10\},
\qquad
e\in\{\epsilon,1\}.
\]

Equivalently,

\[
L(B_0,B_0)=\{0,10\}^{*},
\qquad
L(B_0,B_1)=\{0,10\}^{*}1.
\]

The return blocks are denoted

\[
A:=0,
\qquad
J:=10.
\]

This is a prefix-code factorization, so compression and expansion are mutually inverse on legal words. It permits the two-type automaton to be studied through an induced system acting only on the `B_0` state fiber, together with one terminal channel for words ending in `1`.

## 9. Transient-type signature quotient

Let a typed partial DFAO have state fibers

\[
Q_0=\{q:\tau(q)=B_0\},
\qquad
Q_1=\{r:\tau(r)=B_1\}.
\]

For a transient state `r` in `Q_1`, the only legal continuations are the empty word and words beginning with `0`. Its complete legal-continuation behavior is therefore determined by the signature

\[
\sigma(r)
=
\bigl(o(r),\delta(r,0)\bigr)
\in O\times \operatorname{Option}(Q_0).
\]

Two `B_1` states with the same signature are indistinguishable on every legal continuation. They may be merged without changing the output on any legal word.

For `q` in `Q_0`, define

\[
A(q)=\delta(q,0),
\]

and, when the one-transition is defined,

\[
S(q)=\sigma(\delta(q,1)).
\]

Writing

\[
S(q)=(g(q),J(q)),
\]

identifies `g(q)` as the output observed when a legal word terminates in `1`, and `J(q)` as the return target after the block `10`.

The behavior of the original typed machine on all legal words is determined by

\[
\bigl(Q_0,q_0,o_0,A,S\bigr).
\]

A canonical reconstruction uses one transient state for each distinct defined signature in the image of `S`. Hence every finite typed machine admits a legal-language-equivalent canonical machine with state count

\[
\boxed{
|Q_0|+|\operatorname{im}S|.
}
\]

For a machine with original fibers `Q_0` and `Q_1`,

\[
|\operatorname{im}S|\le |Q_1|,
\]

so canonicalization never increases the number of states:

\[
|Q_0|+|\operatorname{im}S|
\le
|Q_0|+|Q_1|.
\]

A state-minimal typed machine can therefore be chosen so that the signature map on its reachable `B_1` states is injective.

This reduction is stronger than splitting a SAT search by the two raw type cardinalities. It eliminates the transient type as an independent state-search space and replaces it by the number of distinct output-return signatures actually required by the recurrent skeleton.

## 10. Weighted first-return minimization

The typed state-minimization problem can be restated as a weighted minimization problem on the induced `B_0` skeleton:

\[
\boxed{
 m
 =
 \min
 \left\{
 |Q_0|+|\operatorname{im}S|:
 (Q_0,q_0,o_0,A,S)
 \text{ realizes the specification}
 \right\}.
}
\]

For finite samples, the same statement holds with realization restricted to the compressed sample trie. Thus the natural budget is no longer an unstructured color count. It is

\[
\operatorname{cost}(\mathcal K)
=
|Q_0|+|\operatorname{Signatures}(\mathcal K)|.
\]

This suggests a smaller exact encoding:

1. search only for a stable right congruence on recurrent `B_0` prefixes;
2. encode the return actions `A` and `J` on quotient classes;
3. encode terminal outputs on the `B_0` and terminal-`1` channels;
4. charge one transient state per distinct required pair `(g,J)`.

The raw variables for all `B_1` prefix colors and all `Q_1` transition-table entries become unnecessary.

## 11. Exact finite partial-signature completion

Fix a recurrent quotient with class set `C`. Finite sample data may impose partial requirements on transient signatures:

- a full pair `(g,c)` when both terminal output and return target are observed;
- an output-only requirement `g` when a sample terminates after `1`;
- a return-only requirement `c` when a sample continues through `10`;
- no requirement when no one-transition is observed from the class.

Let

\[
P\subseteq O\times C
\]

be the set of distinct fully fixed pairs. Let

\[
R\subseteq O
\]

be the set of output-only requirements and

\[
K\subseteq C
\]

be the set of return-only requirements. Remove requirements already covered by a full pair:

\[
R'=R\setminus\pi_O(P),
\qquad
K'=K\setminus\pi_C(P).
\]

Then the minimum number of distinct transient signatures needed to complete all partial requirements is

\[
\boxed{
 s_{\min}
 =
 |P|+\max(|R'|,|K'|).
}
\]

The lower bound follows because each distinct full pair requires its own signature, while the residual output and return projections require at least `|R'|` and `|K'|` additional pairs. The upper bound pairs residual outputs with residual return classes, then completes any unmatched side using an arbitrary element of the nonempty opposite carrier.

Consequently a fixed recurrent quotient has an exact finite-sample state cost

\[
\boxed{
 |C|+|P|+\max(|R'|,|K'|).
}
\]

This formula removes the transient-signature allocation from the SAT search after the recurrent congruence has been chosen.

## 12. Revised theorem ladder

The next formalization target is a reusable library node rather than a problem-specific CNF.

### M17. `BinaryZeckendorfBlockSkeleton`

Planned path:

```text
D5/S0/Automata/BinaryZeckendorfBlockSkeleton.lean
```

Required declarations and theorems:

1. the block alphabet `zeroReturn` and `oneZeroReturn`;
2. compression and expansion of legal binary Zeckendorf words;
3. mutual inverse laws on legal words;
4. recurrent and transient state fibers of a typed machine;
5. the transient signature `(output, zero-successor)`;
6. extraction of the recurrent skeleton;
7. evaluation agreement between the machine and its skeleton;
8. reconstruction of a canonical typed machine from a skeleton;
9. preservation of anchored zero-loop semantics;
10. the state-count inequality
   \[
   |Q_0|+|\operatorname{im}S|\le |Q|;
   \]
11. existence of a minimal representative with injective reachable transient signatures.

### M18. `FinitePartialSignatureCompletion`

Planned path:

```text
D5/S0/Automata/FinitePartialSignatureCompletion.lean
```

It will formalize

\[
s_{\min}=|P|+\max(|R'|,|K'|)
\]

and use it to define a weighted stable right congruence on the compressed finite trie.

### M19. Known lower-bound replay

After the dictionary evidence is admitted, generate a refutation encoding for the weighted skeleton on the published 79-sample instance and prove

\[
m_{\varphi,4}^{\mathrm{published}}\ge 15
\]

through a kernel-checked certificate.

### M20. First original numerical target

Use exact four-output signatures, weighted recurrent congruence, adaptive sample selection, and certificate-producing solving to test

\[
\boxed{
 m_{\varphi,4}^{\mathrm{published}}\ge 16.
}
\]

A successful refutation would improve the currently reproduced public lower bound. A satisfying assignment would be decoded into a concrete 15-state candidate and checked against a much larger exact oracle before any global claim is considered.

## 13. Claim boundary and novelty status

The first-return factorization follows directly from the two-state binary Zeckendorf validity automaton. Signature merging is a behavioral quotient argument. The weighted state-cost identity and the finite partial-signature completion formula are new deductions within this research lane.

A targeted literature search found standard work on automaton minimization, congruence-based learning, typed automata, and proof-carrying SAT, but did not locate this exact weighted first-return formulation for sparse typed DFAO identification. This is evidence for pursuing the construction, not a definitive novelty claim. A publication-level novelty statement requires a broader bibliographic review and comparison with minimization of partial Moore machines, transducers, induced automata, and return-word automata.

The present section records a research target. No new numerical lower bound is claimed until a concrete finite instance and its proof certificate are replayed in Lean.
