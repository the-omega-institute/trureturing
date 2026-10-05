---
slug: lee-kjoshanssen-2026-quantum-cerny-thue-morse
bibkey: lee2026quantumcerny
doi: null
url: https://arxiv.org/abs/2609.40154
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.result
---

# The Thue–Morse prefix 01101001 has quantum Černý complexity 3, not 2

## Problem

Lee, Lee and Kjos-Hanssen, *Quantum Černý complexity of binary words*,
arXiv:2609.40154v1, define the quantum Černý complexity $\mathrm{qc}(w)$ as the
least $d$ for which two quantum channels on $d\times d$ density matrices and a
start state make $w$ the unique shortest synchronizing word (Definition 1.1).
Open problem 1 reads

> (Thue--Morse prefix.) We conjecture $\qc(01101001)=2$; the bound
> $\qc(01101001)\le3$ follows from Theorem~\ref{thm:kmp}.

Issue #13185 fixes the reading: channels and density matrices are the frozen
`QuantumChannel (Fin d) (Fin d)` and `DensityState (Fin d)`, letters act left
to right, the reachable set is the set of images of the start state, and
`qc w = sInf {d | 1 ≤ d ∧ some instance of dimension d has w as its unique
shortest synchronizing word}`.

## Motivation

The conjecture is the first item of the paper's open problems and the test case
for its question which words have $\mathrm{qc}(w)=2$.
`D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.result` proves
that it fails.

## Gap

Issue #13185 records the literature check: the paper has a single version; the
authors' Lean formalization proves only $\mathrm{qc}(01101001)\le3$ and leaves
the conjecture open; no other source on quantum Černý complexity was found.
`not-found-in-searched-scope`.

## Route

1. **Linearization.** For an instance let $V$ be the complex span of the
   differences of reachable states. A word synchronizes iff the linear map of
   its channel vanishes on $V$; both channels map $V$ into itself; the
   differences have trace zero, so $\dim V\le3$ for a qubit.
2. **Dimension lemma.** For linear maps $f_0,f_1$ of a space of dimension at
   most 3 over any field, write $M_u$ for the map of the word $u$. If
   $M_{01101001}=0$, then one of $M_{01101}$, $M_{01001}$, $M_{1101001}$,
   $M_{0110100}$ vanishes. The image of $M_{01101}$ lies in that of $M_{01}$,
   and equality would kill $M_{01001}$; so $\operatorname{rank}M_{01}>
   \operatorname{rank}M_{01101}\ge1$. If $f_0$ were surjective, $M_{1101001}$
   would vanish, so $\operatorname{rank}M_{01}\le\operatorname{rank}f_0\le2$,
   hence $\operatorname{rank}M_{01}=2$. The image of $M_{01}$ lies in that of
   $f_1$, and equality would kill $M_{1101001}$; so $f_1$ has rank 3, is
   injective, and $M_{0110100}=0$.
3. All four words are shorter than $01101001$, so none can synchronize in a
   qubit instance where $01101001$ is the unique shortest synchronizing word.
   Hence no qubit instance exists, the set defining $\mathrm{qc}$ omits 2, and
   $\mathrm{qc}(01101001)\ne2$.

## Falsifier

The proof would fail if a qubit instance had a difference space of dimension
larger than 3, or if a vanishing word map on that space did not make the word
synchronize.

## Evidence

Numerical check (issue #13185): least-squares solutions of $M_w=0$ for random
$3\times3$ real pairs have some other word of length at most 8 with norm below
$3\cdot10^{-8}$ in 4000 starts; positive controls with known $\mathrm{qc}=2$
($0110$, $01110$, $011110$) reach 0.157, 0.073, 0.052.

The canonical source is
`D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.lean`. Its public
declarations are `applyWord`, `reachable`, `Synchronizing`,
`UniqueShortestSync`, `HasInstance`, `qc`, `thueMorsePrefix`, `claim`,
`wordComp`, `mortal_thueMorse` and `result`; channels and states are the frozen
`QuantumChannel` and `DensityState` of
`D5/S3/Quantum/Foundation/FiniteStateChannel`.
The frozen module state has statement identity
`sha256:332066d32976fe43b4d932486582f8aff11487760096971ac14ea35547c4c5b3`.
The result declaration has statement identity
`sha256:1d759bb72185a8c08110b5869149d68f0cd2f72ef41a26cceaffa530c8886d76`.
The Freeze event is
`sha256:2103075b0f2102e23cbebd0493ebe987ad4e0dc65745108c5fbb2ce52e0d5f0e`.
Its project-level frozen prerequisite is the Freeze event of
`D5/S3/Quantum/Foundation/FiniteStateChannel`
(`sha256:551ef7395f6a8461b4286652103c87fdc6c29b05f249630b04ea95ac06bbb10c`).
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (open problem 1 of a 2026 paper),
preregistered in issue #13185 before any Lean. `theorem`; resolution
`refuted`. The public theorem has `proof_shape: content`; its escape witness is
the dimension lemma `mortal_thueMorse`. Admission basis
`open-problem-resolution`; utility `none`.

What the refutation shows beyond the single word:

- **Value (proved in the paper and here).** With the paper's upper bound
  $\mathrm{qc}(w)\le\lceil\sqrt{|w|+1}\,\rceil=3$, the value is
  $\mathrm{qc}(01101001)=3$. The upper bound is proved in the paper and in the
  authors' Lean files; it is not formalized here.
- **Mechanism (proved).** A qubit gives a difference space of dimension at most
  3. The prefix $01$ recurs at positions 4–5, and this recurrence, together with
  the first letter $0$ and the last letter $1$, forces both letters to act
  bijectively or to make a shorter word synchronize.
- **Family (argument given here, not formalized).** The same three steps apply
  to every word $w$ that starts with $01$, ends with $1$, and contains $01$
  again at positions $j,j+1$ with $j\ge3$ and $j+1<|w|$. With $P$ the map of
  the prefix ending at $j+1$, $Q=M_{01}$ and $z=w_{j+2}\cdots w_{|w|}$, equal
  images of $P$ and $Q$ would make $01z$ synchronize. A surjective $f_0$
  would make $w_2\cdots w_{|w|}$ synchronize. Equal images of $Q$ and $f_1$
  would make $w_2\cdots w_{|w|}$ synchronize. An injective $f_1$ would make
  $w_1\cdots w_{|w|-1}$ synchronize. So all such words have
  $\mathrm{qc}(w)\ge3$, and so do their images under exchanging the letters.
  Examples are $01011$, $010101$ and $0110101$; numerically, least squares
  finds no qubit instance for these words (other-word norms $1.9\cdot10^{-8}$,
  $3.0\cdot10^{-6}$, $5.3\cdot10^{-8}$). For $0111001$, where the second $01$
  ends the word, it finds 0.0034.
- **Effect on the paper's other questions.**
  - Open problem 1 also asks whether all words with at least one alternation
    and no long constant power have $\mathrm{qc}=2$. The word $01101001$ has
    both properties and $\mathrm{qc}=3$, so the answer is no (proved here).
  - Open problem 3 remarks that $\mathrm{qc}(w)=2$ for almost all $w$ would be
    consistent with the results. The family above contains, for random $w$ of
    length $m\to\infty$, a proportion tending to $1/8$, and its letter-exchanged
    copy another $1/8$. So at least a quarter of long words have
    $\mathrm{qc}(w)\ge3$, and almost all words having $\mathrm{qc}=2$ is false
    (by the family argument; not formalized).
  - The paper's other results, the general bounds, $\mathrm{qc}(0^m)$ and
    $\mathrm{qc}(01^n0)=2$, are unaffected.
- **Open.** The characterization of $\{w:\mathrm{qc}(w)=2\}$ remains open.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
