---
slug: nepomechie-raveh-2024-qutrit-dicke-pruning-refutation
bibkey: nepomechieraveh2024quditdicke
doi: 10.26421/QIC24.1-2-2
url: https://arxiv.org/abs/2301.04989v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/PureState/QutritDickePruningRefutation.result
---

# The proposed pruning ranges do not prepare every qutrit Dicke state

## Problem

Rafael I. Nepomechie and David Raveh, *Qudit Dicke state preparation*, Quantum Information and Computation 24 (2024), 37–56, arXiv:2301.04989v4, §4.5, “Simplifying the circuit”, propose occupation-dependent ranges for deleting gates from their qutrit circuit. The v4 source `qdit_v3.tex` (md5 `fcb86a69ac9cdb2a7353251021ea3983`), line 1006, introduces the formulas labelled `W3genericsimple`, `W3specialsimple` and `kkdefs`:

> we conjecture that, similarly to the $d=2$ case \eqref{W2explicit2},

Line 1031 states:

> We have not yet succeeded to prove the result \eqref{W3genericsimple}-\eqref{kkdefs}, which we found through experimentation.

The reading fixed in issue [#21375](https://github.com/the-omega-institute/trureturing/issues/21375) is the following universal preparation identity: for every natural $n\ge2$ and all natural occupations $k_0,k_1,k_2$ with $k_0+k_1+k_2=n$, the specified pruned circuit maps $|\mathrm e(\vec k)\rangle=|0\rangle^{\otimes k_0}|1\rangle^{\otimes k_1}|2\rangle^{\otimes k_2}$ to $|D^n(\vec k)\rangle$.

More precisely, put $l_1=k_1+k_2$, $l_2=k_2$, and $\tilde k=k_2$ if $k_0=0$, otherwise $\tilde k=\max(k_1,k_2)$. The ranges in that reading are inclusive:

- The single-index product retains $\mathrm I_{m,l}$ for $\max(\tilde k+m-n,1)\le l\le\min(\tilde k,m-1)$, applied in increasing $l$.
- The double-index product retains $\mathrm{II}_{m,a,b}$ for $\max(l_2+m-n,1)\le b\le\min(l_2,m-2)$ and $\max(l_1+m-n,b+1)\le a\le\min(l_1,m-1)$, applied with increasing $b$ and increasing $a$ within each $b$.
- Each $\mathcal W_m$ applies the single-index product before the double-index product; $\mathcal U_n$ applies the blocks in time order $n,n-1,\ldots,2$, each on the leftmost $m$ qutrits. Empty ranges contribute the identity.

These are `prunedTilde`, `prunedTildeTilde`, `prunedW` and `prunedU`. The universal equality is `claim`; it is refuted. The definitions and source locators are also documented in [the literature note](../Library/QuantumContext/nepomechieraveh2024quditdicke.md).

## Motivation

Deleting gates for a fixed occupation can reduce the resources needed to prepare a Dicke state. The source makes the intended benefit explicit in `qdit_v3.tex`, line 1046:

> The size and depth of the simplified circuit $\mathcal{U}_n(n-l_1,l_1-l_2,l_2)$ is therefore ${\cal O}(l^2 n)$.

That sentence follows the regime $l_1\sim l_2\equiv l\ll n$ and the gate-count formulas at lines 1037–1046. Correctness of the pruned circuit is required to interpret its gate count as the cost of a preparation algorithm.

## Gap

The bounded literature check is recorded in #21375:

- The v4 source retains the explicit conjecture and the statement that it was found experimentally and remains unproved.
- The preregistration reports 12 citing works in OpenAlex and screening of 21 Semantic Scholar citing records. It identifies follow-ups arXiv:2308.08392v2, 2408.04729v2, 2507.13308v2, 2506.10185 and 2606.24659 without a proof, refutation or correction of the pruning ranges.
- The reported web, Zenodo, MathDB, google-deepmind/formal-conjectures and repository searches found no settlement or existing record of this problem.

`not-found-in-searched-scope`. The source quotation is checked against the v4 TeX; the other search readings remain attributed to the preregistration.

## Route

Fix $n=5$ and $k=(1,3,1)$. Write $\delta_w$ for the unit amplitude at a word $w$, and $P_{r,a}f$ for restriction of an amplitude function to words whose wire $r$ has letter $a$. Wires increase from right to left, so the input is $u=|01112\rangle$, the intermediate branch is $b=|11120\rangle$, and the separating word is $v=|21110\rangle$. Their wire-order lists, starting with wire zero, are respectively $[2,1,1,1,0]$, $[0,2,1,1,1]$ and $[0,1,1,1,2]$.

1. **The five-wire block.** For precisely this occupation and input, `i53_input` proves $\mathrm I_{5,3}\delta_u=\delta_u$. The private lemma `project_w5` proves $P_{0,0}(\mathcal W_5\delta_u)=\delta_b/\sqrt5$, with $\mathcal W_5=\mathrm{II}_{5,4,1}\mathrm I_{5,3}$ embedded in the five-wire register.
2. **The four-wire block.** For this same occupation and the specific input $\delta_b$, `w4_branch` proves $\mathcal W_4\delta_b=\delta_b$. It uses `i42_branch`, `i43_branch` and `ii431_branch`, each of which fixes that particular $\delta_b$, for $\mathcal W_4=\mathrm{II}_{4,3,1}\mathrm I_{4,3}\mathrm I_{4,2}$. For every $f:\mathrm{State}\,5$, `project_w4` proves $P_{0,0}(\mathcal W_4 f)=\mathcal W_4(P_{0,0}f)$; for every real scalar $c$ and every such $f$, `w4_scale` proves $\mathcal W_4(cf)=c\mathcal W_4f$. Consequently the restriction after the first two blocks is still $\delta_b/\sqrt5$.
3. **The remaining blocks.** For every natural wire index $r\le1$, every letter $a:\mathrm{Fin}\,3$, and every $f:\mathrm{State}\,5$, `project_tail` proves that $P_{r,a}$ commutes with the specific composition $\mathcal W_2\mathcal W_3$ for $k=(1,3,1)$ in the five-wire register. For every $f:\mathrm{State}\,5$ satisfying $f(t)=0$ whenever wire zero of $t$ is zero and wire one is not two, `tail_zero` proves $(\mathcal W_2\mathcal W_3 f)(v)=0$. For $f=\mathcal W_4\mathcal W_5\delta_u$, the restriction in item 2 implies exactly this hypothesis. Thus `output_zero` proves that the full pruned output at $v$ is zero for the fixed witness.
4. **The Dicke coefficient.** For precisely $n=5$, $k=(1,3,1)$ and $v$, `target_value` proves $D(v)=1/\sqrt{20}$ and `target_nonzero` proves $D(v)\ne0$. Applying `claim` to the natural counts $1,3,1$, whose sum is five, and evaluating at $v$ contradicts these two coefficient readings. This is `result : ¬ claim`.

## Falsifier

The counterexample would not address the source conjecture if the formal gates, product order or target amplitudes encoded a different circuit. The relevant identifications are:

- `State n` is the space of real amplitude functions on maps $\mathrm{Fin}\,n\to\mathrm{Fin}\,3$; its type imposes no normalization condition. `vertexDelta` supplies the unit input. The real-coordinate reading is appropriate because the specified exchanges and rotations have real entries, as displayed in the source's elementary gates and Appendix A.
- `controlledX` exchanges the two target letters when all listed controls hold. For distinct target letters, `controlledR` has rows $(c,-s)$ and $(s,c)$ on that two-letter subspace. The definitions `V` and `II` use the circuits at source lines 598–696 and 736–881, with the square-root cosines and negative square-root sines of `ugate` and `angles`. They include the boundary omissions of predecessor controls; the last-wire control in `V` is present exactly when its lower letter is positive and $l\le m-2$.
- Within $\mathrm I_{m,l}$, the formal time order of the letter pairs is $(0,1),(0,2),(1,2)$. Within each double-index product it is increasing $b$, then increasing $a$. The formal refutation uses these orders; the computations below separately test the twelve combinations of the six pair orders and two index nesting orders at the witness.
- `initialWord` places twos on the rightmost $k_2$ wires, then $k_1$ ones, then zeros. `dicke` assigns $1/\sqrt{n!/(k_0!k_1!k_2!)}$ exactly to words with those three multiplicities and zero elsewhere. Its factorial quotient is computed in the natural numbers before conversion to a real number. At the witness this quotient is exactly 20.

These are source-to-definition identifications, not an additional Lean theorem equating an external circuit implementation with the formal definitions.

## Evidence

The canonical source is `D5/S3/Quantum/PureState/QutritDickePruningRefutation.lean` (388 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/PureState/QutritDickePruningRefutation.lean.json`, statement `sha256:9c53e163dd709c68abbe1063646a0281a8ebfb589ea276dd01372844556b8749`.

Declaration statements:

- `result`: `sha256:6d44e97f8d80e077b05fdeeb701bdbd599fa31e9a8f21b2010bf04e827cf7795`;
- `claim`: `sha256:31442c99982201730dda2ad261744e7895ffc8e5dde917a3ea30c7845978faa8`.

## Triage

Tier 1: an explicitly stated, experimentally motivated conjecture of a 2024 journal paper, preregistered in issue #21375 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every natural $n\ge2$ and all natural counts $k_0,k_1,k_2$ summing to $n$, the specified `prunedU` maps the unit amplitude at `initialWord` to `dicke`.

**Computed, not formalized** (the orchestrator's exact SymPy simulation, written from the TeX gate definitions without the authors' notebook; #21375 records it):

- For $n=5$, $k=(1,3,1)$, the pruned output differs from the Dicke target exactly at the four words in the table below. The other sixteen sector coefficients agree.
- The same pruned output arises under all twelve combinations of the order of the $V$ gates in $\mathrm I$ and the index nesting in $\mathrm{II}$.
- On the retained branch, $\mathrm I_{4,1}|11120\rangle=(\sqrt3/2)|11210\rangle+(1/2)|11120\rangle$. Inserting $\mathrm I_{4,1}$ before $\mathrm I_{4,2}$ and $\mathrm I_{4,3}$ in $\mathcal W_4$ makes the output of this circuit equal to the Dicke target.
- The unpruned circuit gives the Dicke target for $(1,3,1)$, $(2,2,1)$ and $(1,2,2)$ at $n=5$.
- For $2\le n\le6$ and every occupation, the pruned circuit fails only at $(1,3,1)$ and $(1,4,1)$.

| word | pruned amplitude | Dicke amplitude |
| --- | --- | --- |
| $\lvert21110\rangle$ | $0$ | $1/\sqrt{20}$ |
| $\lvert12110\rangle$ | $0$ | $1/\sqrt{20}$ |
| $\lvert11210\rangle$ | $0$ | $1/\sqrt{20}$ |
| $\lvert11120\rangle$ | $1/\sqrt5$ | $1/\sqrt{20}$ |

**Argued, not formalized.**

- *Missing structure.* The fixed global parameter is $\tilde k=3$. At $m=4$ its lower cutoff is $\max(3+4-5,1)=2$, so it removes $\mathrm I_{4,1}$. Yet the specific branch $|11120\rangle$ has residual occupation $(0,3,1)$ on the four active wires. Applying the piecewise occupation rule to that residual problem would select $\tilde k=1$, rather than the global value three. The global cutoff does not account for this change from three occupied letters to two. The computed action of the omitted gate exhibits the redistribution that is lost.
- *A sufficient deletion criterion.* For a specified input and an ordered gate list, require each deleted gate to fix the intermediate state produced by its preceding gates. Induction on the gate list proves that the shortened and original circuits then have identical intermediate states at every retained gate, and hence identical outputs. Verifying this condition on every reachable residual branch is sufficient. A general branch-aware range satisfying it remains open here; the single-instance repair above supplies no such classification.
- *A surviving special case.* For natural $n\ge2$, the three occupations $(n,0,0)$, $(0,n,0)$ and $(0,0,n)$ make all retained gate ranges empty. In the first two cases $\tilde k=0$ and $l_2=0$; in the third $\tilde k=l_2=n$, so each lower bound exceeds its upper bound for $2\le m\le n$. The input is the unique word of its occupation and its multinomial coefficient is one. Thus the definitions give the required homogeneous Dicke state in these cases. This argument is not a compiled theorem of the module.
- *Effect on the source.* The gate-count expressions at lines 1037–1046 can describe the specified gate list, but they do not establish the cost of a correct preparation algorithm for every occupation. The discussion's simplified qutrit preparation assertion at lines 1201–1204 therefore needs restriction or correction. The unpruned constructions and the separate qubit pruning result are outside `claim`; the refutation does not negate them. The general-$d$ pruning expectation at lines 1133–1135 also remains unresolved, including whether a corrected algorithm can achieve its proposed resource scale.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches reported in #21375 and does not establish exhaustive worldwide novelty or priority. The OpenAlex and Semantic Scholar listings, the five follow-ups named above, the arXiv version-change reading, and the web, Zenodo, MathDB, formal-conjectures and prior-repository search readings were not independently reproduced. The source reading here is the v4 TeX, not the supplementary Cirq notebook or a comparison of all arXiv versions. The agreement with the authors' notebook reported in #21375 is seat-reported and was not reproduced.

The source-to-definition correspondence is a textual identification, not a compiled equivalence with the paper or its notebook. The statements under “Computed, not formalized” and “Argued, not formalized” are outside the formal conclusion of `result`. In particular, alternate-order robustness, the repaired witness circuit, correctness of the unpruned circuit, the small-$n$ scan, the homogeneous special cases and a general safe pruning rule are not additional formalized conclusions of this module. Correctness of a revised range for arbitrary occupations and its resource bounds remain open here.
