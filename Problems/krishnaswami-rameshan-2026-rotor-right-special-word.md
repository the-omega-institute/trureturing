---
slug: krishnaswami-rameshan-2026-rotor-right-special-word
bibkey: krishnaswamirameshan2026rotor
doi: 10.48550/arXiv.2606.25766
url: https://arxiv.org/abs/2606.25766v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.result
---

# The right-special rotor word is the reversed prefix after the initial zero

## Problem

Govind S. Krishnaswami and Anirudh Rameshan, *Symbol sequences from three-rotor coincidences and their word-complexity*, arXiv:2606.25766v1 [nlin.CD] (2026), §5.3.1, “Conjecture on right-special word”, state:

> we conjecture that the $(n-1)$-word that branches (in two ways) coincides with the unique $n$-word starting with 0 read backwards (excluding the 0).

This is a verbatim excerpt from line 701 of the downloaded v1 TeX `3rotor-symb-dyn.tex`, md5 `5d78bd4b19257909d542bbe5b1469202`. The surrounding scope is UHE quasiperiodic trajectories starting at the origin with irrational slope $\sigma>1$ (line 663). Discussion question (1), line 917, explicitly asks for a settlement. The source specifies its encoding in §5.3.4, line 835:

> Given a Sturmian sequence $s_1 s_2 s_3 \cdots$, the corresponding rotor sequence is $02 s_1 2 s_2 2 s_3 2 \cdots$.

Issue [#20821](https://github.com/the-omega-institute/trureturing/issues/20821) fixes the formal reading. For $m\ge1$, define $s_m=3$ exactly when $m=\lfloor k\sigma\rfloor_{\mathbb N}+k$ for some natural $k\ge1$, and $s_m=1$ otherwise. Here $\lfloor\cdot\rfloor_{\mathbb N}$ is the natural-valued floor used by `cutting`. Define $R_0=0$, $R_{2j-1}=2$ and $R_{2j}=s_j$ for $j\ge1$, as in `rotor`.

A finite list $w$ of natural symbols is a factor when $w_t=R_{i+t}$ for some natural starting position $i$ and every $t<|w|$. It is right-special when $wa$ and $wb$ are factors for two distinct natural symbols $a\ne b$; the occurrences may start at different positions. These are `IsFactor` and `IsRightSpecial`.

The claim is: for every irrational real $\sigma>1$, every natural $n\ge2$, and every finite list $w$ of length $n-1$,

$w\text{ is right-special in }R\quad\Longleftrightarrow\quad w=\operatorname{reverse}(R_1R_2\cdots R_{n-1}).$

This reading is proved. The [literature note](../Library/Rewriting/krishnaswamirameshan2026rotor.md) gives the source quotations and locators.

## Motivation

The source uses rotor-coincidence sequences to study the word statistics of three-rotor dynamics. Its proposed rule identifies the branching factor directly from the distinguished initial trajectory, rather than only counting factors. The settlement supplies that identification at every positive word length for the specified irrational cutting sequence and separator encoding.

## Gap

Issue #20821 records the literature check before any Lean:

- the orchestrator reported that the arXiv abstract page listed only v1, which retains the conjecture and Discussion question (1);
- the orchestrator's web searches for the paper, rotor sequences and right-special conjecture returned the source only;
- the orchestrator's Zenodo query for “three-rotor” and “right-special” found no relevant record, and its OpenAlex title search found no indexed record;
- the orchestrator's repository issue search for the arXiv identifier found no record on dev.

`not-found-in-searched-scope`.

The issue identifies characteristic Sturmian prefixes and reversal as known ingredients. The missing identification is their transfer to the rotor encoding with its initial zero and alternating separators. The bounded search readings are attributed reports, not an exhaustive novelty claim.

## Route

1. **Arithmetic identification.** Put $\alpha=1/(\sigma+1)$. Then $\alpha$ is irrational and $0<\alpha<1$. The helper `cutting_mechanical` identifies $s_{j+1}$ with the Boolean lower mechanical word of slope and intercept $\alpha$, relabeled by $\mathrm{false}\mapsto1$ and $\mathrm{true}\mapsto3$. Its mechanical letter is $\lfloor(j+2)\alpha\rfloor-\lfloor(j+1)\alpha\rfloor$. The identification uses a Beatty floor-jump equivalence and $\lfloor k(\sigma+1)\rfloor_{\mathbb N}=\lfloor k\sigma\rfloor_{\mathbb N}+k$.
2. **Both extensions of the reversed prefix.** For a mechanical prefix of length $m$, choose $\varepsilon>0$ preserving the finitely many floors $\lfloor-q\alpha\rfloor$ for $1\le q\le m+1$ under subtraction by $0\le\delta<\varepsilon$. At intercept $-(m+1)\alpha-\delta$, the first $m$ letters reverse that prefix, using $\lfloor-q\alpha\rfloor=-\lfloor q\alpha\rfloor-1$. Taking $\delta=0$ gives final bit true; taking $\delta=\min(\varepsilon,1-\alpha)/2$ gives false. The reused `MechanicalSubshiftIntercept.lowerMechanicalFactor_mem_factorSet` transfers both factors to intercept $\alpha$.
3. **Uniqueness survives encoding.** A nonempty right-special rotor factor cannot contain the unique zero and must end in 2: every other symbol has forced successor 2. Deleting separators projects such a factor of length $\ell$ to a right-special mechanical factor of length $\lfloor\ell/2\rfloor$. The reused `MechanicalRightSpecial.exists_unique_lower_mechanical_right_special` makes the projection unique. Its mechanical letters and the parity of $\ell$ reconstruct the rotor word uniquely.
4. **Identification.** Reverse $R_1\cdots R_\ell$. Each of the two mechanical extensions constructed above lifts to a rotor extension by 1 or 3. More precisely, a mechanical occurrence starting at $k$ lifts to the rotor start $i=2k+2-(\ell\bmod2)$. This supplies existence; uniqueness supplies the forward implication of `claim`. Taking $\ell=n-1>0$ gives `result : claim`.

## Falsifier

The settlement would miss the source conjecture if the crossing index, initial condition, encoding or factor convention differed.

- At the $k$th vertical crossing of $y=\sigma x$, there have been $\lfloor k\sigma\rfloor$ horizontal crossings and $k$ vertical crossings. Irrationality excludes simultaneous positive crossings. Thus the positive crossing index is exactly the criterion in `cutting`, with 3 for vertical and 1 for horizontal crossings, matching TeX line 831.
- The encoding is the source's quoted correspondence. Its zero occurs only at position zero, so the unique length-$n$ factor beginning with zero is the initial prefix. Deleting zero and reversing is exactly the list in `claim`.
- `IsFactor` uses occurrences in the infinite one-sided sequence, not in a finite sample. `IsRightSpecial` requires two genuinely distinct symbols and occurring extensions.

The crossing interpretation is an explicit mathematical bridge to the paper; the Lean module does not model the three-rotor differential equations or their UHE limit.

## Evidence

The canonical source is `D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.lean` (497 lines).

- **Proof.** It proves `result : claim`. A scratch file importing the module checks the compiled definitions and the exact application `example : claim := result`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. The imported `#print axioms result` reports precisely those three axioms; the source scan for the prohibited forms has no matches.

Frozen state: `Golden/Frozen/state/D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial.lean.json`, statement `sha256:57fdce1001e205b8920be809450d9bd12ee42ef1d05448e9900beb454235cb13`.

Declaration statements:

- `result`: `sha256:ab76a48e763fb675ce4f7224405ed0b13ee7b18a6ae2cef82b611a00b3410a5e`;
- `claim`: `sha256:581e720fe5b196a4a488b8c7d6309a2bb34c45ae2cce1eab790a92045f8b4eb6`.

## Triage

Tier 1 conjecture of a 2026 preprint, listed by its authors as Discussion question (1), preregistered in issue #20821 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every irrational real $\sigma>1$, every natural $n\ge2$ and every finite list $w$ of natural symbols of length $n-1$, $w$ is right-special in `rotor` precisely when it is the reversal of that sequence's entries at positions 1 through $n-1$.

**Argued, not formalized.**

- *Decisive mechanism.* The negative-intercept construction preserves the entire reversed prefix while changing its next bit across a single floor boundary. Intercept independence realizes both choices in the original mechanical language. Separators preserve those two choices and force every branching factor to project to the unique mechanical branching factor. Thus complexity supplies uniqueness, while the distinguished prefix and floor reflection supply the identity of that word.
- *Exactly two branches and complexity.* Every occurring factor has a successor because the sequence is infinite. A factor containing zero occurs only at the initial position and therefore has one successor. A nonempty factor ending in a symbol other than 2 has forced successor 2. A factor ending in 2 can be followed only by 1 or 3. Consequently, the unique right-special factor furnished by `result` has exactly these two extensions; every other factor has one. If $C_\ell$ counts all length-$\ell$ factors, partitioning length-$(\ell+1)$ factors by their length-$\ell$ prefixes gives $C_{\ell+1}=C_\ell+1$ for $\ell\ge1$. The case $n=2$ gives both 21 and 23 as factors, so all four symbols occur and $C_1=4$. Hence $C_\ell=\ell+3$ for $\ell\ge1$. These counts and the assertion of exactly two extensions are not the statement of `result`.
- *Irrationality boundary.* At $\sigma=2$, the arithmetic criterion is $m=3k$, so the defined sequence is $0(212123)^\infty$. Each length-6 window in the periodic tail determines its phase, because each period contains a single 3. It therefore has a unique successor. The sole length-6 word containing zero also has a unique successor. Thus the proposed extension to all real slopes greater than one is false for this arithmetic encoding. Actual rational trajectories in the source can have repeated triple coincidences and require their own encoding.
- *Origin anchoring.* For $\sigma=\sqrt2$ the cutting sequence begins $s=1313113\cdots$. Drop its first crossing and encode $s'=s_2s_3\cdots=313113\cdots$ in the same way, giving $R'=0232123212123\cdots$; the prescription for $n=3$ proposes $32$. Successive vertical crossings are separated by at least one horizontal crossing since $\sigma>1$, so the cutting sequence has no factor $33$, and in $R'$ the word $32$ has the single successor 1. The displayed prefix of $R'$ contains both $121$ and $123$, so $12$ is right-special. Thus shifting the cutting sequence need not preserve the reversed-prefix prescription, even though branching in the tail remains. Intercept-independent factor languages alone do not identify an arbitrary starting prefix as special.
- *Transport and neighbouring questions.* An injective renaming of all four symbols preserves occurrences, distinct extensions, reversal and equality: applying the renaming to an occurrence gives an occurrence, and injectivity recovers its original letters. The corresponding renamed characterization therefore follows. Realizing other slopes by the source's rotor permutations, identifying special factors for general intercepts, and relating the coding to finite-energy trajectories are outside the compiled theorem.
- *Effect on the source.* The settlement answers Discussion question (1) for the origin-based encoding and slopes specified in `claim`, and the two-branch argument above supplies the branching premise of TeX line 697. The source already derives $C_n=n+3$ independently from Sturmian counts at lines 827–851; the settlement identifies the branching word and gives another route to that count. It also supplies the uniqueness premise used in the grammar discussion at lines 799–803. It does not by itself prove that no finite list of grammar rules suffices, or formalize the source's non-SFT conclusion. The word-frequency, chaotic-band, periodic-orbit and finite-energy questions listed in Discussion (2)–(6) remain outside this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check recorded in #20821 does not establish exhaustive worldwide novelty or priority. The web, Zenodo, OpenAlex, arXiv version-history and repository-search readings above were reported by the orchestrator and were not independently rerun. The textbook ingredients attributed in that issue to Lothaire and Berstel–Séébold were not independently read here.

The v1 TeX conjecture, its context, the cutting-sequence correspondence and the cited Discussion and grammar passages were read directly. The authors' reported numerical checks and grammar-rule enumeration were not reproduced. All arguments in “Argued, not formalized”, the geometric interpretation of the arithmetic crossing index, the physical UHE correspondence, rotor-permutation transport, word-complexity counts, frequency claims and non-SFT claims are not formalized by `result`. No statement here verifies the finite-energy rotor dynamics or settles the source's other Discussion questions.
