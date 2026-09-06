---
slug: golden-ratio-base4-dfao-minimality
bibkey: barnoffbrightshallit2024using
arxiv_id: 2405.02727
triage: window
motivation_gids:
  - D5/S0/Conventions/WDigits
  - D5/S1/Digit/Carry
  - D5/S1/Digit/Normalize
  - D5/S1/Words/ZeckendorfOrder
  - D5/S1/Words/ZeckendorfBeattyBridge
  - D5/S1/Depth/GoldenContinuedFraction
  - D5/S1/Scale/Fibonacci
---

# Minimality of the base-4 golden-ratio DFAO

## Problem

The paper constructs a DFAO which, on the Zeckendorf representation of `q = b^i`,
outputs the `i`th base-`b` digit of the golden ratio. The full Walnut automaton
is minimal on all valid inputs, but only powers of `b` matter for digit
extraction.

Quoted from arXiv:2405.02727v1:

> “Could it be that there are even smaller automata that answer correctly on
> inputs of the form \(b^i\) (but might give a different answer for other
> inputs)?”

> “We do not know the answer to this question, in general.”

The concrete target is the unresolved base-4 phi instance: prove that the
paper's 22-state Walnut DFAO is minimal among DFAOs which are correct on the
Zeckendorf encodings of all `4^i`, ignore leading zeroes, and obey the
Zeckendorf/Ostrowski validity rules. Equivalently, prove that no such DFAO with
at most 21 states exists.

The paper also says:

> “It is conceivable that the automata produced by our method are indeed minimal
> and unique in general, and we leave this as an open question.”

Minimality of the fixed base-4 instance is narrower and mechanically
falsifiable; uniqueness should remain a separate target.

The paper states the difficulty:

> “The question is likely difficult; in terms of computational complexity, it is
> a special case of a problem known to be NP-hard, namely, the problem of
> inferring a minimal DFAO from incomplete data.”

> “For this reason, \(\varphi\) in base 4 ... encountered prohibitively long
> solving times before the required number of states (22 states ...) could be
> reached, preventing the minimality of the Walnut solutions from being
> determined.”

> “For \(\varphi\) in base 4, it took over 25 hours for the 78'th digit set to
> be declared UNSAT at 13 states...”

The paper explains that both the digit set needed for a candidate and the
representation length of each digit position can be arbitrarily large.

## Motivation

- The input language is exactly the frozen Zeckendorf system; leading-zero
  invariance and the no-adjacent-ones rule can be stated over `WDigits` and
  normalization.
- `GoldenContinuedFraction` and Fibonacci scale give the golden/Ostrowski
  arithmetic that underlies the digit extractor.
- `ZeckendorfOrder` and the Beatty bridge may support exact generation of
  constrained positive and negative examples without floating-point phi.
- The remaining task is automata-theoretic minimality on a sparse input
  language, so the connection is real but one layer farther from existing
  machinery than the other five candidates.

## Gap

- No DFA/DFAO, run semantics, sparse powers language, Myhill-Nerode
  equivalence, or automaton minimization theorem is frozen.
- The actual 22-state Walnut transition/output table must be imported from the
  paper artifact and independently checked.
- No SAT encoding, UNSAT proof checker, or certificate format exists in the
  repository.
- Correctness on every `4^i` is an infinite sparse-language property; matching a
  finite digit dictionary is not enough.

## Route

1. Define the sparse language `L_4 = {zeckendorf(4^i) | i >= 0}` and the target
   output digit function exactly.
2. Verify the 22-state machine on `L_4` using the paper's arithmetic
   construction, separately from minimality.
3. Seek 22 pairwise distinguishable residual configurations: for each pair of
   proposed equivalence classes, exhibit a continuation compatible with some
   power input that forces different output. This would give a checkable
   Myhill-Nerode-style lower-bound certificate without solving a monolithic SAT
   instance.
4. If sparse continuations do not support such a certificate, reproduce the
   paper's incomplete-data SAT model incrementally and require a DRAT/LRAT UNSAT
   certificate for 21 states plus a theorem connecting the finite constraint
   family to all powers.
5. Treat uniqueness only after minimality; multiple machines agreeing on all
   observed digits are not proof of non-uniqueness.

## Falsifier

An explicit DFAO with at most 21 states satisfying both conventions and proved
correct for every Zeckendorf encoding of `4^i` falsifies 22-state minimality. A
finite-prefix match is only a candidate counterexample, not a falsifier.

For a proposed distinguishability certificate, one pair of purported residual
classes that is actually equivalent on all legal power continuations invalidates
that certificate.

## Evidence

1. Transcribe the 22-state table and verify its outputs against exact integer
   arithmetic for the first 100,000 base-4 digits of phi.
2. Generate sparse-input prefix trees for increasing `i`, minimize the finite
   labeled trees, and track stabilization of the number and signatures of
   residual classes.
3. Run incremental SAT for 13 through 21 states, preserving per-bound wall time,
   dictionary extent, candidate automata, and a proof certificate for every
   UNSAT result.
4. Whenever SAT finds a smaller candidate, use exact arithmetic to locate its
   first wrong digit and feed that witness back as a new constraint.

The first meaningful result is either a reproducible 21-state-or-smaller
candidate with its first failure, or a mechanically checked UNSAT certificate at
a stated finite constraint level. Neither alone proves the infinite minimality
theorem.

## Triage

`window`. The problem has a finite 22-state target and certificate-shaped
attacks, but the repository lacks the entire automata/SAT proof layer and the
paper already reports severe scaling.

## ASSUMED-UNVERIFIED

- The paper's base-4 Walnut automaton has exactly 22 reachable states under the
  conventions relevant to the question.
- A finite distinguishability basis exists for the sparse powers-only language.
- Exact digit generation through a large finite range will expose all faulty
  small DFAO candidates quickly enough for incremental SAT.
- Whether the fixed base-4 minimality question was resolved after arXiv v1 is
  unverified; novelty of any certificate construction is unassessed.

## 2026-09-05 continuation: contracting error coordinates and transient-state refutation

This section records research derived from PR #5405 at commit
`a02a13c3e358c262355013e712d42dfe5e0dae6d`. It supersedes the historical
22-state-only objective and the historical statements about missing source
infrastructure above. The objective is to determine the actual minimum,
including the possibility of a smaller machine. The evidence and replay sources
are in `Evidence/D5/Automata/GoldenBase4/`.

### Current mathematical and verification status

An explicit typed partial machine has 14 previous-zero states and 7
previous-one states, with every legal transition defined and illegal `11`
transitions undefined. No rejecting sink is counted. The start consumes leading
zeros and has output zero. Its exact interval invariant gives the all-integer
specification

\[
\Delta_4(q)=\lfloor4q\varphi\rfloor-4\lfloor q\varphi\rfloor
          =\lfloor4\{q\varphi\}\rfloor.
\]

In particular, its output on `zeckendorf(4^n)` is the required `D_4(n)`.
The all-integer task has a 21-state upper construction and 112 same-type
finite distinguishing witnesses giving a matching typed lower bound. These
witnesses must not be used unchanged as a lower bound for the powers-only task.

Separately, 28 exact power samples refute the existence of a machine with at
most three previous-one states, with no restriction on the number of
previous-zero states. Applied after the existing canonical transient-signature
quotient, this gives the structural bound `s >= 4`.

The published total-state lower bound 15 is inherited, not re-certified in this
submission. Under the partial-state convention just specified, the resulting
research interval is `15 <= m_typed <= 21`. The author's extended manuscript
reports 22 states and a 14-state UNSAT calculation in Section 6. Its original
base-four Walnut table has not been compared state by state here. The discrepancy
must not be attributed to a sink, a paper error, or a new priority claim without
that comparison.

The derivations and exact executable checks are supplied for scrutiny. No Lean
elaboration, kernel proof, LRAT verification, or admission of these new numerical
results is claimed. The Python and C++ programs are separate implementations by
the same authoring assistant, not independent-author review. No theorem for the
exact powers-only minimum is supplied.

### Error dynamics and the all-input induction

Let `q=[w]_F` and `v=[w0]_F`, using MSD-first Fibonacci weights `1,2,3,5,...`.
Set `psi=1-phi` and `e(w)=phi*q-v`. Appending the bit `a` gives

\[
q'=v+a,\qquad v'=q+v+2a,
\qquad e(wa)=\psi e(w)-a\psi^2.
\]

The last identity follows from `phi^2=phi+1`. Since `v` is an integer,
`{q*phi}={e(w)}`. The error lies in the open typed domains

\[
I_R=(3-2\varphi,2-\varphi),\qquad
I_T=(1-\varphi,3-2\varphi).
\]

For `f_a(x)=psi*x-a*psi^2`, endpoint comparison gives
`f_0(I_R) subset I_R`, `f_0(I_T) subset I_R`, and `f_1(I_R)=I_T`.
The initial error is zero. Type `R` means the empty prefix or last bit zero;
`T` means last bit one. These names specify numeration types and do not assert
that every `R` state is graph-theoretically recurrent.

The output cuts are `0,1/4` in `R` and `-1/2,-1/4` in `T`. Repeatedly add
legal preimages of cuts until closed. Represent every endpoint as `(a+b*phi)/4`.
The inverse maps on coefficient pairs are

\[
f_0^{-1}(a,b)=(-b,-a-b),\qquad
f_1^{-1}(a,b)=(4-b,-4-a-b).
\]

The resulting ordered interior cuts are

```
R: (4,-3), (1,-1), (6,-4), (3,-2), (0,0), (5,-3),
   (2,-1), (7,-4), (4,-2), (1,0), (6,-3), (3,-1)
T: (1,-2), (-2,0), (3,-3), (0,-1), (2,-2), (-1,0)
```

All true prefix errors lie in `Z[phi]`. Except for zero, at least one coordinate
of each listed pair is not divisible by four. Irrationality of `phi` makes the
coefficients in the basis `1,phi` unique, so these 17 artificial cut points
cannot be reached. Zero receives its own singleton state. The 13 open `R`
intervals plus this singleton give 14 states; the seven open `T` intervals give
seven states.

`machine21.tsv` lists every state, output, transition and endpoint. Columns are
`id type output zero one lower_a lower_b upper_a upper_b singleton`.
The interval checker verifies all 35 legal transition inclusions and all 21
constant-output cells using exact algebra. The negative slope reverses the
endpoint order. The singleton is checked separately. Coverage of all reachable
errors, transition preservation and the output identity yield correctness by
induction on input length. Finite numerical regression is supplemental and is
not the premise of that induction.

### Exact reuse of the first-return skeleton

The existing `Skeleton` definition is reused by the following serialization:

```
start = 0
A = [0,9,8,7,7,6,5,5,4,4,3,2,2,1]
J = [10,9,9,9,10,10,10,11,11,12,12,12,13,13]
F = [0,3,3,3,3,3,0,0,0,0,0,1,1,1]
G = [2,3,2,2,2,2,2,2,2,2,1,1,1,1]
```

Here `zeroStep(q)=some A(q)`, `oneSignature(q)=some(G(q),some J(q))`,
and `zeroOutput(q)=F(q)`. The seven used `(G,J)` pairs are
`(1,13),(1,12),(2,12),(2,11),(2,10),(2,9),(3,9)`.
This supplies the concrete `(r,s)=(14,7)` construction. The JSON and its checker
verify the correspondence to all 14 rows of the full machine. An actual Lean
transport theorem for this concrete table remains to be supplied.

All 21 states have access words. A pair search produces a common legal suffix
for every pair within a numeration type, with distinct oracle outputs. The
C++ checker independently evaluates those complete words as Fibonacci integers
and checks the exact floor difference. There are `choose(14,2)+choose(7,2)=112`
same-type pairs. Their full words involve 39 integers, at most 341, with maximum
word length 12. For example, `100000` followed by `0` represents 21, which is
not a power of four. This is why all-integer minimality does not settle the
sparse-input minimum.

### Gap-state relaxation and the bound s >= 4

Write a nonzero legal word as

\[
1\,0^{g_1}1\,0^{g_2}1\cdots0^{g_k}1\,0^\ell,
\qquad g_i\ge1.
\]

Only samples with `ell=0` or `ell=1` are used. On the previous-one state set
`T`, define `H_g(t)=delta*(t,0^g1)` and `E(t)=output(delta(t,0))` wherever they
are defined. Every observed path must succeed. Fill unused partial table entries
arbitrarily and allow the different `H_g` maps to vary independently. This is a
relaxation of the actual machine: all real fitted machines induce such tables,
whereas the tables need not share any real previous-zero realization. A
refutation of the relaxation therefore excludes every real realization,
regardless of its previous-zero state count.

The samples `n=0,1,26` end in one and have outputs `2,1,3`. They force at least
three different `T` states. Under the exactly-three hypothesis, name them by
outputs `1,2,3`; the first input one reaches the state with output two.
All selected `ell=1` labels are zero or one. An `E` value of two, three or
undefined cannot be used by any such observed endpoint, so it may be changed
to zero without changing the samples. Thus the eight Boolean `E` maps cover
all possibilities without an additional restriction on fitted machines.

The selected power indices are

```
0,1,3,4,6,8,10,11,12,16,20,22,26,29,
31,37,39,40,44,49,51,55,58,65,68,71,76,78
```

`gap3_core_rows.tsv` contains `n,d,ell,g_1,...,g_k`. The replay program rebuilds
each complete word, verifies that its integer value is exactly `4^n`, and
recomputes its label using

\[
\lfloor q\varphi\rfloor
=\left\lfloor\frac{q+\lfloor\sqrt{5q^2}\rfloor}{2}\right\rfloor.
\]

There are 11 gap lengths, 33 three-valued transition entries, and 732 shared
trie nodes. Each edge enforces `color(child)=H_g(color(parent))`.
Domain propagation removes unsupported parent and child values. When a parent
has a unique value, the corresponding transition row is intersected with the
child domain. Every such narrowing preserves every genuine assignment.

`gap3_refutation.txt` records a complete branch tree for each Boolean `E` map.
A `B variable mask` node must enumerate every value remaining in that domain.
An `L` leaf is accepted only after propagation has produced an empty domain.
The replay reads all eight cases in order and rejects trailing or missing data.
There are 936 certificate nodes, including 350 branches and 586 contradiction
leaves. The certificate's Git blob SHA is
`99744bdab177cdc0f255dc2679df821b64809fd3`.

No ordinary self-loop, unreachable slot or arbitrary first-occurrence ordering
is forbidden. Neither the replay nor its conclusion imposes a bound on the
previous-zero state count. The finite evidence excludes at most three
previous-one states. Applying it to the existing canonical signature machine
gives `s >= 4`. A Lean proof of the relaxation transport and checker soundness
is still required for kernel certification. No inclusion-minimality or
minimum-cardinality claim is made for the 28-sample set.

### What the suffix experiment shows and the next coupled search

For each of the first 79 and the first 200 power samples, the simple
same-type common-suffix conflict graphs, with the published zero-output anchor,
have a triangle and a verified three-coloring in each type. Their chromatic
numbers are therefore `3,3`. This particular pairwise graph abstraction yields
only six states on these samples. It does not rule out stronger graphs on
larger samples or different certificates.

The gap refutation uses the additional consistency that the same transition
entry must be reused on every occurrence. The next search should retain this
coupling and the signature cost rather than replace the transition system by
only a pairwise incompatibility graph.

Assuming `r+s <= 20`, `s <= r`, and the derived `s >= 4`, seven capacity
rectangles cover every candidate:

```
(10,10), (11,9), (12,8), (13,7), (14,6), (15,5), (16,4).
```

Indeed `r'=max(r,10)` satisfies `r <= r' <= 16` and `s <= 20-r'`.
Use the existing capacity padding with unused states allowed. The old
`(17,3)` branch is excluded by the gap certificate. Similarly, total budget 14
needs only `(7,7),(8,6),(9,5),(10,4)` under the same structural bound.
No refutations of these seven budget-20 cases are supplied here. Excluding all
of them would give the powers-only lower bound 21 after the model-to-encoding
transport is proved. A smaller satisfying finite-sample machine instead needs
an all-powers correctness proof or a counterexample search with the exact
oracle; finite fitting alone is insufficient for an upper-bound claim.

There is a useful correction to the historical evidence paragraph above:
a finite UNSAT certificate CAN give an infinite-domain lower bound once every
purported smaller all-powers machine is proved to induce a satisfying assignment
for those exact finite power samples. An all-powers machine would have to fit
that subset. The missing requirement is the sound transport and certified
refutation, not an infinite dictionary. Finite SAT fitting has the opposite
asymmetry and supplies no all-powers correctness theorem by itself.

### Reproduction and concrete proof frontier

Run `sh Evidence/D5/Automata/GoldenBase4/reproduce.sh`.
The deposit replay executed 100,000 consecutive integers and 2,000 powers,
in addition to the exact interval proof checks, the 2,000-power skeleton check,
the complete gap refutation and five negative tests. All passed. The earlier
research run used 1,000,000 consecutive integers and 5,000 powers; both ranges
are reproducible through the environment variables documented in the README.
Five changed-input tests reject an incorrect transition, an incomplete branch,
a false contradiction leaf, a truncated proof and an incorrect oracle digit.

The next formal obligations are: the arithmetic prefix-error invariant and its
finite interval simulation; the concrete table-to-existing-skeleton transport;
the gap-word transport into the relaxed transition equations; solution
preservation of propagation and exhaustive branch coverage; and finally the
sample-to-slot-CNF and certified refutation chain for the remaining budgets.
These are separate obligations. A source table alone is not a proof of the
numerical upper bound, and a discovery program returning UNSAT is not a
kernel-checked lower bound.

Reference: Aaron Barnoff, Curtis Bright and Jeffrey Shallit, *Computing the
base-b representation of quadratic irrationals using automata*, Theoretical
Computer Science 1071 (2026), 115843, DOI `10.1016/j.tcs.2026.115843`.
The author's extended manuscript is `https://cs.curtisbright.com/reports/digits-automata.pdf`;
Section 6 supplies the reported state-count and sparse-task context.

## 2026-09-05 formal continuation: direct invariant and exact M01 input transport

Two source modules now supply the complete upper-construction argument against
M01's existing input and digit functions:

- `D5/S1/Digit/GoldenBase4IntervalMachine.lean`;
- `D5/S1/Digit/GoldenBase4DenseInput.lean`.

Each has a source-bound Scribe companion under `Blueprint/D5/S1/Digit/`.
The first was committed at `e9307a6d4c6bf064bc74c2cbefd0a996e2214e37`;
the second at `c54dd3255e4e00a30420ad778be4293cba6d3ef5`.
This section updates the proof frontier of the preceding research deposit.
The scripts have not been elaborated by the pinned Lean executable in this
session. Kernel verification, axiom-closure output and repository admission are
not asserted. The exact arithmetic checks below are separate executable evidence.

### A smaller correctness argument for the fixed table

The previous derivation described the artificial cuts through irrationality and
membership in `Z[phi]`. Those facts help explain how the partition was found,
but are not necessary premises for correctness of this explicit table.

For a word `w`, `fibPair w` is defined using the standard upstream `Nat.fib`
weights. Its components are the value of `w` and its shifted value. The theorem
`fibPair_append_digit` derives the update `(q,v) -> (v+a,q+v+2a)`.
`error_append_digit` then proves the exact affine update

\[
e(wa)=(1-\varphi)e(w)-a(1-\varphi)^2
\]

from `Real.goldenRatio_sq`. All machine runs use the existing
`TypedPartialDFAO` and `runTransition`; no replacement run semantics is introduced.

Let `C_q` be the interval assigned to state `q`, with `C_0={0}`. For every
noninitial legal transition `q --a--> t`, the finite certificate proves

\[
t\ne0,\qquad
\ell_t\le f_a(u_q),\qquad f_a(\ell_q)\le u_t.
\]

Since the affine slope is negative, these inequalities imply
`e in C_q -> f_a(e) in C_t`. The two transitions from the singleton are checked
separately. `initial_cell` starts the induction. Thus every reached error lies
in its state cell without first proving that a family of cells covers the
whole real domain, and without an assumption excluding unreachable cut points.

For each state the source supplies an integer strip `m_q` and proves

\[
m_q+d_q/4\le e<m_q+(d_q+1)/4.
\]

This identifies both floors and hence the emitted digit. The separate theorem
`legal_run_exists` shows that every legal base word has a successful machine
run. This is necessary: correctness conditioned only on successful runs could
otherwise leave required inputs undefined. Combining these results gives
`every_legal_word_correct`, for words of arbitrary length.

### Connecting the unchanged canonical input to the invariant

The second module closes the source-level M01 transport obligation rather than
assuming an encoder-correctness field. It uses the existing `wdigits`,
`zeckendorfWordLength`, `zeckendorfBit`, and `zeckendorfMSDWord` unchanged.

Upstream `wdigits_isCanonical` gives descending indices separated by at least
two and bounded below by two. `occupied_index_bounds` places all those indices
inside the existing dense display. A finite bijection `i -> i+2` identifies the
selected dense positions with the occupied Fibonacci indices. Together with
`decode_wdigits`, this yields

\[
\operatorname{fibPair}(\operatorname{zeckendorfMSDWord}(n))_1=n.
\]

The guarded induction `separated_bits_run` proves legality of the dense word.
Entry from the previous-one type requires the next bit to be zero; the proof
retains that condition rather than resetting the type. It follows that the
same canonical M01 word has both its exact value and a legal shared-base run.

The endpoint is the following source theorem, with the original M01 functions:

```lean
theorem twenty_one_state_power_witness :
    ∃ M : TypedPartialDFAO binaryZeckendorfBase (Fin 4) (Fin 21),
      (∀ i, M.evalOutput (base4PowerWord i) = some (base4GoldenDigit i)) ∧
      M.step M.start 0 = some M.start ∧ M.output M.start = 0
```

The witness is the explicit interval machine. The argument has no finite sample
extent, no supplied global-correctness hypothesis, and no assumption that a
chosen input encoder means the desired integer. The original M01 arithmetic
and dense word are connected by proofs. This supplies a source-level upper
construction for the concrete task; it does not supply a sparse state lower bound.

### Executed checks on the actual source tables

`check_interval_source.py` parses the finite vector literals in the Lean source
itself. It reduces algebraic coefficients using `phi^2=phi+1` and uses the exact
rational bracket `8/5 < phi < 13/8`. It checked all 35 legal transitions, the 66
noninitial endpoint inequalities, the singleton cases, and all 21 output cells.
Four mutations of a zero target, a one target, an output and an endpoint were
rejected. An additional 16,382 finite word-and-appended-bit checks passed for
the Fibonacci pair recurrence, including noncanonical binary words.

`check_dense_input.py` checked 20,000 consecutive integers and 1,000 power
inputs, indices 0 through 999. Each case checks the occupied-index bounds,
separation, range bijection, dense Fibonacci value, legal machine run and exact
integer-square-root digit oracle. The display of zero is `[0]`, as in M01.
No floating-point arithmetic is used. These runs do not execute Lean and are
not substitutes for kernel checking of the universal statements.

The source SHA-256 values for the checked files are:

```
GoldenBase4IntervalMachine.lean
6e1de8d37db9ffff38b286079dfcd9a0c4b355a87ceefd164f5b3dafe3d91a55
GoldenBase4DenseInput.lean
78c213ad2e9ab3c6709b4c352cb5d8b0d9b61c8c1898534297832a9b7dd8e113
```

The source-bound interval and dense-input checks can be replayed with:

```sh
python Evidence/D5/Automata/GoldenBase4/check_interval_source.py \
  D5/S1/Digit/GoldenBase4IntervalMachine.lean
python Evidence/D5/Automata/GoldenBase4/check_dense_input.py \
  D5/S1/Digit/GoldenBase4IntervalMachine.lean
```

The two Lean files expose 21 public theorem declarations, each with a Scribe
binding, and the interval Scribe also binds the concrete machine definition.
No `sorry`, `admit` or newly postulated axiom is used in these new source files.

### The remaining minimum-state question

The exact powers-only minimum is still undetermined. This continuation does
not increase the published total-state lower bound 15 and does not provide
refutations for all total budgets through 20. The existing three-transient-state
refutation and its `s >= 4` consequence still need their Lean checker-soundness
and transport proofs. They are not asserted to be kernel-certified here.

The author's extended manuscript uses MSD-first inputs and the same zero-based
digit convention, and reports a 22-state base-four Walnut construction. Its
original base-four table has not been obtained for a state-by-state comparison.
The present 21-state upper construction does not identify why that reported
number differs. A sink explanation, a paper correction and a priority claim
are not supplied by the construction alone.

After verification of the submitted upper proof, the decisive remaining result
is either a smaller all-powers-correct machine or complete certified exclusion
of machines with at most twenty states. The seven budget rectangles recorded
above remain the relevant coupled lower-bound targets. All-integer distinguishing
suffixes cannot replace the powers-only sample obligations in those targets.

## 2026-09-06 structural continuation: one zero generator and exact response rank

The target remains the minimum state count on the original power inputs. This
continuation derives structural constraints on every slot candidate and an exact
certificate for the already constructed reference machine. It does not increase
the total-state lower bound 15, prove that the powers-only minimum is 21, or
resolve the discrepancy with the paper's reported 22-state Walnut object.

### Literature and the precise transfer being used

Barnoff, Bright and Shallit, *Computing the base-b representation of quadratic
irrationals using automata*, TCS 1071 (2026), 115843, distinguish all-integer
correctness from correctness only on powers. Their incomplete-data minimization
problem remains the target; no output on an arbitrary nonpower may be added to
its lower-bound sample set. DOI: `10.1016/j.tcs.2026.115843`.

Moradi, Rampersad and Shallit, *Complexity of Linear Subsequences of
Fibonacci-Automatic Sequences*, arXiv:2603.21645v1, 23 March 2026, construct
Fibonacci automata for arithmetic relations and give polynomial bounds for
linear subsequences. Their explicit treatment of MSD-first input, leading-zero
loops and omitted dead states is relevant to matching conventions. Their
linear-subsequence result does not establish the exponential restriction
`h(4^n)` or a minimality transfer to that restriction.
Source: `https://arxiv.org/html/2603.21645v1`.

Lacroce, Balle, Panangaden and Rabusseau, *Optimal approximate minimization of
one-letter weighted finite automata*, MSCS, online 8 November 2024, volume 2025,
provides the one-letter Hankel/realization setting. We use only the exact
factorization principle, not an approximate singular-value bound. Linear rank
is a necessary deterministic state-capacity constraint; arbitrary low-rank
completion is not sufficient for a deterministic typed machine.
DOI: `10.1017/S0960129524000276`.

Dumitru, Yoshinaka and Shinohara, *Learning deterministic finite-state machines
from the prefixes of a single string is NP-complete*, arXiv:2601.12621v1,
18 January 2026, explains why a generic prefix-tree presentation does not itself
make exact identification easy. This result is not a hardness proof for the
single fixed golden-ratio instance.
Source: `https://arxiv.org/html/2601.12621v1`.

The repository already has the general linear-system result in
`D5/S3/Observer/Hankel/HankelRankMinimality.lean` and its reachable-observable
minimal-realization companion. The new source supplies the deterministic slot
bridge; it reuses `Skeleton`, `SlotWitness`, upstream iterates, `Matrix.mul`, and
`Matrix.rank`. It introduces no alternate DFAO, run semantics, or rank definition.

### Every gap length uses the same zero map

For an existing `SlotWitness`, write

\[
A:R\to R,\qquad B:R\to T,\qquad C:T\to R,
\]

for `zeroTarget`, `slotOf`, and `returnTarget`. Let `F` be the recurrent digit
output and `G` the transient digit output. Starting in transient slot `t`, the
word `0^(k+1)1` selects

\[
\boxed{H_{k+1}(t)=B(A^k(C(t))).}
\]

Thus separate gap lengths cannot be chosen independently in a genuine machine.
The old three-slot refutation allowed such independence as a relaxation, which
was sound for that exclusion but lost this shared-generator structure.

`evalFrom_zero_prefix` proves the equation for every continuation using the
existing Option-valued block evaluation. `evalFrom_one_zero_gap` then identifies
the original evaluation of `10 0^k 1` with
`G(B(A^k(C(B(q)))))`. The source takes the existing serialization equations as
its only machine interface. No ordinary self-loop or unused capacity is removed.

### Joint responses factor through the actual recurrent carrier

A probe asks either whether the current output equals a specified digit, or
whether the next one edge selects a specified transient slot. Its value is the
rational indicator 0 or 1. The slot probe is latent structural information for
an unknown candidate; it is not an externally known digit label.

Choose row origins `q_i`, row delays `a_i`, column delays `b_j`, and probes `p_j`.
The sampled response is

\[
H_{ij}=p_j(A^{a_i+b_j}(q_i)).
\]

Define

\[
L_{iq}=\mathbf1_{A^{a_i}(q_i)=q},
\qquad U_{qj}=p_j(A^{b_j}(q)).
\]

The unique intermediate state and the iterate-addition identity give

\[
\boxed{H=LU,\qquad \operatorname{rank}_{\mathbb Q}H\le |R|.}
\]

Here `|R|` is the number of recurrent states. The Lean names are
`response_factorization` and `response_rank_le`. Every square sampled response
of order greater than the recurrent capacity has determinant zero, proved as
`response_det_eq_zero`. A right inverse supplies an exact finite rank certificate
through `capacity_ge_of_right_inverse`. These are algebraic consequences of the
actual transition system, so they require no additional symmetry-breaking premise.

### A concrete unimodular reference certificate

`GoldenBase4ZeroResponse.lean` reads the outputs of
`GoldenBase4IntervalMachine.machine` directly. Three finite table equalities
identify its zero rows, one-edge selectors, and transient returns with the
existing machine. Its explicit `SlotWitness` has fourteen recurrent positions
and seven transient slots.

Row access from the start or a named return, followed by a finite zero delay,
exhausts all fourteen recurrent states. Joint probes at depths zero through
three contain a 14 by 14 submatrix `profileMinor`. The source supplies an
integer-valued matrix `profileInverse` and a finite proof body for

\[
\operatorname{profileMinor}\,\operatorname{profileInverse}=I_{14}.
\]

This establishes the source theorem `profile_rank_fourteen`. The executable
checker additionally verifies the reverse product and determinant -1. The ranks
of the full joint response through one, two, three and four zero-depth levels
are respectively `9,12,13,14`. These are exact rational ranks.

Consequently, any deterministic slot realization of this same labelled profile
requires at least fourteen recurrent states. This scope is explicit in
`same_profile_recurrent_lower_bound`. Slot labels may be renamed consistently,
but arbitrary powers-correct candidates are not required to have this profile.

### The remaining arithmetic requirement

The reference rank certificate must not be substituted for a powers-only lower
bound. In particular, copying the reference slot readouts or its unconstrained
nonpower outputs into an unknown candidate would assume information that the
original task does not specify.

A valid application to the remaining capacity cases must keep these entries
as unknowns, impose the exact observed power labels and shared transition
equations, and prove that every compatible completion violates the relevant
rank bound or another necessary deterministic constraint. Low rank alone does
not certify existence of a deterministic machine. The one-hot state and slot
conditions, type restrictions, common shift action, and signature budget remain
part of the problem. The current source proves the necessary rank constraints;
it does not prove that all compatible completions have rank fourteen.

The seven previously recorded budget-20 cases therefore remain unrefuted in
this continuation. A reference-profile rigidity result is useful for designing
structural exclusions, but it is stronger data than the powers-only task supplies.

### Executed checks and source status

The two new Lean modules are
`D5/S0/Certificates/SkeletonSlotZeroResponse.lean` and
`D5/S1/Digit/GoldenBase4ZeroResponse.lean`. Each has a Scribe companion covering
all its public declarations. There are fourteen theorem declarations in total.
No new axioms, `sorry`, or admitted claims are used. The proof scripts have been
logically reviewed but have not been elaborated or kernel-checked in this
session; inherited source dependencies are not newly certified here.

The standard-library-only checker reads the original and new Lean table
literals. It verifies both inverse products, all row accesses, probe metadata,
and the exact determinant. Across 1,164 small slot tables it checks 122,724
factorization entries, 129,696 zero-prefix evaluation equations, and 9,264
gap-evaluation equations. The set includes 876 models with zero self-loops,
520 with unused slots, and 260 with duplicate output-return pairs. Four altered
return, probe, origin and inverse cases are rejected. These executed checks do
not replace the general Lean proof or establish a new powers-only bound.

Reproduce from a checkout with

```sh
python Evidence/D5/Automata/GoldenBase4/check_zero_response.py .
```

The exact minor, inverse and measured results are retained in
`zero_response_minor14.json` and `zero_response_validation.json` in the same
Evidence directory. The generic Hankel factorization is established mathematics;
no priority claim is made for it. The contributions here are its source-level
transport from the existing typed slot semantics, the explicit exact reference
certificate, and the precise separation between latent completion variables
and the arithmetic observations allowed by the original open problem.

## 2026-09-06 arithmetic continuation: prefix exposure and unbounded error weight

This continuation studies the original powers-only problem through the regular
language on which a candidate differs from the exact reference machine. It adds
one structural obstruction, not a new numerical powers-only state lower bound.
The proof source is `D5/S1/Digit/GoldenBase4UnboundedError.lean`, with its paired
Scribe, committed at `139babbef0500e7a50c646872b76314fbc771f3c`.

### Current arithmetic literature and its exact scope

Chang and Miller, *Benford's Law under Zeckendorf Expansion*, Fibonacci Quarterly
63(2), 304-335, published online 14 August 2025, DOI
`10.1080/00150517.2024.2413585`, arXiv:2309.00090, Theorems 1.5 and 3.8, give
positive limiting frequencies for every admissible leading block in powers.
Applying the latter theorem to `4^(a+mn)` also gives this assertion on each fixed
arithmetic progression of exponents. The irrationality needed is elementary:
`4^q=phi^p`, for positive integers p,q, would give `16^q=(-1)^p` after taking the
quadratic field norm, a contradiction. These are prefix statements, not a
claim that powers meet every nonempty regular language.

Bugeaud, *On the Zeckendorf representation of smooth numbers*, Moscow Math. J.
21(1), 31-42 (2021), DOI `10.17323/1609-4514-2021-21-1-31-42`,
arXiv:1909.03863, Theorem 1.4, proves that integral S-units of sufficiently large
size have more than `(1-epsilon) log log N / log log log N` nonzero Zeckendorf
digits. The threshold is effectively computable. In particular, for each fixed
K, only finitely many `4^n` have at most K nonzero digits. No explicit threshold
for an arbitrary K is computed in this continuation.

Earp-Lynch, Earp-Lynch, Kihel and Tiebekabe, *Powers as Fibonacci Sums*,
Quaestiones Mathematicae 48(4), 597-609 (2025), DOI
`10.2989/16073606.2024.2411461`, was first published online on 16 October 2024.
Its arXiv:2608.04445v1 version was submitted on 5 August 2026 and records minor
corrections and improved computation code. Thus the 2026 posting is an updated
version of an earlier journal article. Theorem 1.1 and Table 4 completely list
the powers of two having exactly six nonzero Zeckendorf digits. Their exponents
are `9,11,12,14,17,28`. Restricting to even exponents yields the corollary

\[
\#_1 Z(4^n)=6\quad\Longleftrightarrow\quad n\in\{6,7,14\}.
\]

The article combines explicit logarithmic-form estimates and Baker-Davenport
reduction; its six-term binary case reduces the largest Fibonacci index from
an initial bound `5.5*10^94` to at most 51. The three relevant table rows were
recomputed here with exact integer arithmetic. The authors' complete reduction
and code were not rerun, and their completeness theorem has not been imported
as a Lean axiom. No complete classification for all weights at most six is
claimed on the basis of Table 4 alone.

Dekking, *The structure of Zeckendorf expansions*, Integers 21, A6 (2021),
arXiv:2006.06970, gives generalized Beatty descriptions for integers with fixed
terminal blocks. This is the complementary suffix arithmetic. Substituting
`4^n` into such a description leaves a Diophantine condition; the result does
not itself determine powers in arbitrary finite-state product languages.

Holzer and Maletti, *An n log n algorithm for hyper-minimizing a (minimized)
deterministic automaton*, TCS 411, 3404-3413 (2010), DOI
`10.1016/j.tcs.2010.05.029`, studies compression permitting finitely many errors.
Its DFA acceptance setting is not silently identified with this typed DFAO
problem. It motivates checking whether finite-error compression could help.
The stronger bounded-nonzero-digit obstruction below answers that question for
the present reference function and the start-zero-loop convention.

### What prefix density forces in the original candidate class

Here is a human-level consequence of the cited prefix theorem. Let M be any
machine correct on all original power inputs and satisfying the initial zero
self-loop. Every valid finite Zeckendorf word is a prefix of a power word after
possibly adding leading zeroes. Hence every such word must have a defined run
in M. If q is reached by a valid word w and a is a legal next symbol, then wa
is also such a prefix. Its transition in M must therefore be defined.

Thus a correct candidate is total on legal transitions of its reachable part.
Deleting an edge on the grounds that a valid prefix might never occur in a
power is unsound. This argument does not prescribe the output at the endpoint
of w when w is not itself a power. The full-word output is observed only after
the remaining suffix has been read. The density-to-totality argument is not
claimed as a kernel-checked analytic theorem in the new module.

### Why bounded-weight disagreement was a plausible route

For a candidate M, let E_M be the set of valid words on which its output differs
from the exact all-integer reference output, with an undefined run counted as a
failure. This language is regular by the finite product construction. Exact
powers-only correctness is equivalent to

\[
E_M\cap\{Z(4^n):n\ge0\}=\varnothing.
\]

If E_M had a bounded number of ones, Bugeaud's theorem would reduce its power
intersection to finitely many effectively bounded cases. Specific low-weight
classes can use the newer explicit Fibonacci-sum classifications. This was a
concrete route to an infinite correctness certificate, rather than mere testing.
The next theorem proves that it cannot produce a machine below 21 states under
the stated anchor. A polynomial-growth regular language need not have bounded
one-count, so those notions must not be interchanged.

### New structural obstruction: all smaller anchored machines have heavy errors

Let A denote the existing 21-state reference table and let wt(w) count ones.
For every finite typed partial candidate M with its initial zero self-loop,

\[
|Q_M|<21\quad\Longrightarrow\quad
\forall K\ \exists w:\quad w\text{ is legal},\quad
\operatorname{wt}(w)>K,\quad M(w)\ne\Delta_4([w]_F).
\]

The word in this statement is not required to represent a power of four.
Undefined candidate output also counts as disagreement. The proof uses the
actual reference table, its existing arithmetic theorem, and finite diagnostic
suffixes. It assumes no number-theoretic density or sparsity theorem.

In the reference machine, reading `1` reaches state 18 and `00001` is a loop
at that state containing exactly one one. Therefore

\[
p_K=1(00001)^K
\]

reaches state 18 and has K+1 ones. Twenty fixed access tails from state 18 reach
all states 1 through 20. Appending them to p_K yields high-weight access to every
noninitial reference state. Thirteen diagnostic suffixes separate every pair
of distinct states of the same type; all 112 such pairs were checked. States
of different types cannot represent the same candidate state after successful
runs of the same input types.

Suppose M agreed on every legal word of weight greater than K. Two high-weight
access words reaching the same candidate state must reach the same reference
state: otherwise a common legal diagnostic suffix forces different outputs,
while their candidate continuations remain identical. Appending a suffix never
reduces the number of ones. Thus the twenty reference core states force twenty
different candidate states.

None of these twenty candidate states can be M's start state. If a core access
word reached the start, appending zero would leave M there. In the reference,
zero moves every noninitial state to a different state. Applying the preceding
collision argument to the access word and to that word followed by zero gives
a contradiction. Consequently the twenty states and the start are distinct.
The proof explicitly constructs an injection from `Option (Fin 20)` into Q_M.

The contrapositive yields unbounded error weight. This excludes finite-error
compression and, more strongly, compression where all errors have bounded
nonzero-digit count. It does not exclude a smaller machine whose unbounded-
weight error language nevertheless avoids every power of four.

### Source and arithmetic validation

The public endpoints are `high_weight_collision`,
`bounded_error_weight_requires_twenty_one`,
`small_machine_unbounded_error_weight`, and
`small_machine_unbounded_arithmetic_errors`. The last uses the existing
`successful_run_digit` to identify the disputed output with the true floor
difference. All four have source-bound Scribe entries. No new axioms or missing
proof placeholders were introduced. Pinned Lean elaboration and kernel checking
were not executed; inherited source proofs are not newly certified here.

The standard-library checker reads the actual reference and new Lean literals.
It verifies the twenty access tails, twenty nonfixed zero steps, the pumping
cycle, and the 112 same-type separations. For thresholds 0,1,6,14,64 it performs
1,255 exact arithmetic checks on pumped accesses and diagnostic suffixes.
Three modified cycle/access/separator certificates are rejected.

A separate bounded scan of power indices 0 through 999 checks exact digits and
finds all twenty noninitial states as terminal states by index 62. Their first
indices, ordered by reference state 1 through 20, are

```
56,19,5,2,17,27,28,57,21,4,62,20,15,11,1,45,3,0,12,26.
```

This also prevents shrinking the reference by an ordinary type- and transition-
preserving quotient that remains correct on those powers and has zero initial
output. Every reference state's output is then fixed by a power observation or
the initial anchor, and the diagnostic suffixes force the quotient to be
injective. This is a finite-certificate mathematical corollary, not a newly
kernel-checked theorem or a restriction on arbitrary redesigned candidates.

The scan sees exactly-six-weight powers only at 6,7,14. Its finite extent is
not used as evidence that there are no later instances; that assertion comes
from the cited paper's completeness theorem. The validation JSON records this
distinction explicitly.

Reproduce with

```sh
python Evidence/D5/Automata/GoldenBase4/check_unbounded_error.py \
  D5/S1/Digit/GoldenBase4IntervalMachine.lean \
  D5/S1/Digit/GoldenBase4UnboundedError.lean
```

The checked source SHA-256 is
`13faec22a8bacd5c8749315fede85466ef26c1c05188214e34cdbe5b37c7332a`.
The reference SHA-256 remains
`d02440b7e57663841f541a3418b780bb950b114fc669beeacdd2cad82b762101`.
Results are retained in `unbounded_error_validation.json`.

### Remaining exact target

For a smaller candidate, the necessary error language now has unbounded one-
count, cannot contain a whole valid prefix cone of failures, and must avoid all
power words. The whole-prefix restriction follows from prefix density and
global correctness. These necessary properties do not imply a contradiction:
prefix density alone is weaker than hitting every regular set. The missing
step is a statement about the arithmetic intersection for error languages
arising from the bounded candidate/reference product, or an explicit smaller
machine together with a different infinite correctness certificate.

No 20-state exclusion, improved numerical powers-only lower bound, or resolution
of the original Walnut 21/22 comparison is claimed. The new obstruction removes
specific tempting compression routes; it does not rename the all-integer
problem as the original sparse-input problem.

## 2026-09-06 synchronization: four-slot exclusion and prime-residue stratification

This appendix incorporates the completed gap4 and residue-bridge work that was
previously present in source/evidence but absent from this cumulative theory file.
The preceding sections remain historical snapshots. The current structural
transient-signature lower bound is five, subject to the verification distinction
below; the exact total-state minimum is still undetermined.

### The finite obstruction uses genuine power inputs

Let S be the 144 indices in `Evidence/D5/Automata/GoldenBase4/gap4_power_rows.tsv`.
Every index lies between zero and 249. Exact Fibonacci evaluation reconstructs
`4^n` from each row. Labels are computed using integer square roots:

\[
L(q)=\left\lfloor\frac{q+\lfloor\sqrt{5q^2}\rfloor}{2}\right\rfloor,
\qquad D_4(n)=L(4^{n+1})-4L(4^n).
\]

For every typed partial candidate whose previous-one fiber has cardinality at
most four, at least one row of S has an incorrect or undefined output. There
is no bound on the previous-zero fiber. The reduction and completed external
proof replay establish this statement without using the 21-state reference
machine. Consequently the unresolved 21/22 artifact comparison cannot affect
this particular exclusion.

For a word `1 0^g1 1 ... 0^gk 1 0^ell`, with positive internal gaps and ell zero
or one, retain only the state after each one. Actual successful runs induce
partial maps H_g on that fiber and terminal outputs G and E. Fill unused
partial entries arbitrarily. Different H_g are allowed to be independent,
which is a relaxation: every fitted actual machine induces a fitted relaxed
model. No assertion that every relaxed model has a recurrent realization is
used in the exclusion.

### Why the 48 output cases cover every four-slot candidate

The exact rows n=0,1,26 end in one and have distinct outputs 2,1,3. Name their
terminal states 0,1,2. Padding a smaller nonempty fiber to four states leaves
all observed runs unchanged. The fourth G output can be restricted to 1,2,3:
a value zero is never used by these terminal-one observations and can be changed
to one without changing any sample. Every ell=1 observation is labelled zero
or one. E outputs outside that set are likewise unused at observed endpoints
and can be changed to zero. Thus the complete normalized family is

\[
G=(2,1,3,c),\quad c\in\{1,2,3\},
\qquad E\in\{0,1\}^4,
\]

with exactly 48 cases. This is an observation-preserving output normalization,
not a ban on transition self-loops or on unused slots. All gap maps remain
arbitrary total four-state maps. The input family uses 19 gap lengths, giving
76 four-valued transition variables and a 13,831-node shared prefix trie.
Each arc enforces `child = H_g(parent)` with the same H_g reused across rows.

The three stored proof parts cover all 48 cases. The independent C++ replay
recomputes every power and label, then checks complete branch coverage and
solution-preserving support pruning. It accepts only a genuinely empty-domain
leaf. Recorded totals are 1,272,968 proof nodes, 420,692 branches, 852,276
contradiction leaves, and maximum branch depth 21. Eight corrupted-data/proof
checks were rejected in the original run. The producer's branching heuristic
is not used by the replay. The two implementations were written by the same
authoring assistant, not independently reviewed by another author.

Files now in the PR include `FiniteDomainSelectionRefutation.lean` and its
Scribe, the numeric rows, `check_gap4_certificate.cpp`, compressed complete
proofs, the replay record, and `reproduce_gap4.sh`. The Lean checker was
subsequently generalized from Fin 4 to Fin colors. Its soundness theorem is
`accepted_refutation_excludes_solution`.

The concrete B/L trees have not been parsed into a Lean Refutation value and
kernel checked. The full typed-candidate normalization-to-instance proof also
remains to be connected in Lean. The numerical conclusion is therefore an
explicit mathematical reduction with completed exact external replay, not a
claimed kernel-accepted numerical theorem.

### Consequence for the original total-budget search

Apply the exclusion after the existing transient-signature quotient. A
canonical realization has one previous-one state per used signature, so s>=5.
Together with r+s<=20 and s<=r this gives r<=15. Capacity padding covers every
such candidate by one of

```
(10,10), (11,9), (12,8), (13,7), (14,6), (15,5).
```

Indeed r'=max(r,10) satisfies r<=r'<=15 and s<=20-r'. The old (16,4) case is
excluded by the same four-slot certificate. None of these six remaining cases
is excluded merely by this arithmetic observation. The inherited total-state
lower bound 15 is not increased by the one-sided bound alone.

### What the prime residues do and do not encode

`GoldenBase4ResidueBridge.lean` and its Scribe preserve the distinction between
Z(4^n), the actual input word, and Z(2n), the prime-axis exponent word for
4^n=2^(2n). The residue pair

\[
((4^n\bmod5),(4^n\bmod7))
\]

depends exactly on n mod 6. Its values in order are

```
(1,1), (4,4), (1,2), (4,1), (1,4), (4,2).
```

Their injectivity and period-six reduction are proved in the source. Modulo
three every power is one and no exponent information is obtained. Thus the
four-prime/5040 lane supplies a genuine congruence coordinate; the Euler-Mascheroni
constant is not a premise in this automaton argument.

The previous exploratory phase split separated the 144 rows by n mod 6 and
retained the three state-naming anchors in each subproblem. Each separate
four-slot relaxation was reported satisfiable; no combined satisfying table
was obtained. Such separate tables do not solve the joint problem. All phases
must use the same transition variables, so the relevant feasible set is the
intersection of the six phase constraints in one shared table space. A phase
label must not be added as free state memory to the candidate under test.

Chang-Miller's prefix theorem applies separately to 4^(a+6k). This exposes
valid prefixes in each phase, but does not fix outputs at arbitrary nonpower
prefixes or establish the required terminal error/power intersection. The
residue lemma alone cannot justify a stronger lower bound.

### The next finite problem

Five transient states give two unnamed extra G outputs and 32 Boolean E maps.
The same observation-preserving normalization therefore covers 3^2*2^5=288
cases. The earlier bounded attempt ended UNKNOWN; it was not a five-slot
refutation. For five-slot candidates, shared zero-generator constraints and
cross-phase constraints must remain attached to the same candidate table.
A complete five-slot refutation would imply s>=6 and remove (15,5); a relaxed
SAT model would still require a genuine recurrent realization and all-power
correctness. Neither conclusion follows from a timeout.

## 2026-09-06 finite-prefix barrier and completed source synchronization

This continuation gives an explicit twenty-state machine fitting the original
power observations through index 366 and failing at index 367. It establishes
a necessary sample extent for any twenty-state exclusion based on an initial
digit dictionary. It does not prove a new total-state lower bound or supply an
all-powers twenty-state upper construction. The original minimum remains open
in this work, and the reported Walnut 21/22 discrepancy remains unassigned.

### Repaired four-slot evidence and the current proof interfaces

The older appendix's references to stored numeric rows and compressed proofs
are historical. A later source repair removed malformed serialized copies and
retained `gap4_produce.cpp`, `rebuild_gap4.py`, `check_gap4_certificate.cpp`,
`test_gap4_rejection.py`, and `reproduce_gap4.sh` instead. The deterministic
producer regenerates all three complete proof parts. The audited rebuild gave
the same sample and proof bytes as the previously replayed originals. Hash
agreement checks integrity; the separate replay checks the proof steps. The
accepted totals remain 144 true power samples, 48 cases, 1,272,968 nodes,
420,692 branches, and 852,276 contradiction leaves. This supplies the external
four-slot exclusion and hence s>=5; it is not a new Lean numeric certificate.

The now-present `SkeletonSlotGapConstraintTransport` constructs actual finite
assignments from `SlotWitness` runs. The existing shared gap maps are inserted
as table values, actual prefix runs as trace values, and syntactic path-append
identities imply the original Selection equations. Fitted terminal observations
put these values into the observation domains. The endpoint is
`fitted_slots_induce_selection_solution`. Concrete certificate parsing, state
anchor normalization, and execution of the resulting million-node Lean value
are still separate obligations.

`SkeletonSlotProfileSymmetry` proves slot renaming while retaining the same
Skeleton: B becomes pi composed with B, C becomes C composed with inverse pi,
and G is renamed by inverse pi. Thus each gap map is conjugated, with no
self-loop deleted. For five slots the three observation-named anchors stay
fixed. Each remaining joint (G,E) profile has six possible values; sorting the
two unnamed profiles leaves 6+choose(6,2)=21 unordered pairs. Including the
three anchored Boolean E values gives 8*21=168 cases. This replaces the old
288-case enumeration without identifying equal-profile states or restricting
unused capacity. It is a complete symmetry cover, not a five-slot refutation.

### Why free long-tail readouts cannot strengthen a gap-only lower bound

`GoldenBase4ZeroTailForgetting.lean` was synchronized with its Scribe at
`729b114484d766aaf886115a3a941472deccc2de`. For every successful reference prefix
ending in the previous-one fiber and every terminal-zero length ell>=2,

\[
\Delta_4([u1\,0^\ell]_F)=
\begin{cases}3&\ell\text{ even},\\0&\ell\text{ odd}.\end{cases}
\]

The source proves this for all depths by finite core transitions and induction,
then uses the existing arithmetic correctness theorem. In the error coordinate,
put t=phi-1. A previous-one error satisfies -t<e<-t^3. Zero multiplies it by -t;
after at least two zeroes its absolute value is below 1/4, and its sign
alternates. The two possible floor differences are consequently three and zero.

For any fixed gap trace and fixed readouts at tail lengths zero and one, all
longer labels can be satisfied by the constant readout prescribed by parity.
The theorem `free_tail_completion_iff` proves both directions. This result
applies to independently chosen readouts; actual machines must retain the
common-map condition E_ell=F composed with A^(ell-1) composed with C. Therefore
long-tail observations can constrain recurrent capacity, but merely adding
them to the old free-readout relaxation cannot increase its transient bound.

The executed source-bound check validates 700 exact arithmetic tail cases,
256 pairs of fixed short readouts, and rejects two changed-table mutations.
These are finite checks. The all-depth Lean proof has not been compiled here.

### A concrete twenty-state candidate survives every index below 367

`GoldenBase4TwentyStatePrefixBarrier.lean` and its Scribe were committed at
`13cdd4e5f7c6f4b275467f5d44ba08f788278466`. The machine has thirteen
previous-zero states 0 through 12 and seven previous-one states 13 through 19.
Its start is zero, with zero output and a zero self-loop. The table is

```
zeroTarget = [0,8,7,6,5,4,4,3,3,2,2,2,1,12,11,11,10,9,8,8]
oneTarget  = [17,19,18,17,17,17,16,16,15,14,14,13,13,0,0,0,0,0,0,0]
output     = [0,3,3,3,3,0,0,0,0,0,1,1,1,1,1,2,2,2,2,3]
```

The last seven oneTarget entries are unused: the step definition makes a one
from any previous-one state undefined. Every permitted transition is present.
All twenty states are reachable, and there are seven distinct transient
output-return signatures. The table was discovered by identifying old
reference states 2 and 3 while retaining state 2's zero successor. This changes
transition behavior and is not the output- and transition-preserving quotient
excluded in the earlier section.

Against the unchanged M01 words and digit functions, the new source statements
are

\[
\forall n<367,\quad M_{20}(Z(4^n))=D_4(n),
\qquad M_{20}(Z(4^{367}))=1,\quad D_4(367)=0.
\]

The finite prefix comparison uses kernel-style `decide` proof bodies against
the reference machine, followed by the existing all-index arithmetic theorem.
Those proof bodies have not been executed by Lean in this session. Separately,
`check_twenty_state_prefix.py` reads the actual Lean vector literals and computes
all labels from integer square roots, without using the reference machine as
an oracle. It evaluates the canonical words at indices 0 through 1999 exactly.
The first failure is 367; the only other failure in that finite range is 1164.
No assertion about the complete infinite error set follows from that scan.

The index-367 word has 1057 bits. Its SHA-256 is
`6bcc16ae77b94c9423f921e1c103be2d13b85ead036f67fbf5c8ae31be1eadef`.
The source SHA-256 is
`1e937bdd9fd537f48c5583bcc5e3176ea29e10ef9163237d78cbc25407347048`.
The checker also validates all twenty access states, the seven signatures,
240 leading-zero cases, and rejection of altered zero-target, output, and type
guard data. No floating-point arithmetic is used.

### Consequence for the original lower-bound program

For any index set S contained in {0,...,366}, the same explicit machine fits
all observations in S. Thus no sound encoding of those observations can refute
all twenty-state typed candidates. The source theorem
`every_subprefix_has_twenty_state_witness` quantifies over arbitrary index
families, including repetitions. In particular, the old 144-row gap4 dictionary
with maximum index249 has a genuine (r,s)=(13,7) realization.

This does not weaken s>=5: the witness has seven transient states. It does
show that the (13,7) budget20 case on the old dictionary is satisfiable, rather
than an unresolved UNSAT computation. Any initial-prefix certificate proving
the total lower bound21 must include an index at least367. The single index367
eliminates this witness only; it does not establish that all other twenty-state
machines fail by that index.

To raise the inherited total lower bound15 to16, combine s>=5, s<=r and
r+s<=15. Setting r'=max(r,8) covers every candidate in one of

```
(10,5), (9,6), (8,7).
```

All three still require actual refutations. Earlier coupled searches on the
first250 inputs ended UNKNOWN. This continuation also tried exact-table CNF
and incremental candidate refinement for (8,7); fitted finite models were
checked against every generated clause and their selected true power labels,
but the final searches remained UNKNOWN. No partial proof log is promoted to
a refutation. The twenty-state prefix witness is the new definitive finite
result; it is neither a lower bound16 nor an all-powers upper bound20.

### External methods and current repository reuse

The original target remains Barnoff, Bright and Shallit's incomplete-input
DFAO problem, TCS1071 (2026),115843, DOI10.1016/j.tcs.2026.115843.
Heule and Verwer's exact SAT-based DFA identification (2010), DOI
10.1007/978-3-642-15488-1_7, supplies the established finite-inference setting.
Ulyantsev, Zakirzyanov and Shalyto, arXiv:1602.05028, supply explicit BFS/DFS
symmetry-breaking methods; their assumptions must be matched before reuse.

Brand, Faber, Held and Mutzel's ZykovColor work, arXiv:2504.04821 and ALENEX2026,
pp.142-155, studies merge/separate search with transitivity propagation through
IPASIR-UP. Its graph-coloring performance is not a performance guarantee for
this typed DFAO instance. The current repository `TracePartitionRefutation`
already provides equality closure, exhaustive merge/fresh branches, and a
simultaneous recurrent/signature capacity statement. Its abstract source
soundness must still be consumed by a complete numerical trace certificate.

Meng, An, Li, Turrini, Xu, Zhan and Zhang's *Efficient Decomposition
Identification of Deterministic Finite Automata from Examples*, SETTA2025,
proceedings online 1 April2026, DOI10.1007/978-981-95-7826-9_10,
arXiv:2509.24347v1, motivates compressed sample representations. Its encoding
allows a merged representative to be related to multiple candidate states.
Copying the APTA single-color constraint to an arbitrary compressed sample
node would silently remove candidates. No compressed-data completeness theorem
or claimed speedup on this instance is asserted in the present continuation.

The current PR review included both loning and AlyciaBHZ work. PR#5818 exposes
the existing binary-base language bridge; #5233 gives exact partial-signature
completion costs. Loning's current closure-barrier review in #5867 reinforces
that agreement between two implementations sharing a defect is not an
independent truth anchor. Here the finite witness uses the original M01
specification, while the separate executable labels come from exact integers.
The reverted #5837/#5857 module is not used as a new prerequisite.

### Executed validation and remaining verification

Reproduce the new finite witness with

```sh
python Evidence/D5/Automata/GoldenBase4/check_twenty_state_prefix.py \
  D5/S1/Digit/GoldenBase4TwentyStatePrefixBarrier.lean
python Evidence/D5/Automata/GoldenBase4/check_zero_tail_forgetting.py \
  D5/S1/Digit/GoldenBase4IntervalMachine.lean \
  D5/S1/Digit/GoldenBase4ZeroTailForgetting.lean \
  Blueprint/D5/S1/Digit/GoldenBase4ZeroTailForgetting.scribe.cs
```

The corresponding reports are `twenty_state_prefix_validation.json` and
`zero_tail_validation.json`. The two newly synchronized Lean modules have
paired Scribes for all seventeen public declarations, including ten theorems.
No new axiom, admitted proof, sorry, or native_decide is authored. Logical
review and exact executable checking are distinct from unperformed Lean
elaboration, kernel acceptance, and transitive axiom-closure inspection.
No new numerical minimum or first-priority claim is made.

## 2026-09-07 channel retraction and the unchanged numerical frontier

`D5/S0/Certificates/SkeletonChannelRetraction.lean` supplies a complete output-
normalization reduction for the existing partial Skeleton semantics. Its paired
Scribe covers all fifteen public declarations. The source commit is
`65add728b8ac43e4033006195c3a2231b8a02ce2`.

For arbitrary output maps f and g, preserve the start, zero edges and every
return target, replace recurrent outputs F by f composed with F, and replace
one signatures (d,next) by (g(d),next). Induction on the existing return blocks
proves exact evaluation transport:

\[
\operatorname{eval}_{K'}(w,c)
=\operatorname{Option.map}(h_c)(\operatorname{eval}_K(w,c)),
\quad h_R=f,\quad h_T=g.
\]

This includes failed partial runs. Each old used signature maps to a new used
signature, and every new signature is in that image. The resulting surjection
proves that the existing canonical state cost cannot increase. No injectivity
of f or g, no totality, and no reachability premise is needed.

For the radix-four sample problem take f(2)=0 and f(d)=d otherwise; take g(0)=1
and g(d)=d otherwise. Suppose the actual recurrent-channel sample labels avoid
two, and the transient-channel sample labels avoid zero. Those hypotheses concern
the authoritative observations, not the unknown candidate's unobserved outputs.
The retraction fixes every observed label. It also preserves the initial zero
output and initial zero self-loop. Therefore `normalized_sample_feasibility_iff`
proves that existence at the same canonical budget is equivalent to existence
with the reduced ranges

\[
F(R)\subseteq\{0,1,3\},\qquad G(T)\subseteq\{1,2,3\}.
\]

The equivalence does not claim that every original candidate already satisfies
those restrictions. It constructs a replacement candidate without increasing
cost. Different states with the same normalized outputs remain distinct unless
an independently justified signature quotient is applied. No ordinary self-loop
is forbidden and no missing edge is inserted.

The standard-library check exhausts all partial skeleton tables with one or two
recurrent states and four-valued outputs: 24,408 models, 1,462,320 evaluation
identities, including 773,372 undefined evaluations. Canonical cost strictly
decreases in 864 tested models. A changed-return mutation is rejected. Results
and source hashes are in `channel_retraction_validation.json`; run

```sh
python Evidence/D5/Automata/GoldenBase4/check_channel_retraction.py
```

The generic source has nine theorem proof bodies, with no new axiom or missing
proof placeholder. Logical review and finite exhaustive testing are completed;
Lean elaboration and kernel checking have not been executed. No formal numerical
DFAO lower bound follows from these tests alone.

The current search also tried rollback trace merging and shared macro-transition
encodings on true power samples. The tested budget-15 cases did not produce a
complete refutation. In particular, no lower bound sixteen or transient bound
six is asserted. The existing total-bound targets (10,5), (9,6), (8,7) remain.
The output normalization is a proved search reduction; a timeout remains an
unresolved computation, irrespective of the number of constraints examined.

The literature connection is the exact incomplete-data identification problem,
with sample compression preserving complete candidate semantics. The relevant
SETTA2025/2026 decomposition work and ALENEX2026 ZykovColor references are recorded
in the preceding appendix. Neither a compressed representative nor a normalized
output is licensed to carry a reference-state identity that the power samples
do not determine. The original power-only minimum remains the research target.
