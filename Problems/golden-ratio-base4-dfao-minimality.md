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
