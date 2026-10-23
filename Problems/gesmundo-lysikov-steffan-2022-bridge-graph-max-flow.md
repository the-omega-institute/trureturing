---
slug: gesmundo-lysikov-steffan-2022-bridge-graph-max-flow
bibkey: gesmundo2025bridge
doi: 10.1007/s00031-024-09863-2
url: https://arxiv.org/abs/2212.09794v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowMinCut.result
---

# Quantum max-flow equals min-cut in the symmetric bridge regions

## Problem

F. Gesmundo, V. Lysikov and V. Steffan, *Quantum max-flow in the bridge graph*,
arXiv:2212.09794v2, Conjecture 1.4 (also Conjecture 3.14), state:
“Let $(a,b),(a',b')\in U_w\cup V_w\cup W_w$. Then”
$\operatorname{QMaxFlow}=\operatorname{QMinCut}=\min\{ab',a'b\}$.
Conjecture 3.15 is the width-three case. The
[literature note](../Library/QuantumBounds/gesmundo2025bridge.md) gives the
verbatim source clauses and locators. [#14652](https://github.com/the-omega-institute/trureturing/issues/14652)
records the complete target and literature scope.

## Motivation

`QuantumMaxFlowMinCut.result` proves both equalities at width three, for every
positive natural dimension quadruple in the two symmetric regions. The matrices
are over $\mathbb C$. The source letters $(a,b,a',b')$ correspond to Lean's
$(a,b,c,d)$, and the delivered flattening is the transpose of the source's;
rank is invariant under transpose. The attained supremum definition represents
the source's maximum, by `QuantumMaxFlowBound.QMaxFlow_attained`.

## Gap

The preregistration records the source, MathDB and citing-work searches; no
settlement was found in that searched scope. This is a bounded literature
reading, not an exhaustive originality claim. The width-three Lean conclusion
supplies the hypothesis of source Proposition 3.18. That general-width
implication remains a literature theorem rather than a formalized Lean bridge.

## Route

For $a>0$ and $t=b/a\ge1$, the smaller root of $t^2-3t+1$ is below $1$.
Consequently $a\le b\le(3+\sqrt5)a/2$ is equivalent to
$a\le b$ and $a^2+b^2\le3ab$. Apply the same calculation to $(c,d)$.
On this domain the source's cut formula $\min(3ac,ad,bc)$ equals
$\min(ad,bc)$; `QuantumMaxFlowBound.cone_QMinCut` proves this integer equality.

The construction uses rational three-slice matrices. A backward cyclic shift
and a forward cyclic shift with closing weight $1/2$ interact through floor
selectors. Its strictly positive shift is $\kappa=p$. The exact higher-order
Schur equations reduce full rank to the shifted cyclic resolvent, and a balanced
interval count forces its relevant periodic recurrence to vanish. Short and
long reservoirs give every strict base. Rational-to-complex transfer preserves
rank. Castling preserves the deficit, and strong induction on $b+d$ reaches
all cone pairs, including square, mixed and descended cases.

## Falsifier

A positive quadruple satisfying both cone inequalities and whose maximum
complex three-slice rank is below $\min(ad,bc)$ would falsify the width-three
claim. Failures of a particular construction outside its stated conditions
are method boundaries, not counterexamples to the proved conjecture.

## Evidence

The seven supporting modules have admission basis `escape-witness`, with
content theorems `QuantumMaxFlowBound.widthTwo_proved`,
`CastlingDeficit.castling_proved`, `FloorSelectorCycles.balanced_cycle_zero`,
`CyclicResolvent.schur_rank`, `ShiftPencilBlocks.pencil_rank_of_le`,
`ReservoirSchur.short_short_witness` and `LongReservoir.base_witness`.
The settling `QuantumMaxFlowMinCut.result` has admission basis
`open-problem-resolution` (#14652; Proved). Their axiom closures are contained
in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit of the 68 public theorems is unfinished:
[#14762](https://github.com/the-omega-institute/trureturing/issues/14762).
The result is a proof, so the designated-refutation exemption does not apply.
Missing source-family reconstruction and variation/sensitivity/dependence
proofs are audit obligations; they do not replace or weaken the mathematical
statements.

## Triage

### What the settlement shows

- **Proved — rational width-three construction.** The symbolic slices use backward
  and forward cyclic permutations, closing weight $1/2$, floor selectors and
  $\kappa=p>0$. `ReservoirSchur.short_short_witness` and
  `LongReservoir.base_witness` give the rank witnesses. These are arbitrary-dimension
  constructions, not a bounded enumeration of matrix certificates.
- **Proved — exact Schur complement and balance.**
  `CyclicResolvent.schur_rank` obtains $\min(AD,BG)$ for every positive shift
  under $0<B\le A$ and $0<D\le G$.
  `FloorSelectorCycles.balanced_cycle_zero` provides the balanced periodic
  recurrence step; the short and long reservoir equations yield full rank on
  every strict same-depth base in `LongReservoir.base_witness`.
- **Proved — castling transport.** `CastlingDeficit.castling_proved` preserves the
  deficit, and `QuantumMaxFlowMinCut.result` uses simultaneous cone descent
  to reach the entire cone. Rational witnesses transfer to complex matrices
  through `QuantumMaxFlowBound.rationalWitness_full_rank`.
- **Proved via literature — general width.** Source Proposition 3.18, page 20,
  derives Conjecture 1.4 for every $w\ge3$ from the delivered width-three
  conclusion. The implication is a literature reading with the source's
  hypotheses; the implication is not formalized in this delivery. The source results that take the
  symmetric-region equality as a premise can use this conclusion at width
  three and Proposition 3.18 for the general-width premise.
- **Computed — $\kappa=0$ core boundary.** For multiplicities $(3,2,4,3)$ the
  unshifted cyclic core has exact rational rank $7$, against target $8$.
- **Computed — $p=0$ extension boundary.** With $1\le a,c\le14$, both computed
  depths zero, ordered positive cone pairs and positive width-two defect,
  the literal extension is deficient on $261/3364$ pairs over
  $\mathbb F_{1000003}$. This finite-field statistic is not an exact rational
  count. The specific dimension pair $(5,13),(7,18)$ has exact rational rank
  $88$ against target $90$, so the literal extension fails over $\mathbb Q$.
- **Proved in the source — strict gaps outside the symmetric region; not formalized here.**
  Corollaries 1.2–1.3 and Theorem 3.8(2) establish
  $\operatorname{QMaxFlow}<\operatorname{QMinCut}$ outside the symmetric region.
  For $w=3$, $z=(1,3,8)$, $p=1$ and $\alpha=\beta=1$, the two pairs
  $(a,b)=(a',b')=(4,11)$ lie in $X_3$, outside the cone:
  $4^2+11^2=137>132=3\cdot4\cdot11$.
  The source formula gives $\operatorname{QMaxFlow}=43<44=\operatorname{QMinCut}$.
- **Proved — the symmetric conjecture in source §1.3(1).**
  `QuantumMaxFlowMinCut.result` settles its width-three case; source Proposition 3.18
  supplies general width as literature evidence.
- **Open — other graphs and periodic translation-invariant matrix product states.**
  The questions in source §1.3(2) are outside the scope of these declarations.

Source §1.3 states exactly (arXiv:2212.09794v2, page 7):

> 1.3. Open questions. We identify some open ends of this work.
>
> (1) One open task is Conjecture 1.4. The reduction discussed in Section 3.4 guarantees
> that the case w = 3 is equivalent to the full conjecture.
>
> (2) We believe that methods similar to ours can be applied to graphs that are not
> bridge graphs. For example, it would be interesting to see if one can calculate
> the quantum max-flow in translation-invariant matrix product states with periodic
> boundary conditions – which is the main example in prior work on the quantum
> max-flow where it was used to show separations between quantum min-cut and
> quantum max-flow [GLW18].
- **Proved — independence from source Theorem 3.1.**
  `CastlingDeficit.castling_proved` is derived from the module's field-linear
  algebra construction. It does not assume the source's castling theorem.

### Reproducible boundary computation

Experiment entry: [`docs/reports/gesmundo-lysikov-steffan-2022-bridge-graph-max-flow/check.py`](https://github.com/the-omega-institute/trureturing-experiments/blob/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/gesmundo-lysikov-steffan-2022-bridge-graph-max-flow/check.py) in `the-omega-institute/trureturing-experiments` at `602ec65402d492351ebc19230b04caa93001cda8`. The program is run with `python3 check.py` (NumPy, SymPy). Exit code: 0. Source SHA-256: `9df34d66155c6e0c369f70e756f688dac611e7b0d6e3d8297631d329a1d22f9a`.
It produces both computed bullets above: the $\kappa=0$ core rank $7$ against target $8$; $261/3364$ deficient pairs over $\mathbb F_{1000003}$; and the exact rational rank $88$ against target $90$ for the dimension pair $(5,13),(7,18)$.

## ASSUMED-UNVERIFIED

The literature search is bounded to the scope in #14652. Proposition 3.18 is
not part of the delivered Lean proof. Successful kernel checks do not establish
that every source-family audit target is `DTR-Declared`; #14762 states the
missing registration evidence. No uniform extension of the boundary experiment
is claimed.
