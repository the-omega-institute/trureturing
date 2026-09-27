[Index](../../marked_head_profile.md) · [Future-risk state](../321-384/334-same-chain-overlap-and-future-risk-certificates.md) · [Complete-event-law ambiguity](../../problem-details/43-sharp-first-hit-ambiguity-with-identical-complete-event-laws.md)

# Exact continuation counts require the joint future residue histogram

For a fixed finite inventory of permitted future moduli, the coarsest
information determining all future survivor counts is one explicit
joint residue histogram. Separate histograms for every permitted next
action need not remain sufficient after a deletion. An actual pair
of odd-distinct covering prefixes demonstrates the failure.

These are ordinary CRT and inclusion-exclusion derivations and exact
research checks, not new Lean certification or a literature-priority
claim. The observed output is the **exact survivor cardinality**.
Minimality for the weaker empty/nonempty output is not asserted.
None of these state descriptions supplies the positivity bound needed
for unrestricted Erdős #7.

## Fixed future inventory and its canonical state

Fix `L>0`, a survivor set `H subset Z/L`, a used-modulus set `U`,
and a finite set `F` of permitted unused future moduli, disjoint from
`U`. Each modulus in `F` may be used at most once, with an arbitrary
literal residue. The E7 specialization requires all moduli in `U,F`
to be odd and greater than one, with every used modulus dividing `L`.
Put

\[
 N=\operatorname{lcm}(F),\qquad B=\gcd(L,N),\qquad
 K_B(b;H)=|\{h\in H:h\equiv b\pmod B\}|,
 \tag{FH1}
\]

where the empty LCM is one. For two sources `H,G` with the same
`L,U,F`, the following statements are equivalent:

1. Their complete histograms `K_B` agree.
2. For every sequence of distinct moduli from `F`, including the empty
   sequence, and every choice of their literal phases, the final
   survivor cardinalities agree in the actual final LCM period.

**Sufficiency.** Work first in the common period `T=lcm(L,N)`.
For any subset `S` of selected future events, let `n_S` be the LCM
of its moduli. If its phases are incompatible, its intersection is
empty. Otherwise the intersection is a class `a_S mod n_S`. The
number of lifted old survivors in that class is exactly

\[
 \frac{T}{\operatorname{lcm}(L,n_S)}
 K_{\gcd(L,n_S)}(a_S;H).
 \tag{FH2}
\]

Every gcd in FH2 divides `B`, so the required count is a marginal
of `K_B`. Inclusion-exclusion determines the survivor count for any
continuation in period `T`. Divide by `T/L_S`, where `L_S` is the
actual final period of that continuation, to obtain its actual count.

**Necessity.** Fix an integer `b` and give every modulus in `F`
phase `b`. For `S subset F`, let `C_S` denote the survivor count
after exactly those deletions, lifted to `T` by multiplying its
actual count by `T/lcm(L,lcm(S))`. Then

\[
 \boxed{K_B(b;H)=\sum_{S\subseteq F}(-1)^{|S|}C_S.}
 \tag{FH3}
\]

Indeed, for each lifted old point, writing `f_m` for membership in
the class `b mod m`, the sum of its contributions is

\[
 \sum_{S\subseteq F}(-1)^{|S|}\prod_{m\in S}(1-f_m)
 =\prod_{m\in F}f_m.
\]

This is the indicator of `b mod N`. CRT gives exactly one such
lift for each old survivor congruent to `b mod B`. Thus all exact
continuation counts recover the complete histogram. For empty `F`,
FH3 just recovers `K_1=|H|` from the empty continuation.

Consequently `K_B` identifies exactly the equivalence classes of this
specified future-count task. Fixed phases, restricted action sequences,
or an emptiness-only readout define different tasks and can have
coarser quotients.

## An update using only the stored histogram

Apply an available action `a mod m`, with `m in F`. Set

\[
 \begin{aligned}
 L'&=\operatorname{lcm}(L,m),&F'&=F\setminus\{m\},\\
 B'&=\gcd(L',\operatorname{lcm}(F')),&g&=\gcd(L,B'),\\
 h&=\gcd(L,\operatorname{lcm}(m,B')),
 &t&=\frac{L'}{\operatorname{lcm}(L,B')}.
 \end{aligned}
\]

Both `g` and `h` divide the old `B`. For every `b mod B'`,

\[
 \boxed{
 K_{B'}(b;H')=tK_g(b;H)
 -{\bf1}_{a\equiv b\ (\mathrm{mod}\ \gcd(m,B'))}K_h(s;H),
 }
 \tag{FH4}
\]

where in the compatible case `s` solves `s=a mod m`, `s=b mod B'`.
It is defined modulo `lcm(m,B')`; its representative does not affect
`K_h`. The second term is omitted in the incompatible case.

The first term counts all old lifted survivors in the `b` cell.
Since `B'|L'`, the deleted intersection satisfies
`lcm(L,m,B')=L'`; hence every compatible old survivor has exactly
one deleted lift. All needed `K_g,K_h` are marginals of stored `K_B`.
Thus `(L,U,F,K_B)` is closed under legal updates, including LCM growth.
The inventory and used labels remain part of the state.

## Every immediate histogram can agree and still fail dynamically

Take `L=105`, used moduli `U={15,21,35,105}` and the actual prefixes

| History | Phase mod 15 | Phase mod 21 | Phase mod 35 | Phase mod 105 |
| --- | --- | --- | --- | --- |
| A | 0 | 2 | 0 | 8 |
| B | 5 | 0 | 5 | 3 |

Both leave 90 survivors and have identical complete histograms

\[
 K_3=(28,34,28),\qquad K_5=(11,20,20,19,20).
\]

Restrict the permitted future inventory to `F={3,5}`. Both are unused.
These two histograms supply every possible immediate gcd channel,
so every one-step count agrees for every phase of either available
modulus. But `K_15(0)` equals zero in A and five in B. Appending
`0 mod 3` and then `0 mod 5` gives

\[
 \begin{array}{ll}
 A:&90\longrightarrow62\longrightarrow51,\\
 B:&90\longrightarrow62\longrightarrow56.
 \end{array}
 \tag{FH5}
\]

All six moduli in each completed prefix are distinct odd integers
greater than one. The already-used label 15 cannot be used again,
but its histogram is still needed as the joint observation of the
two unused actions 3 and 5. The correct future base here is `B=15`.
FH5 refutes dynamic sufficiency of the separate immediate histograms;
it is not a covering counterexample.

## Unrestricted future exact counts recover the whole source

Let `L` be odd and every used modulus divide `L`. The single future
modulus `3L` is odd, greater than one, unused and larger than every
used modulus. For a literal phase `a mod L`, its exact update is

\[
 |H'_a|=3|H|-K_L(a;H)=3|H|-{\bf1}_H(a).
 \tag{FH6}
\]

Thus any summary determining the current count and all permitted
next exact counts must distinguish every distinct `H` at fixed `L,U`.
This remains true if future moduli must increase numerically.

This is information sufficiency, not a storage, runtime, symbolic
description-length or all-subsets-reachability lower bound. A source
can still have a short symbolic representation. In particular FH6
cannot distinguish nonempty sources using only the next emptiness
bit: every nonempty `H` stays nonempty after this action. Coarser
certificates for noncoverage remain possible.

## Implementation and existing-result boundary

[future_residue_histogram_state.py](../../frontier/cover-geometry/future_residue_histogram_state.py)
provides the actual-history constructor, fixed-inventory profile,
CRT update and inversion from continuation counts. Its controls
check 66,928 update cells and 2,208 full-profile reconstructions,
including every source subset for the specified small periods and
inventories, and reconstruct FH5 from the literal prefixes. The
universal statements follow from FH2--FH4, not bounded enumeration.

The existing [effective-resolution derivation at dev 4c08d06c5a](https://github.com/the-omega-institute/trureturing/blob/4c08d06c5a111eaf1d9799d8fe2fb9a31e156b9c/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_RESOLUTION.md)
already gives the exact one-step formula, scalar insufficiency and
the fact that all-divisor histograms include `K_L`. The existing
`ControlledBehaviorUniversality.controlled_behavior_universal_property`
supplies the generic minimal quotient by all finite controlled-word
observations. No replacement or renamed Lean wrapper is introduced.
FH1 explicitly computes the equivalence classes for this arithmetic
task; FH4 supplies their CRT update.

Report 334 retains richer matching and phase data for future weighted
risk. Problem-details 43 separates complete single-sample event laws
under clipping and first-hit dynamics. Those weighted tasks differ
from the deterministic deletion counts considered here. The new
arithmetic identification and actual FH5 example are elementary
specializations, with no literature originality claim and no
unrestricted covering conclusion.
