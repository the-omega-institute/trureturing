---
slug: even-hypergraph-inverse-positivity-refutation
bibkey: chaithrarani2025marked
doi: 10.48550/arXiv.2507.20847
url: https://arxiv.org/html/2507.20847v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation
---

# Even-hypergraph inverse-positivity refutation

## Problem

Section 8.1 of arXiv:2507.20847v1, PDF p. 23, states: “Let 𝒢 be a simple
hypergraph. Then we have I(𝒢,−x)⁻¹ ≥ 0 if and only if all edges of 𝒢 must
have even number of elements.” Quotations preserve the prose verbatim;
mathematical glyphs and whitespace are normalized.

Section 3.1, p. 7, begins: “Let n be a positive integer.” Definition 2(1),
p. 7, says: “A hypergraph 𝒢 is called simple if for any e,f ∈ ℰ, we have
|e| ≥ 2 and e ⊆ f implies e = f.” Definition 2(5), p. 7, says: “A subset
I ⊆ 𝒱 is called independent if no edge of 𝒢 is entirely contained in I,
i.e., e ⊈ I for all e ∈ ℰ.”

Definition 3, p. 7, includes every independent subset, including the empty
set, in the ordinary independence polynomial. The coefficient ring is rational
(p. 1) and positivity is coefficientwise (p. 2). Relabel `[n]` as `Fin n`.
Here `indicator S` is one on `S` and zero elsewhere, and `signedIndependence E`
is the sum, over all independent `S ⊆ Fin n`, of the monomial with exponent
`indicator S` and coefficient `(-1 : ℚ)^S.card`. The precise claim is

```lean
∀ n : ℕ, 0 < n → ∀ E : Finset (Finset (Fin n)),
  ((∀ e ∈ E, 2 ≤ e.card) ∧
    (∀ e ∈ E, ∀ f ∈ E, e ⊆ f → e = f)) →
  ((∀ m : Fin n →₀ ℕ,
      0 ≤ MvPowerSeries.coeff m (signedIndependence E)⁻¹) ↔
    ∀ e ∈ E, Even e.card)
```

The inverse is in `MvPowerSeries (Fin n) ℚ` and all multiindices are quantified.
There is no marked-vertex parameter. The scope is the full Section 8.1
equivalence, also introduced by Conjecture 1 on p. 5.

## Motivation

Even edge cardinality is proposed as a complete characterization of inverse
positivity. A faithful refutation must satisfy source simplicity and obtain a
negative coefficient of the actual inverse of the source polynomial. A single
squarefree coefficient can disprove positivity at all multiindices.

## Gap

The supplied bounded check of v1 and related Zhang–Dong (2020), DOI
`10.1016/j.disc.2020.112134`, and Foissy (2026), DOI
`10.1016/j.aam.2026.103067`, located no later full resolution. This is not an
exhaustive absence or priority claim. The source's reported Sage checks through
ten vertices conflict with the eight-vertex witness. Their code and tested
families were unavailable; no explanation for the discrepancy is established.

## Route

Use `Fin 8`, labeled `a1,a2,a3,b1,b2,b3,s,t`, with edges
`{6,7,0,1}`, `{6,7,1,2}`, `{6,7,2,0}`, `{6,7,3,4}`, `{6,7,4,5}`,
`{6,7,5,3}`. Six distinct four-element sets have even cardinality at least
two and satisfy the inclusion clause of simplicity.

For `T ⊆ Fin 8`, set `i=|T∩{0,1,2}|`, `j=|T∩{3,4,5}|`, and
`d=(1,1,0,−4)`. Put `c(T)=1` unless both `6,7` belong to `T`, and
`c(T)=2−d(i)d(j)` otherwise. If `f(U)=(−1)^|U|` for independent `U`
and zero otherwise, the finite certificate is
`c(∅)=1` and `c(T)=−∑_{∅≠U⊆T} f(U)c(T∖U)` for every nonempty `T`.
The constant coefficient of the signed independence polynomial is one.
Every decomposition of `indicator T` corresponds uniquely to `U ⊆ T`
and `T∖U`; induction on cardinality thus identifies the certificate with
the actual inverse coefficients. For the full set, the value is
`2−(−4)(−4)=−14`, contradicting the even-edges-to-positivity implication.

The same arithmetic can be seen from `A=∏(1−a_i)`, `B=∏(1−b_i)`,
`J_A=1−a1−a2−a3`, `J_B=1−b1−b2−b3`. The signed polynomial is
`F=(1−s−t)AB+stJ_AJ_B`, and `[st]F⁻¹=2/(AB)−J_AJ_B/(A²B²)`.
Each triple coefficient in `J_A/A²` or `J_B/B²` is `8−3·4=−4`, yielding
`2−16=−14`. This is an ordinary algebraic explanation of the same witness,
not an additional formal proof.

## Falsifier

Failure of a source hypothesis, an incorrect independence polynomial, or a
nonnegative full squarefree coefficient in its actual inverse would invalidate
this counterexample. Failure of the finite convolution identity at any of the
256 subsets would invalidate this particular certificate and its formal route.

## Evidence

- The complete 256-subset certificate and unconditional public `result : Not claim`
  are in `D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.lean`.
- The production Lean source compiles in the pinned environment with exit 0.
- The production module's semantic declarations are `indicator`,
  `signedIndependence`, `SourceSimple`, `claim`, and `result`; its reported
  compiler-checked axiom closure is `[propext, Classical.choice, Quot.sound]`, with no `sorry`,
  private axiom, or `native_decide`.
- The certificate uses `decide +kernel` for all 256 subsets and proves the
  actual inverse coefficient at the full squarefree multiindex is `−14`, so
  the result refutes the full source equivalence over all multiindices.
- Primary HTML SHA-256:
  `39e8da49ecd6878f0cc909c3ec2b554d78ca66dda89f363a3450360ef36ca700`.
  Source locators are the v1 PDF pages cited in Problem.

## Triage

`theorem` classifies the target proposition; it is not a completion status.
The ordinary counterexample refutes the sufficient direction of the published
equivalence, and the kernel-checked theorem establishes that refutation. No
claim is made here against the other direction or against a different
conjecture with added hypotheses.

## ASSUMED-UNVERIFIED

The bounded literature check covers the cited v1 and the listed related works;
it does not establish exhaustive absence or worldwide priority. The source's
reported Sage checks through ten vertices conflict with the eight-vertex
witness, and the unavailable tested families and code leave the cause of that
discrepancy unresolved. These are source and prior-art boundaries, not gaps in
the Lean refutation.
