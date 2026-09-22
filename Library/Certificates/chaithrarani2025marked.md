---
bibkey: chaithrarani2025marked
authors: Chaithra P; Shushma Rani; R. Venkatesh
year: 2025
title: "Marked multi-colorings and marked chromatic polynomials of hypergraphs and subspace arrangements"
doi: 10.48550/arXiv.2507.20847
url: https://arxiv.org/html/2507.20847v1
claim: "Section 8.1: for a simple hypergraph on a positive finite number of vertices, the reciprocal of its signed ordinary independence polynomial has nonnegative rational coefficients at every multiindex if and only if every edge has even cardinality."
strata_touched:
  - D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation
license: citation-only
triage: anchor
---

# Marked multi-colorings and marked chromatic polynomials of hypergraphs and subspace arrangements

## Source wording and scope

Quotations below preserve the prose verbatim, with mathematical glyphs and
whitespace normalized. Page numbers refer to the v1 PDF.

- Section 8.1, p. 23: “Let 𝒢 be a simple hypergraph. Then we have I(𝒢,−x)⁻¹ ≥ 0 if and only if all edges of 𝒢 must have even number of elements.”
- Section 3.1, p. 7: “Let n be a positive integer.”
- Definition 2(1), p. 7: “A hypergraph 𝒢 is called simple if for any e,f ∈ ℰ, we have |e| ≥ 2 and e ⊆ f implies e = f.”
- Definition 2(5), p. 7: “A subset I ⊆ 𝒱 is called independent if no edge of 𝒢 is entirely contained in I, i.e., e ⊈ I for all e ∈ ℰ.”

Definition 3 (p. 7) defines `I(𝒢,x)` as the sum of `∏_{v∈I} x_v`
over all independent sets, including the empty set. The ambient series have
rational coefficients (p. 1); nonnegativity is coefficientwise (p. 2).
The introductory Conjecture 1 is on p. 5; the full equivalence targeted here
is the statement in Section 8.1 on p. 23. It concerns the ordinary polynomial,
without marked vertices or a restriction to squarefree coefficients.

Relabel the source `[n]` as `Fin n`. Define `indicator S` to be the exponent
vector equal to one on `S` and zero elsewhere, and

```lean
signedIndependence E : MvPowerSeries (Fin n) ℚ :=
  ∑ S ∈ Finset.univ.powerset.filter (fun S => ∀ e ∈ E, ¬ e ⊆ S),
    MvPowerSeries.monomial (indicator S) ((-1 : ℚ) ^ S.card)
SourceSimple E :=
  (∀ e ∈ E, 2 ≤ e.card) ∧ (∀ e ∈ E, ∀ f ∈ E, e ⊆ f → e = f)
claim := ∀ n : ℕ, 0 < n → ∀ E : Finset (Finset (Fin n)),
  SourceSimple E →
    ((∀ m : Fin n →₀ ℕ,
        0 ≤ MvPowerSeries.coeff m (signedIndependence E)⁻¹) ↔
      ∀ e ∈ E, Even e.card)
```

These are the semantic definitions and full proposition, written schematically
with `n` implicit in the first two definitions. Simplicity ensures the empty
set is independent, so the signed polynomial has constant coefficient one and
its reciprocal is the actual formal power-series inverse.

## Counterexample and attribution

The source supplies the conjecture and definitions. The repository refutation
uses vertices `0,…,7`, labeled `a1,a2,a3,b1,b2,b3,s,t`, and edges
`{6,7,0,1}`, `{6,7,1,2}`, `{6,7,2,0}`, `{6,7,3,4}`, `{6,7,4,5}`,
`{6,7,5,3}`. Six distinct four-element sets satisfy both simplicity clauses
and have even size. Their full squarefree inverse coefficient is `−14`.

For a subset `T`, let `i=|T∩{0,1,2}|`, `j=|T∩{3,4,5}|`, and
`d=(1,1,0,−4)`. The certificate is `c(T)=1` unless both `6,7` belong to
`T`, in which case `c(T)=2−d(i)d(j)`. With `f(U)=(−1)^|U|` for
independent `U` and zero otherwise, it satisfies `c(∅)=1` and
`c(T)=−∑_{∅≠U⊆T} f(U)c(T∖U)` for nonempty `T`. Squarefree exponent
decompositions are exactly subset/complement pairs. Induction on cardinality
therefore identifies this certificate with coefficients of the actual inverse.
At the full set, `c(T)=2−(−4)(−4)=−14`. This refutes the sufficient direction
of the equivalence. The production Lean module
`D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.lean` contains
the complete finite certificate and public theorem `result : Not claim`. The
production source compiles with compiler-checked result axiom closure
`[propext, Classical.choice, Quot.sound]`; the certificate
proves the actual inverse coefficient `−14` at the full squarefree multiindex.

## Verified locator

- DOI: 10.48550/arXiv.2507.20847
- URL: https://arxiv.org/html/2507.20847v1
- Version: arXiv:2507.20847v1; PDF pp. 1, 2, 5, 7, 23 as specified above.
- Retrieved primary HTML SHA-256:
  `39e8da49ecd6878f0cc909c3ec2b554d78ca66dda89f363a3450360ef36ca700`.

## Bounded literature status

The supplied bounded source check covers v1 and related work of Zhang–Dong
(2020), DOI `10.1016/j.disc.2020.112134`, and Foissy (2026), DOI
`10.1016/j.aam.2026.103067`. No later full resolution was located within
that check. This does not establish exhaustive absence or worldwide priority.
The source reports Sage checks through ten vertices, which conflicts with the
eight-vertex witness. The tested families and code were unavailable to the
supplied check; the cause of this discrepancy is undetermined.
