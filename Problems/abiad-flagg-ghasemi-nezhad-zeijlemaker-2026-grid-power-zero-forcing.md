---
slug: abiad-flagg-ghasemi-nezhad-zeijlemaker-2026-grid-power-zero-forcing
bibkey: abiadflaggghaseminezhadzeijlemaker2026powers
doi: null
url: https://arxiv.org/abs/2610.03892v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.result
---

## Problem

Abiad, Flagg, Ghasemi Nezhad and Zeijlemaker, *The Zero Forcing Number of Graph Powers*, arXiv:2610.03892v1, §3, Conjecture 12 (`conj:grid`):

> Let b≥1, k≥1 and ℓ≥k+1. Then Z((P_b □ P_ℓ)^k)=bk.

The endpoint is refutation of this full universal statement as printed. It does not settle a corrected b≤ℓ conjecture or assert author intent.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every natural b,k,ℓ | `∀ b k ell : ℕ` in `claim` |
| b≥1, k≥1, ℓ≥k+1 | `1 ≤ b → 1 ≤ k → k + 1 ≤ ell →` |
| P_n is the n-vertex path | Mathlib `pathGraph n` on `Fin n`, adjacency of consecutive values |
| Cartesian product | Mathlib `pathGraph b □ pathGraph ell`, on `Fin b × Fin ell` |
| Distinct vertices at base distance ≤k | `graphPower`: `u ≠ v ∧ G.edist u v ≤ (k : ℕ∞)` |
| Ordinary unique-white-neighbor forcing | Frozen `ZeroForcingThree.Black` and `IsZeroForcing` |
| Minimum initial cardinality | Frozen `ZeroForcingThree.zeroForcingNumber`, an infimum of attainable finite cardinalities |
| Equality to bk | `zeroForcingNumber (...) = b * k` |
| Negation of the entire assertion | `result : ¬ claim` |

All admissible grids are connected and finite: positive path factors are connected, and Cartesian products preserve reachability. Extended graph distance is used directly, so no disconnected-distance collapse or k=1-only power definition affects the universal statement. The coordinate correspondence is (i,j)↦(i+1,j+1). No source hypothesis is dropped or added. `Black.force` can also derive a vertex already black, which adds no vertex and does not alter the closure; when its target is white, its premises say precisely that the source is black and every other neighbor is black.

## Motivation

Tier 1: a recent explicitly published named conjecture, preregistered before the formal probe in [#16240](https://github.com/the-omega-institute/trureturing/issues/16240). The targeted issue is the literal quantified assertion, not the classical grid formula. Source definitions and limitations are recorded in `Library/GraphInvariants/abiadflaggghaseminezhadzeijlemaker2026powers.md`.

## Gap

The source's preceding paragraph cites Z(P_b □ P_ℓ)=min(b,ℓ) at k=1 and reports exhaustive attainment of bk on a range containing (3,2,1). These conflict with its unrestricted conjecture. Independent source/context scans find no b≤ℓ convention; current arXiv v1 source hashes agree with intake and v2 returns 404. No claim about a corrected statement or the authors' intended domain follows.

The preregistration's bounded arXiv, Crossref, formal-conjectures and repository ownership searches found no exact prior adjudication. Additional focused GitHub code search for zero forcing found the unrelated TxGraffiti assertion at formal-conjectures revision 72dad3524e0174dea703f267664d3bc9298803a0; it contains no proved grid-power result. Repository searches include private helpers; the existing general zero-forcing API is reused. Pinned Mathlib supplies paths, Cartesian products and extended-distance interfaces, but no zero-forcing API or exact settlement was found. `make search-atoms SOURCE=2610.03892 TEXT="zero forcing" LIMIT=25` returned no atom.

## Route

Take b=3, k=1 and ℓ=2. Mathlib's `edist_le_one_iff_adj_or_eq` identifies the first distance power with the base graph. Name vertices A=(0,0), B=(0,1), C=(1,0), D=(1,1), E=(2,0), F=(2,1). Initially blacken A and B, then force A→C, B→D, C→E, D→F. The imported minimum definition and `Nat.sInf_le` give Z≤2; the universal conjecture would give Z=3.

## Falsifier

The complete unordered edge list is AB, AC, BD, CD, CE, DF, EF. When A forces C its other neighbor B is black; when B forces D its other neighbor A is black. When C forces E its other neighbors A,D are black; when D forces F its other neighbors B,C are black. Thus all six vertices become black from two initial vertices, and 2<3. Exact Z and the alternative (4,3,2) witness are not needed or claimed.

## Evidence

The designated Lean theorem is `D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.result`. The claim definition has literal type `Prop` and the theorem is written with literal type `Not claim`. The only new definitions are `graphPower` and `claim`; the only new theorem is `result`. All force certificates and the k=1 distance specialization are local terms on its live proof path. The directly reused frozen owner is `D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree`, with frozen module identity `sha256:09006a0e8fc30987321439153310f86ebfc30d7e8836789450cd5f5b90fd43eb`; its `Black`, `IsZeroForcing` and `zeroForcingNumber` declarations supply the forcing semantics.

`proof_shape: bind-only`; `escape_witness: bind-only`; `admission_basis: open-problem-resolution`. The proof instantiates frozen forcing constructors and pinned distance/minimum interfaces and normalizes finite facts. No classical mathematical novelty is claimed. The computational kind is `certified-instance` with utility `refutes` pointing exactly to `claim` and `result`. The designated result has the §3.9 four-slot registration exemption; no other new public theorem needs registration.

This settlement addresses only the literal printed assertion. Resolution credit requires the independent review triplet, required CI, a merged PR and subsequent dev verification; canonical freezing alone does not complete delivery.

## Triage

### What the settlement shows

- **Refuted by `GridPowerZeroForcingRefutation.result`:** the full Conjecture 12 as printed. The failure mechanism is that the unrestricted domain permits b>ℓ, while the k=1 grid can be forced along the other coordinate using fewer than b initial vertices.
- **Literature-attested, not new:** the source cites the classical k=1 value min(b,ℓ). This refutation uses only explicit forces at (3,2,1).
- **Source assertion contradicted:** the reported exhaustive attainment over b≤3, k≤3, k+1≤ℓ≤10 includes the refuting triple. Its underlying computational program and data are unavailable here; no explanation of the discrepancy is asserted.
- **Open here:** equality under the additional restriction b≤ℓ, any exact formula at general k, and any new family classification. These are separate questions and receive no resolution credit from this result.
- **Unaffected logical scope:** the conjecture is an equality strengthening of the preceding upper bound. The witness Z≤2<3 does not contradict that upper bound Z≤bk or the separate path, cycle and spider results. The source uses `conj:grid` only at its statement; no later theorem cites it. Those results are not re-proved or independently audited here.

## ASSUMED-UNVERIFIED

Global absence of a correction or earlier exact adjudication beyond the bounded searches is unverified. The additional current arXiv API request returned HTTP 429 and contributes no negative evidence; current abstract, HTML and original-source retrievals succeeded. Author intent is unverified. The bounded search and formal refutation alone establish neither publication nor KPI credit or host-goal completion.
