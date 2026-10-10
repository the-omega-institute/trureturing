---
slug: galke-van-luijk-wilming-2023-renyi-sufficiency
bibkey: galke2023renyisufficiency
doi: 10.48550/arXiv.2304.12989
url: https://arxiv.org/abs/2304.12989v6
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation.result
---

# Equal minimal Rényi profiles without positive interconversion

## Problem

N. Galke, L. van Luijk and H. Wilming, *Sufficiency of Rényi divergences*, arXiv:2304.12989v6, Section 3.3, Conjecture 22 (IEEE Transactions on Information Theory 70(7), 5057–5076, DOI 10.1109/TIT.2024.3376395), assert:

> Let $(\rho_1,\sigma_1)$ and $(\rho_2,\sigma_2)$ be pairs of density operators on quantum system $S_1$ and $S_2$. Let $(a,b)$, $\tfrac12\leq a<b$, be any interval on which the minimal quantum Rényi divergences of both dichotomies are finite. Then the dichotomies are interconvertible via positive, trace-preserving maps if and only if they have the same minimal quantum Rényi divergences on this interval.

Equation (40) requires maps in both directions carrying both members of each dichotomy. Appendix E, Eq. (105), defines the minimal (sandwiched) divergence. At $\alpha=1$ the value is Umegaki relative entropy; its finiteness requires support inclusion. The exact formal predicate uses $1\leq\alpha$ in that support clause.

## Motivation

The external named problem and its conventions are specified in [#14827](https://github.com/the-omega-institute/trureturing/issues/14827). The resolution is **Refuted**: `RenyiSufficiencyRefutation.result : ¬ claim`. The witness has $n=m=5$, $\varepsilon=1/1000$, $\sigma=\operatorname{diag}(1,2,3,4,5)/15$ and interval $(2,3)$.

## Gap

Scalar spectral profiles do not retain the relative orientation of two imaginary triangle edges. Equality of these profiles therefore does not identify the positive-map interconversion class. The literature search recorded in #14827 found no earlier settlement in its searched sources; this is a bounded search, not a proof of priority.

## Route

Let $\rho_s=(I+\varepsilon A_s)/5$. The real edges are $01,12,03,34$, and the Hermitian imaginary edges have $(A_s)_{20}=s_1i$ and $(A_s)_{40}=s_2i$. `rho false` represents $(+,+)$; `rho true` represents $(+,-)$.

`RenyiSufficiencyRefutation.weighted_charpoly_eq` proves equality of characteristic polynomials after arbitrary diagonal weighting. Functional calculus gives equality of trace powers and `checkpoint_profiles` gives equality and finiteness throughout $(2,3)$.

The unitalized round trip fixes the likelihood matrix. `PositiveMapKadison.kadison_finite_weights`, `PositiveMapJordanDomain.hermitian_jordan_domain` and `BouquetFixedPoint.bouquet_fixed_point_rigidity` force it to be the identity. `PositiveInverseProjectionFrame.orthogonal_projection_frame` and `PositiveInverseClassification.unital_positive_inverse_classification` restrict the forward map to unitary or transpose-unitary conjugation. `BouquetHolonomy.two_triangle_holonomy_obstruction` and `bouquet_not_interconvertible` exclude both possibilities for this pair.

## Falsifier

An explicit positive trace-preserving interconversion for the displayed pair would contradict `bouquet_not_interconvertible`. A mismatch between the source definition and `claim`, an unapproved axiom in the proof closure, or a failure of the kernel check would invalidate this formal settlement. Floating-point profile agreement alone does not establish the result.

## Evidence

The canonical Lean modules and their Blueprint Scribes are under `D5/S3/QuantumChannels/RenyiSufficiency/` and `Blueprint/D5/S3/QuantumChannels/RenyiSufficiency/`. The claim and result are literal `Prop` and `Not claim`. The axiom closure of every public declaration is contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

Experiment entry: [numerical profile and holonomy check](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/galke-van-luijk-wilming-2023-renyi-sufficiency). Run `python3 check.py` from that directory; exit code **0**. `check.py` SHA-256: `0baddd7b7b32a439397d5a06b4a1d5e883d8af78f2dfd2f65be751fe76bcf3bd`.

The experiment checks every sign pattern for $r=2,3$, dimensions $5,7$, $\varepsilon=0.9/(2r)$ and $\alpha\in\{0.5,0.6,0.75,0.9,1,1.5,2,3,5,10\}$. Its minimum eigenvalues are $0.09937694101250946$ and $0.08616247190575878$; maximum absolute profile differences are $1.1379786002407855\cdot10^{-15}$ and $2.248201624865942\cdot10^{-15}$. For $(+,+)$ the normalized first two holonomies have product $-1$; for $(+,-)$ it is $+1$. These are finite floating-point readings at perturbations different from the Lean witness, not uniform proofs.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The other 34 public theorems have an unfinished escape audit: [#14881](https://github.com/the-omega-institute/trureturing/issues/14881). Missing evidence includes whole-family variation, sensitivity and actual observational dependence; no `declared_validated` registration is claimed.

## Triage

### What the settlement shows

**Proved in Lean — orientation-blind profiles.** `RenyiSufficiencyRefutation.weighted_charpoly_eq` establishes the weighted characteristic-polynomial identity. In the determinant expansion, each triangle's two orientations contribute $2\operatorname{Re}(i s_j c)=0$ for real diagonal weights. No simple cycle traverses two triangles of the bouquet. The relative sign is therefore absent from the spectral profile. `checkpoint_profiles` establishes the equal finite minimal profiles required by the interval claim.

**Proved in Lean — positive round-trip rigidity.** Unitalization of putative positive trace-preserving interconversion gives positive maps fixing the likelihood matrix. Kadison equality, faithfulness of the weighted trace and the Jordan multiplicative domain give `BouquetFixedPoint.bouquet_fixed_point_rigidity`. The round trip is the identity.

**Proved in Lean — classification and holonomy obstruction.** `PositiveInverseClassification.unital_positive_inverse_classification` gives a unitary or transpose-unitary conjugation. State preservation and the distinct diagonal entries of $\sigma$ make its unitary diagonal. Diagonal conjugation preserves each triangle gain; transposition reverses every imaginary orientation together. The product of the first two triangle gains distinguishes $(+,+)$ from $(+,-)$, as proved by `BouquetHolonomy.two_triangle_holonomy_obstruction` and `bouquet_not_interconvertible`.

**Proved in prose, not formalized — the family.** For $r\geq2$, use $r$ triangles sharing one vertex, in $d=2r+1$, a faithful diagonal $\sigma$ with distinct entries, and sufficiently small positive $\varepsilon$. Diagonal dominance makes every $\rho_s$ faithful. Every simple cycle is a single triangle, so the determinant expansion above makes all diagonally weighted spectra independent of $s\in\{\pm1\}^r$. The trace-power profiles consequently coincide for all positive orders.

For the rigidity argument, choose $\varepsilon$ small enough that the likelihood eigenvalue intervals remain disjoint: its diagonal entries at $\varepsilon=0$ are distinct, and the off-diagonal row sums tend to zero. The Kadison and faithful-state argument fixes its spectral projections and then $\sigma$. The Jordan algebra generated by $\sigma$ and the likelihood is the full Hermitian matrix space: polynomial spectral projections of $\sigma$ isolate the vertices; Jordan products isolate the real edges $0a_j,a_jb_j$ and the imaginary edges $b_j0$; products along these connected paths produce all real off-diagonal directions, and an imaginary triangle supplies all imaginary directions. Complex linearity then gives the full matrix algebra. The positive inverse pair is thus an order automorphism, whose matrix-unit classification is unitary or transpose-unitary conjugation. Since $\sigma$ has distinct entries, its unitary is diagonal. The triangle signs are preserved individually or reversed simultaneously. Hence only $s$ and $-s$ can be interconverted; transposition does interconvert those two. There are exactly $2^{r-1}$ classes. This argument extends the mechanism in prose; the canonical Lean settlement is the five-dimensional witness only.

**Literature — surviving statements.** The classical sufficiency result is Theorem 13 and the commuting quantum case is Lemma 24 in arXiv v6. They are unaffected. The source has **Corollary 21**, not a classical sufficiency Theorem 21: it already states that Petz and maximal Rényi profiles are insufficient. Interconvertibility implies equality of minimal profiles by data processing under positive trace-preserving maps; the refutation concerns the converse. Corollary 23 is conditional on Conjecture 22, so that conjecture no longer supplies its no-catalysis justification. This witness does not refute the no-catalysis conclusion itself.

**Computed — finite numerical scope.** The experiment and its command, exit code, SHA-256, parameter set and readings are given in Evidence. Its $r=2,3$ numerical results do not certify an unbounded family or an arbitrary order.

**Proved consequence in prose — complete positivity.** Completely positive maps are positive, so this same pair also excludes completely positive trace-preserving interconversion. Replacing positive interconversion by completely positive interconversion does not rescue the stated sufficiency implication. This conclusion settles the complete-positivity question for this pair because complete positivity implies positivity; the general relation between the two interconversion classes remains open here. No separate CP theorem is added to the Lean modules.

**Proved by an exact specialization — the endpoint.** The existing `Dmin_eq_bouquet` proof specializes to $\alpha=1/2$ at $\varepsilon=1/1000$; `DminFinite_bouquet` supplies both finiteness clauses and `bouquet_not_interconvertible` supplies the same obstruction. This transient compiled application adds no canonical theorem. Equality at the endpoint alone therefore does not imply interconversion. The main public settlement uses the open interval $(2,3)$. The endpoint question is settled only for this displayed pair by the exact specialization; the classification of all endpoint-equal pairs remains open.

**Open — neighbouring questions.** Minimal and sandwiched denote the same divergence in this source, so sandwiched-profile sufficiency is refuted here. Petz-profile sufficiency is already ruled out by Corollary 21. Whether minimal profiles in both argument orders, or a richer joint family of divergences, suffice is not settled by the canonical Lean declarations. The general no-catalysis question and a formalized arbitrary-$r$ family remain open in this delivery.

## ASSUMED-UNVERIFIED

The preregistration's citing-work audit includes an embargoed recommendation-algorithm paper whose abstract was read but whose full text was unavailable. Its absence of a quantum-dichotomy settlement is unverified. Publication priority beyond the searched literature is unverified. The arbitrary-$r$ family is a prose argument, not a kernel-checked general theorem. The escape audit is unfinished as specified in #14881.
