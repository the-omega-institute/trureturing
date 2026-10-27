# Universal fixed-lag certificate search

## Abstract

A finite algorithm decides original numbered certificates at each fixed positive lag.

The orders n and k and lag m are arbitrary natural numbers. A and B are natural count matrices of orders n and k. The input requires positive orders, positive lag, and a nonzero entry in every row and every column of both matrices. The selector aligned chooses either the two original aligned laws or the two original compatibility sweep laws. All equalities retain the numbered edges and the whole output paths.

**Definition 1.1 (The four actual maps).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \operatorname{Maps}\left(A, B, R, S, m\right) = \operatorname{FourEquivalenceFamilies}\left(A, B, R, S, m\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Maps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FourEquivalenceFamilies is the product of the endpoint-indexed families EdgePair(A,R,i,z) ≃ EdgePair(R,B,i,z), EdgePair(B,S,t,w) ≃ EdgePair(S,A,t,w), EdgePair(R,S,i,w) ≃ FinitePath(A,m,i,w), and EdgePair(S,R,t,v) ≃ FinitePath(B,m,t,v). Each equivalence stores its forward and inverse tables and both inverse laws.

**Definition 1.2 (Both sweep laws).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall d \in \operatorname{Maps}\left(A, B, R, S, m\right),\; \operatorname{Compatible}\left(d\right) = \left(\operatorname{ForwardSweepLaw}\left(d\right) \land \operatorname{BackwardSweepLaw}\left(d\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every length-m A path alpha from i to j and every numbered R edge r from j to z, write psiA(i,j) inverse(alpha)=(u,r0,s0). ForwardSweepLaw says sweep(phiR,alpha,r)=(u,r0,psiB(u,z)(j,s0,r)). BackwardSweepLaw is the literal swapped equation: for a B path beta from t to z and S edge s from z to w, write psiB(t,z) inverse(beta)=(u,s0,r0); sweep(phiS,beta,s)=(u,s0,psiA(u,w)(z,r0,s)). Both quantify over every original path and numbered edge.

**Definition 1.3 (Both alignment laws).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall d \in \operatorname{Maps}\left(A, B, R, S, m\right),\; \operatorname{Aligned}\left(d\right) = \left(\operatorname{AlignedA}\left(\operatorname{phiR}\left(d\right), \operatorname{phiS}\left(d\right), \operatorname{psiA}\left(d\right)\right) \land \operatorname{AlignedB}\left(\operatorname{phiR}\left(d\right), \operatorname{phiS}\left(d\right), \operatorname{psiB}\left(d\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Aligned` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AlignedA and AlignedB are the original predicates from OriginalAlignedBalanced, applied to these same four equivalences.

**Definition 1.4 (Selecting the law pair).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \forall d \in \operatorname{Maps}\left(A, B, R, S, m\right),\; \forall aligned \in \mathit{Bool},\; \operatorname{Valid}\left(\mathit{aligned}, d\right) = \operatorname{ifThenElse}\left(\mathit{aligned}, \operatorname{Aligned}\left(d\right), \operatorname{Compatible}\left(d\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The true selector requires Aligned and the false selector requires Compatible. No maps are replaced when selecting the laws.

**Definition 1.5 (Essential count matrices).**

$$\forall r \in \mathit{Nat}, X \in \operatorname{CountMat}\left(r, r\right),\; \operatorname{Essential}\left(X\right) = \left(\left(\forall i \in \operatorname{Fin}\left(r\right),\; \exists j \in \operatorname{Fin}\left(r\right),\; \operatorname{entry}\left(X, i, j\right) \ne 0\right) \land \left(\forall j \in \operatorname{Fin}\left(r\right),\; \exists i \in \operatorname{Fin}\left(r\right),\; \operatorname{entry}\left(X, i, j\right) \ne 0\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Essential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every row and every column has a nonzero entry. The two clauses are separate, including at order zero.

**Definition 1.6 (The original input boundary).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \operatorname{Input}\left(A, B, m\right) = \left(1 \le n \land \left(1 \le k \land \left(1 \le m \land \left(\operatorname{Essential}\left(A\right) \land \operatorname{Essential}\left(B\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Input consists exactly of 0<n, 0<k, 0<m and essentiality of A and B. Lag zero, an empty order, and a zero row or column are rejected.

**Definition 1.7 (Unrestricted original existence).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall aligned \in \mathit{Bool},\; \operatorname{OriginalExists}\left(A, B, m, \mathit{aligned}\right) = \left(\operatorname{Input}\left(A, B, m\right) \land \left(\exists R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right), d \in \operatorname{Maps}\left(A, B, R, S, m\right),\; \operatorname{Valid}\left(\mathit{aligned}, d\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.OriginalExists` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R and S range over all natural matrices of the displayed shapes. There is no entry bound in this existence predicate. The witness includes all four equivalences and both selected laws.

**Definition 1.8 (The four matrix products).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right),\; \operatorname{MatrixLaws}\left(A, B, R, S, m\right) = \left(A \cdot R = R \cdot B \land \left(B \cdot S = S \cdot A \land \left(R \cdot S = \operatorname{power}\left(A, m\right) \land S \cdot R = \operatorname{power}\left(B, m\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.MatrixLaws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four products follow from cardinalities of the four equivalences. The RS and SR equations use the corresponding A and B path counts separately.

**Definition 1.9 (A finite matrix carrier).**

$$\forall r \in \mathit{Nat}, s \in \mathit{Nat}, bound \in \mathit{Nat},\; \operatorname{BoundedMatrix}\left(r, s, \mathit{bound}\right) = \operatorname{FiniteMatrixFunctions}\left(r, s, \operatorname{succ}\left(\mathit{bound}\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.BoundedMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

BoundedMatrix(r,s,bound) is Fin r → Fin s → Fin(bound+1), including entries zero through bound.

**Definition 1.10 (Recovering natural entries).**

$$\forall r \in \mathit{Nat}, s \in \mathit{Nat}, bound \in \mathit{Nat}, X \in \operatorname{BoundedMatrix}\left(r, s, \mathit{bound}\right), i \in \operatorname{Fin}\left(r\right), j \in \operatorname{Fin}\left(s\right),\; \operatorname{entry}\left(\operatorname{entries}\left(X\right), i, j\right) = \operatorname{val}\left(\operatorname{entry}\left(X, i, j\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.entries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The decoding takes each Fin value's natural-number value without changing a row, column or edge number.

**Definition 1.11 (All bounded matrices and all maps).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \operatorname{Candidate}\left(A, B, m\right) = \operatorname{BoundedMatrixAndMapTuples}\left(A, B, m\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Candidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dependent sum first enumerates R in BoundedMatrix(n,k,powerMaximum(A,m)), then S in BoundedMatrix(k,n,powerMaximum(B,m)), then all Maps(A,B,entries(R),entries(S),m). Path types are encoded recursively. Equivalences are encoded by their actual forward and inverse finite tables with inverse-law tests. Thus the enumeration includes whole maps rather than cardinality surrogates.

**Definition 1.12 (Checking a candidate).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall aligned \in \mathit{Bool},\; \forall c \in \operatorname{Candidate}\left(A, B, m\right),\; \operatorname{candidateCheck}\left(A, B, m, \mathit{aligned}, c\right) = \operatorname{decide}\left(\operatorname{Input}\left(A, B, m\right) \land \left(\operatorname{CandidateMatrixLaws}\left(A, B, m, c\right) \land \operatorname{Valid}\left(\mathit{aligned}, \operatorname{maps}\left(c\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.candidateCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CandidateMatrixLaws abbreviates MatrixLaws(A,B,entries(c.R),entries(c.S),m). The final conjunction tests both laws of the selected kind on c's four actual maps.

**Definition 1.13 (Executable finite search).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall aligned \in \mathit{Bool},\; \operatorname{search}\left(A, B, m, \mathit{aligned}\right) = \operatorname{GuardedFirstAcceptedCandidate}\left(A, B, m, \mathit{aligned}\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.search` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If Input is false, search returns none. Otherwise it runs List.find? with candidateCheck on Encodable.sortedUniv(Candidate(A,B,m)). A successful result returns the actual bounded matrices and all four equivalences. Both Fintype and Encodable are constructed, so this is executable exhaustive search.

**Definition 1.14 (The decision Boolean).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall aligned \in \mathit{Bool},\; \operatorname{existsBool}\left(A, B, m, \mathit{aligned}\right) = \operatorname{isSome}\left(\operatorname{search}\left(A, B, m, \mathit{aligned}\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.existsBool` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

existsBool observes whether the search returned an actual candidate.

**Theorem 1.15 (Soundness of the returned maps).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall aligned \in \mathit{Bool},\; \forall c \in \operatorname{Candidate}\left(A, B, m\right),\; \operatorname{search}\left(A, B, m, \mathit{aligned}\right) = \operatorname{some}\left(c\right) \Rightarrow \left(\operatorname{Input}\left(A, B, m\right) \land \operatorname{Valid}\left(\mathit{aligned}, \operatorname{maps}\left(c\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.search_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

List.find? supplies a true candidateCheck. Eliminating its decidable conjunction gives the original input and both selected laws for precisely the returned maps.

**Theorem 1.16 (Universal correctness).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), m \in \mathit{Nat},\; \forall aligned \in \mathit{Bool},\; \operatorname{existsBool}\left(A, B, m, \mathit{aligned}\right) = \mathit{true} \Leftrightarrow \operatorname{OriginalExists}\left(A, B, m, \mathit{aligned}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.search_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Soundness recovers the unrestricted witness from the returned candidate. For completeness, start with arbitrary natural R and S and the original four equivalences. Essentiality and the inverse path bijections bound every R entry by powerMaximum(A,m) and every S entry by powerMaximum(B,m). Encode each entry in the corresponding Fin type and retain the same four equivalences. This constructs an actual Candidate whose check is true; membership in sortedUniv makes the search succeed. The construction occurs directly in the universal theorem and adds no bounded-input hypothesis.

The executable examples use command-local CountMat(1,1) inputs with every entry equal to one, evaluate both selectors, and reject lag zero and a nonessential input. The utility instance names the already existing private unitCountMatrix in CompatibleResponseForgettingBound, which is the same closed one-matrix input. A separate example enumerates all four map tables for the one-vertex two-loop input. Examples provide computational observations, not additional mathematical results.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Aligned`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.BoundedMatrix`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Candidate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Compatible`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Essential`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Input`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Maps`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.MatrixLaws`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.OriginalExists`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.Valid`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.candidateCheck`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.entries`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.existsBool`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.search`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.search_correct`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/FixedLagCertificateSearch.search_sound`
- Dependency: [D5/S3/ConceptDynamics/Coding/OriginalResponseControls](../OriginalResponseControls.md)
