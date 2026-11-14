---
bibkey: gilyensulowwiebe2019qsvt
authors: Andras Gilyen, Yuan Su, Guang Hao Low, Nathan Wiebe
year: 2019
title: "Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics"
doi: 10.1145/3313276.3316366
url: https://arxiv.org/abs/1806.01838v1
claim: "Lemma 6 gives parity-controlled interval sums of squares; Theorem 3 synthesizes exact-length QSP phase lists, yielding full signed-circle factorizations of their continuous unitary completions; Definitions 15–16 and Theorem 17 lift scalar reflection words to projected unitary encodings."
strata_touched:
  - D5/S3/ContinuousObservables/IntervalSOSCompletion
  - D5/S3/ContinuousObservables/PhaseSynthesis
  - D5/S3/ContinuousObservables/ProjectedUnitaryLifting
  - D5/S3/ContinuousObservables/PhaseSynthesisLifting
license: citation-only
triage: anchor
---

# Interval sums of squares and continuous unitary completion

## Verified locator

DOI: https://doi.org/10.1145/3313276.3316366

Primary version: https://arxiv.org/abs/1806.01838v1

Section 3.1, Theorem 3, equation (3), printed page 8 fixes the rotation matrix convention. Theorem 5 and Lemma 6 are on printed page 11; the factorization proof continues on page 12. The DOI identifies the STOC 2019 publication; the mathematical locators here refer specifically to the arXiv v1 text.

## Mathematical result

For every natural k and even real polynomial A of degree at most 2k, nonnegativity on the whole closed interval [-1,1] implies

$$A=B^2+(1-X^2)C^2,$$

where B,C are real polynomials, B has degree at most k and parity k, and C has degree at most k-1 and parity k-1. The Lean endpoint uses natural degree and natural truncated subtraction, and explicitly requires C=0 when k=0; A=0 is included. Parity means that coefficients of the opposite parity vanish, after complexification.

The retained original proof is by shosonoda, from [auto-res/lean-qsvt](https://github.com/auto-res/lean-qsvt/tree/42c4b9149d5957db497e4226bc02da92d10f7a3c). Its selected declarations are from QSVT/Polynomial/Parity.lean, QSVT/Polynomial/SqrtPart.lean, QSVT/QSP/Poly.lean, QSVT/QSP/PolyW.lean and QSVT/QSP/Complementary.lean. Copyright (c) 2026 shosonoda; Apache-2.0. The full license is retained at docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. The source assembly changes namespaces, helper visibility, imports and exposition, and adds the native field application; it preserves the selected original proof bodies. This is reuse of a published result, not a claim of a new SOS theorem.

Unlike the paper's global root product, the source proof removes one elementary factor at a time. Nonreal squared roots give a conjugate quartic; real squared roots outside (0,1) give signed quadratics. Interior real roots are at least double: a simple root would reverse sign. The cofactor remains even and nonnegative; continuity extends its sign across the finite zero set. Strict degree reduction and the product formula for weighted sums of two squares complete strong induction.

## Native application and limits

For p of parity k, natural degree at most k, and p(x)^2 at most one on [-1,1], apply the full theorem to A=1-p^2. For z=windingPhase(t), x=Re(z), y=Im(z), the field is

$$U(t)=\begin{pmatrix}p(x)+iB(x)&iyC(x)\\iyC(x)&p(x)-iB(x)\end{pmatrix}.$$

The circle identity x^2+y^2=1 turns the SOS identity into p(x)^2+B(x)^2+y^2C(x)^2=1. Polynomial continuity gives a continuous field in the existing CyclicObservable 2 algebra, indexed by ZMod 2. Direct matrix multiplication gives both U-star U=1 and U U-star=1, determinant one and Re(U(t)00)=p(x). All scalar factor degree, parity and k=0 data remain in the existential field theorem.

This signed-circle convention agrees with equation (3) on the upper semicircle, where y=sqrt(1-x^2). On the lower semicircle its off-diagonal sign differs from the square-root pullback. The completion theorem alone supplies no phase list. The phase-synthesis theorem below factors the same field; neither theorem supplies an effective factor-finding bound, query complexity, block encoding, physical implementation or full QSVT. The native matrix algebra is an application of the SOS factors. The substantial proof content remains the original root, double-root, cofactor and induction arguments. An equivalent result in the receiver's pinned Mathlib should replace the transplant when available.


## Polynomial phase synthesis

Theorem 3, equations (4)–(8), printed pages 8–9, gives the polynomial-pair phase synthesis. With coefficient conjugation P*, assume natural degrees d(P)≤k and d(Q)≤k−1, Q=0 at k=0, parities k and k−1, and the global identity PP*+(1−X²)QQ*=1. There exist an initial real phase and a real list of length exactly k whose left-fold pair is (P,Q). The forward step is (R,S)↦(e^(iφ)(XR+(X²−1)S),e^(−iφ)(XS+R)).

The original Lean producer is `QSVT/QSP/Existence.lean`, `exists_phases`, from the same pinned Apache-2.0 source. The additional consumed helpers come from QSP/PolyW.lean, QSP/Poly.lean and Polynomial/Parity.lean. Its induction is on the budget, so zero top coefficients and lower actual degree retain exact list length. Matching top coefficient norms gives a canceling phase; the inverse pair lowers the budget, preserves parity and the polynomial norm identity, and is sent back to the original pair by the last forward step. At budget zero the constant can be any complex number of modulus one.

For the same SOS factors B,C above, set P=c(p)+i c(B) and Q=c(C), with c denoting complexification. Their polynomial norm identity is precisely the SOS identity. The native phase product starts at diag(e^(iφ₀),e^(−iφ₀)) and multiplies on the right by phaseCompletion(X,0,1) and the next diagonal phase. At every signed circle point x+iy it equals the entire matrix U above. This is equality in CyclicObservable 2, with no restriction to the upper semicircle. The phase list, scalar factors, both star products, determinant and real readout all concern the same witnesses. The result reuses established synthesis and SOS proofs; the signed-circle matrix and list transport is an application, not a new synthesis theorem or a full QSVT result.

## Projected unitary lifting

Definitions 15–16 and Theorem 17, printed pages 17–19 of the fixed arXiv v1 text, treat arbitrary finite-dimensional complex Hilbert spaces, a unitary and two orthogonal projections. The alternating phase word has an input-projected block equal to the singular-value polynomial, with the output projection selected by parity. The even transformation retains the polynomial's value at zero on the complete input range, including a dimension surplus relative to the output range.

Corollary 8 converts a nonempty rotation phase list to reflection phases while preserving the scalar 00 polynomial. The full matrix relation includes a power of i and a right diagonal phase. These identities do not themselves construct real-part extraction or certify the resources of a native circuit.
