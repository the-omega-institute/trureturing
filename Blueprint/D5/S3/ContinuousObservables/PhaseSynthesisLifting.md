# Native phases on a projected unitary

## Abstract

The same signed-circle completion and native phases determine the compressed operator of a raw projected unitary.

Fix an arbitrary finite-dimensional complex Hilbert space H, a raw endomorphism U with U*U=UU*=1, and arbitrary self-adjoint idempotents Pi and Pt. Set E=ofRaw(U,Pi,Pt), A=Pt U Pi and G=A*A. The definitions of F, V, D, R and S are those of ProjectedUnitaryLifting: V is the alternating operator word, while S is the ordered scalar reflection product.

**Theorem 1.1 (One phase tuple supplies both the circle field and the projected polynomial).**

$$\forall (H: \operatorname{FiniteComplexHilbertSpace}()), \forall (U: \operatorname{End}(H)), \forall (Pi: \operatorname{End}(H)), \forall (Pt: \operatorname{End}(H)), \forall (k: \mathbb{N}), \forall (p: \mathbb{R}[X]), ((\operatorname{rawUnitaryProjections}(U, Pi, Pt)) \land (0 < k) \land (\operatorname{d}(p) \leq k) \land (\operatorname{par}(\operatorname{c}(p), k)) \land (\forall (x: I), \operatorname{abs}(\operatorname{p}(x)) \leq 1)) \Rightarrow \exists (B: \mathbb{R}[X]), \exists (C: \mathbb{R}[X]), \exists (Ufield: \operatorname{CircleMatrixField}()), \exists (phi0: \mathbb{R}), \exists (Phi: \operatorname{List}(\mathbb{R})), (((1-(p)^{2} = (B)^{2}+(1-(X)^{2})(C)^{2}) \land (\operatorname{d}(B) \leq k) \land (\operatorname{d}(C) \leq k-1) \land ((k = 0) \Rightarrow C = 0) \land (\operatorname{par}(\operatorname{c}(B), k)) \land (\operatorname{par}(\operatorname{c}(C), k-1))) \land (Ufield = \operatorname{F}(p, B, C)) \land (\operatorname{star}(Ufield)Ufield = 1) \land (Ufield\operatorname{star}(Ufield) = 1) \land (\forall (t: T), \operatorname{det}(\operatorname{Ufield}(t)) = 1) \land (\forall (t: T), \operatorname{Re}(\operatorname{entry}(\operatorname{Ufield}(t), 0, 0)) = \operatorname{p}(\operatorname{Re}(\operatorname{z}(t)))) \land (\operatorname{length}(Phi) = k) \land (\operatorname{nonempty}(Phi)) \land (\operatorname{q}(phi0, Phi) = \operatorname{pair}(P, \operatorname{c}(C))) \land (\operatorname{phaseProduct}(phi0, Phi) = Ufield)) \land ((\operatorname{length}(Psi) = k) \land (\forall (x: J), \operatorname{entry}(\operatorname{S}(Psi, x), 0, 0) = \operatorname{eval}(P, x)) \land ((\operatorname{Even}(k)) \Rightarrow Pi\operatorname{V}(E, Psi)Pi = Pi\operatorname{eval}(\operatorname{evenRoot}(P), G)Pi) \land ((\operatorname{Odd}(k)) \Rightarrow Pt\operatorname{V}(E, Psi)Pi = A\operatorname{eval}(\operatorname{oddRoot}(P), G)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/PhaseSynthesisLifting.native_phase_lifting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, d(q)=natDegree(q), c is coefficientwise complexification, par(q,k) means vanishing coefficients of opposite parity, I=[-1,1], J=[0,1] and T=AddCircle(1). The hypotheses are k>0, d(p)<=k, par(c(p),k) and |p(x)|<=1 for every x in I. Ufield is a continuous 2 by 2 complex matrix field on T. Write z(t)=windingPhase(t), x=Re(z) and y=Im(z), retaining the sign of y. The completion F(p,B,C)(t) has entries p(x)+iB(x), iyC(x), iyC(x), p(x)-iB(x). The displayed star, determinant and real-readout constraints all concern this same field.

The pair q(phi0,Phi)=qspPolyW(phi0,Phi) is the native left fold of stepW, starting at (exp(i phi0),0). Its matrix word Wword is D(phi0) followed by W(x)D(phi) in list order, where W(x)=[[x,i sqrt(1-x squared)],[i sqrt(1-x squared),x]]. The witnesses B,C,Ufield,phi0,Phi are obtained together from PhaseSynthesis.exists_phase_factorization. They are retained without a second completion or a new phase choice. The bound in absolute value supplies that theorem's squared bound.

The nonempty list Phi has length k. Define Psi=cor8Phases(phi0,Phi): its first phase is phi0+last(Phi)+(k-1)pi/2, and its remaining phases are dropLast(Phi), each reduced by pi/2. Its length is exactly k. The source conversion proves Wword(phi0,Phi,x)=i to the k times S(shift(phi0,Phi),x)D(last(Phi)-pi/4), with shift=(phi0-pi/4)::map(phi-pi/2,dropLast(Phi)). Absorbing the two diagonal contributions and i to the k into the first phase identifies exactly the 00 entry with S(Psi,x). The full matrix retains its stated diagonal factor; equality of 00 entries is not an equality of the two complete words.

Put P=c(p)+i c(B). Native multiplication gives the first row of Wword as P(x), iQ(x)sqrt(1-x squared), with Q=c(C), by induction on the native pair recursion. Hence S(Psi,x) has 00 entry P(x) on J. Define evenRoot(P)=contract(2,P) and oddRoot(P)=contract(2,divX(P)). Coefficient parity gives P(x)=evenRoot(P)(x squared) for even k, and P(x)=x oddRoot(P)(x squared) for odd k. The exact scalar-premise lifting theorem therefore applies to E with these roots. Its even output is Pi V Pi and its odd output is Pt V Pi, both on the original raw U and projections.

All zero-dimensional spaces, zero-rank projections and singular values zero and one remain included. An even zero singular component is P(0)Pi. The restriction k>0 serves only the nonempty conversion; the general lifting theorem includes the empty list. This result implements the complex polynomial P=p+iB in the compressed block. A circuit realizing the unscaled real polynomial p with one ancilla, exact calls to the original U or U*, and a separate zero-call constant phase is a further construction. Neither real-part extraction, exact resource accounting, physical adjoint by phase negation nor deterministic output semantics follows from these block identities.

Conversion proof bodies are reused from Copyright (c) 2026 shosonoda, auto-res/lean-qsvt@42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/QSP/Conversion.lean, Wrot_eq_Rref, phaseZ_mul_Wrot_mul_phaseZ, seqW_cons, seqW_append_singleton, seqW_eq_seqR and seqW_apply_zero_zero_eq. The scalar multiplication uses the existing native PhaseSynthesis.mul_signal_phase. The literature is Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Theorem 3, Corollary 8, Definitions 15–16 and Theorem 17. Apache-2.0 is preserved in docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. The combination is a receiving application of established results and makes no mathematical novelty claim.

## References

- Truth anchor: `D5/S3/ContinuousObservables/PhaseSynthesisLifting.native_phase_lifting`
- Dependency: [D5/S3/ContinuousObservables/PhaseSynthesis](PhaseSynthesis.md)
- Dependency: [D5/S3/ContinuousObservables/ProjectedUnitaryLifting](ProjectedUnitaryLifting.md)
