# Weyl Displacement Words over a Finite Cyclic Window

## Abstract

Weyl displacement words compose with a phase fixed by the symplectic pairing.

For an arbitrary Hermitian H on Fin d x Fin e with d,e >= 2, both partial traces are unnormalized. Write TrA = partialTraceLeft, TrB = partialTraceRight, h0 = trace(H)/(de), HA = e^(-1) TrB(H) - h0 I_d, HB = d^(-1) TrA(H), H0 = HA tensor I_e + I_d tensor HB, and V = H - H0. Hermiticity makes h0 real, so this is the same scalar offset as ReTr(H)/(de); only HA is centered. Partial traces and these operations preserve Hermiticity. The trace identities give trace(HA)=0, trace(HB)=trace(H)/d, TrA(V)=0, and TrB(V)=0.

Use E = (ZMod.finEquiv d).toEquiv, W(a,b) = displacement(d,E(a),E(b)).submatrix E E, and T(a,b) = W(a,b) tensor I_e. Here E(a).val=a.val. The shift entry is one precisely when E(i)=E(j)+1, the clock entry on i=j is exp(2 pi i/d) raised to i.val, and T(a,b)((i,k),(j,l))=W(a,b)(i,j) times the Kronecker delta for k=l. Thus W is exactly the positive-shift word X^a.val Z^b.val, and the window-register unitarity gives unitarity of every T.

The scalar Weyl twirl is existing mathematics: Matrix.sum_weyl_conj in LionSR/QICLean, QICLean/Channel/WeylTwirl.lean at revision 2d1491f41311f2f2ff9b1ec0ebd47fed9172760b, with the Apache-2.0 source attribution to Sirui Lu and TNLean contributors. Its shift convention is inverse to the window register, giving displacement(d,a,b)=Matrix.weyl(windowRoot(d),-a,b). The bijections a -> -E(a) and b -> E(b) preserve the d^2 summands. This is a source adaptation, not an additional dependency on that project's Lean 4.35.0-rc3 pin.

For every joint matrix Y, fix k,l and apply the scalar twirl to the arbitrary block Y_kl(i,j)=Y((i,k),(j,l)). Entrywise tensor multiplication then gives d^(-2) sum_(a,b) T(a,b) Y T(a,b)^adj = d^(-1) I_d tensor TrA(Y). Every joint Y is included; no simple-tensor or Hermiticity condition is needed. TrA is unnormalized, so this formula has no factor e. Equivalently, the all-joint tensor supplier Matrix.sum_kronecker_one_weyl_conj in QICLean/Channel/ComplementaryWeylTwirl.lean at the same revision transports along (i,k) -> (k,E(i)). Applying the formula to this V gives a zero average because TrA(V)=0.

Define EA(Y)=e^(-1)(TrB(Y) tensor I_e). Expanding partial traces gives EA((L tensor I_e)Y(M tensor I_e))=(L tensor I_e)EA(Y)(M tensor I_e) for arbitrary Y,L,M. Its fixed points are exactly N tensor I_e, so EA is idempotent. The literal decomposition of H gives, for every M, [H,M tensor I_e]-EA([H,M tensor I_e])=[V,M tensor I_e]. In particular R(a,b)=[H,T(a,b)]-EA([H,T(a,b)])=[V,T(a,b)]. Unitarity gives R(a,b)T(a,b)^adj=V-T(a,b)V T(a,b)^adj. Averaging these d^2 terms proves the same-H reconstruction V=d^(-2) sum_(a,b) R(a,b)T(a,b)^adj.

For every square matrix A on this same index type, CStarMatrix.ofMatrixStarAlgEquiv and StarAlgEquiv.norm_map identify the CStarMatrix norm with the Matrix.Norms.L2Operator norm; Matrix.cstar_norm_def identifies the latter with norm(Matrix.toEuclideanCLM A). ComplexOrder supplies the complex CStar instances. This applies to every residual as well as V, hence to their common finite maximum delta. With c the Euclidean induced norm of H-H0, reconstruction, the triangle inequality and unitary norm invariance give c <= delta; the commutator formula gives delta <= 2c. No coordinate proxy or norm on a different carrier is substituted.

Put hsSquare(Y)=Re(trace(Y^adj Y))/(de). Hermiticity of V, cyclicity of trace and unitarity give trace(R(a,b)^adj R(a,b))=2 trace(V^2)-2 trace(V T(a,b) V T(a,b)^adj). The zero twirl kills the summed cross term. Consequently (1/(2d^2)) sum_(a,b) hsSquare(R(a,b))=hsSquare(V), with both the original de denominator and the 1/(2d^2) averaging factor.

MatrixUnitCertificate.matrix_unit_eq_single and the displacement composition law express every matrix unit in the span of the displacement family. Transport by E proves that the W(a,b) span every d by d complex matrix. The linear residual map therefore vanishes on every M exactly when it vanishes on all W(a,b). Together with reconstruction and the norm bounds, the following conditions are equivalent: for every M, [H,M tensor I_e] is some N tensor I_e; for every M, EA fixes [H,M tensor I_e]; every R(a,b) is zero; V=0; and delta=0. These statements retain arbitrary M and the actual same H throughout. They are finite-matrix consequences of the cited results, not claims of a new Weyl twirl, a physical realization, asymptotic bounds, thermal factorization, or dynamical and recovery estimates.

**Definition 1.1 (The displacement word).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ \operatorname{displacement}\left(M, a, b\right) = \operatorname{shiftMatrix}\left(M\right)^{\operatorname{val}\left(a\right)} \cdot \operatorname{clockMatrix}\left(M\right)^{\operatorname{val}\left(b\right)}.$$

*Formalization.* `D5/S3/Quantum/Algebra/WeylDisplacement.displacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displacement word at index (a, b) is the shift raised to the canonical natural representative of a, times the clock raised to the canonical natural representative of b. Both generators, their Weyl relation, their orders, and their unitarity are already frozen in the window register, which this module imports.

The finite Weyl-Heisenberg group these words generate is classical, so no novelty is claimed for them. Appleby (2005), Journal of Mathematical Physics 46, 052107, doi 10.1063/1.1896384, defines the extended Clifford group as the normalizer of that group. Only the bibliographic identity and the published abstract were checked; the full text was not read, so the article is cited as background and not as the source of the identities proved below.

**Theorem 1.2 (Composition law).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b, c, d: \operatorname{ZMod}(M),\ \operatorname{displacement}\left(M, a, b\right) \cdot \operatorname{displacement}\left(M, c, d\right) = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(b \cdot c\right)} \cdot \operatorname{displacement}\left(M, {a + c}, {b + d}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two displacement words multiply to a third, scaled by a single window phase. The exponent of that phase is the clock index of the left factor times the shift index of the right factor, and nothing else. The proof moves a clock power across a shift power by iterating the frozen Weyl relation twice, once in each exponent.

Exponents are natural representatives of residues, so the identity needs the generators to see their exponents only modulo the window cardinality. That is supplied by the frozen order relations for the clock and the shift and by primitivity for the phase.

The pinned Mathlib source carries no Weyl-Heisenberg material: no file mentions the Weyl-Heisenberg group, the generalized Pauli group, or clock and shift matrices, and no file is named after Pauli or Heisenberg. The displacement words are nevertheless classical, so the cited article records that no novelty is claimed here.

**Theorem 1.3 (Squaring identity).**

$$\forall M: \mathbb{N},\ [\operatorname{NeZero}(M)],\ \forall a, b: \operatorname{ZMod}(M),\ \operatorname{displacement}\left(M, a, b\right)^{2} = \operatorname{windowRoot}\left(M\right)^{\operatorname{val}\left(a \cdot b\right)} \cdot \operatorname{displacement}\left(M, {a + a}, {b + b}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Setting the two indices equal in the composition law gives the square of a displacement word as the doubled word carrying the phase whose exponent is the product of the two indices.

**Theorem 1.4 (The composition phase is not vacuous).**

$$\operatorname{displacement}\left(2, 0, 1\right) \cdot \operatorname{displacement}\left(2, 1, 0\right) \neq \operatorname{displacement}\left(2, 1, 0\right) \cdot \operatorname{displacement}\left(2, 0, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_two_not_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The composition law would read the same way if every phase were one, so a witness is recorded that the phase does real work. On the two-address window the words at (0, 1) and (1, 0) do not commute. Assuming they did forces the window phase to be its own square, hence one, contradicting primitivity.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_mul`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_sq`
- Truth anchor: `D5/S3/Quantum/Algebra/WeylDisplacement.displacement_two_not_commute`
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
