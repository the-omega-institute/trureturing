# SupportPerspectiveTransport

## Abstract

Signed support transport and ambient unitalization for the supported transformer.

**Theorem 1.1 (Normalize the actual spectral square root).**

Lean statement: `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.spectral_sqrt_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.spectral_sqrt_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable carrier n and PSD Q in M_n(C), let R=sqrt(Q), W=spectralInverseSqrt(Q), and P=spectralSupport(Q). Then R*=R, W*=W, P*=P, P P=P, P R=R, R P=R, P Q=Q, and W Q W=P. These are consumed specializations of the existing singleton square-root Kraus support and normalization results. The empty carrier and Q=0 are included.

**Theorem 1.2 (Positive maps preserve support of signed sandwiches).**

$$\forall u: \operatorname{Level}(),\ v: \operatorname{Level}(),\ n: \operatorname{Type}(u),\ [\operatorname{Fintype}(n)], [\operatorname{DecidableEq}(n)], m: \operatorname{Type}(v),\ [\operatorname{Fintype}(m)], [\operatorname{DecidableEq}(m)], Phi: \operatorname{PositiveLinearMap}(\mathbb{C}, \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{Matrix}(m, m, \mathbb{C})),\ B: \operatorname{Matrix}(n, n, \mathbb{C}),\ Z: \operatorname{Matrix}(n, n, \mathbb{C}),\ q: \operatorname{Matrix}(m, m, \mathbb{C}),\ S: \operatorname{Matrix}(m, m, \mathbb{C}),\ \operatorname{PSD}(B), \operatorname{Hermitian}(Z), q=\operatorname{spectralSupport}(\operatorname{Phi}(B)), S=\operatorname{Phi}(\operatorname{sqrt}(B)Z\operatorname{sqrt}(B)) \implies qS=S=Sq$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.positive_map_sandwich_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite positive complex-linear map Phi, PSD B, and Hermitian Z, put S=Phi(sqrt(B) Z sqrt(B)) and q=spectralSupport(Phi(B)). Then q S = S = S q. Hermitian norm bounds give -norm(Z) Phi(B) <= S <= norm(Z) Phi(B); positivity and zero Gram matrices force support. This argument does not require Z, f(Z), or f(0) to be nonnegative. The support facts are supplied by the existing spectralSupport and spectralInverseSqrt definitions and singleton-sqrt Kraus specializations of SpectralTransposeRecovery.

**Theorem 1.3 (Localize CFC through a supported sandwich).**

$$\forall u: \operatorname{Level}(),\ n: \operatorname{Type}(u),\ [\operatorname{Fintype}(n)], [\operatorname{DecidableEq}(n)], q: \operatorname{Matrix}(n, n, \mathbb{C}),\ Y: \operatorname{Matrix}(n, n, \mathbb{C}),\ R: \operatorname{Matrix}(n, n, \mathbb{C}),\ t: \mathbb{R},\ f: \mathbb{R} \to \mathbb{R},\ \operatorname{Hermitian}(q), qq=q, \operatorname{Hermitian}(Y), qY=Y, qR=R, Rq=R \implies R\operatorname{cfc}(f, Y+t(1-q))R=R\operatorname{cfc}(f, Y)R$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.cfc_supported_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Hermitian projection q, Hermitian Y with qY=Y, and R satisfying qR=R=Rq, every real t and every real function f satisfy R cfc(f,Y+t(I-q)) R = R cfc(f,Y) R. The proof uses the rectangular intertwining theorem with intertwiner q. No independent block functional-calculus premise is assumed.

**Theorem 1.4 (Apply Jensen to an explicit ambient unitalization).**

$$\forall u: \operatorname{Level}(),\ n: \operatorname{Type}(u),\ [\operatorname{Fintype}(n)], [\operatorname{DecidableEq}(n)], m: \operatorname{Type}(u),\ [\operatorname{Fintype}(m)], [\operatorname{DecidableEq}(m)], f: \mathbb{R} \to \mathbb{R},\ Phi: \operatorname{PositiveLinearMap}(\mathbb{C}, \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{Matrix}(m, m, \mathbb{C})),\ B: \operatorname{Matrix}(n, n, \mathbb{C}),\ i: n,\ X: \operatorname{Matrix}(n, n, \mathbb{C}),\ \operatorname{OperatorConvexOnAll}(u, \operatorname{Ici}(0), f), \operatorname{ContinuousOn}(f, \operatorname{Ici}(0)), \operatorname{PSD}(B), \operatorname{PSD}(X) \implies \operatorname{cfc}(f, \operatorname{ambientUnitalization}(Phi, B, i, X))\le\operatorname{ambientUnitalization}(Phi, B, i, \operatorname{cfc}(f, X))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.ambient_unitalized_jensen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For PSD B and any positive complex-linear Phi, define N(Z)=Phi(B)^{+1/2} Phi(sqrt(B) Z sqrt(B)) Phi(B)^{+1/2}. The plus exponent denotes the existing spectral inverse square root, zero on the kernel, not an algebraic inverse. The singleton Kraus normalization gives N(I)=q, with q=spectralSupport(Phi(B)). Choose an input coordinate i and set Theta(Z)=N(Z)+Z_ii (I-q). Coordinate evaluation is a positive unital complex-linear state, so Theta is positive unital, even when Phi(B)=0. The new positive-map Jensen bridge gives cfc(f,Theta(X)) <= Theta(cfc(f,X)) for PSD X, the full all-Hilbert operator-convex supplier and continuity. This is a concrete construction, not a unitality assumption on Phi.

SupportPerspectiveTransformer consumes these interfaces and supplies the exact kernel-inclusion reconstruction, mixed spectral products and final congruence cancellations. The Jensen and transport modules and the transformer have passed explicit targeted Lean builds and a joint scoped report using only standard Lean axioms. Information-audit binding is assessed separately. Identity regularization and trace data processing remain outside this source endpoint.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.ambient_unitalized_jensen`
- Truth anchor: `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.cfc_supported_localization`
- Truth anchor: `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.positive_map_sandwich_support`
- Truth anchor: `D5/S3/Quantum/Lieb/SupportPerspectiveTransport.spectral_sqrt_normalization`
- Dependency: [D5/S3/Quantum/Lieb/PositiveMapJensen](PositiveMapJensen.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](../Recovery/SpectralTransposeRecovery.md)
