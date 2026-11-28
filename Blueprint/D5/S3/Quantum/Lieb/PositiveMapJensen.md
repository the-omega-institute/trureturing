# PositiveMapJensen

## Abstract

Finite positive-map Jensen bridge with arbitrary finite carriers.

**Theorem 1.1 (Jensen for every finite positive unital complex-linear map).**

$$\forall u: \operatorname{Level}(),\ n: \operatorname{Type}(u),\ m: \operatorname{Type}(u),\ [\operatorname{Fintype}(n)], [\operatorname{DecidableEq}(n)], [\operatorname{Fintype}(m)], [\operatorname{DecidableEq}(m)], f: \mathbb{R} \to \mathbb{R},\ Phi: \operatorname{PositiveLinearMap}(\mathbb{C}, \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{Matrix}(m, m, \mathbb{C})),\ A: \operatorname{Matrix}(n, n, \mathbb{C}),\ \operatorname{OperatorConvexOnAll}(u, \operatorname{Ici}(0), f), \operatorname{ContinuousOn}(f, \operatorname{Ici}(0)), \operatorname{PositiveComplexLinear}(Phi), \operatorname{Phi}(1)=1, 0\le A\implies\ \operatorname{cfc}(f, \operatorname{Phi}(A))\le\operatorname{Phi}(\operatorname{cfc}(f, A))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/PositiveMapJensen.positive_unital_jensen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kei Tsukamoto, Kento Mori, Hayata Yamasaki (2026). *Lieb-Ando trace curvature and operator power convexity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean>.

*Commentary.*

Let n and m be arbitrary finite decidable carriers in Type u, Phi a complex-linear positive map from M_n(C) to M_m(C) with Phi(I)=I, and A PSD. Assume OperatorConvexOnAll.{u} (Ici 0) f and ContinuousOn f (Ici 0). Then cfc(f,Phi(A)) <= Phi(cfc(f,A)). The spectral projections E_i of A give positive effects Phi(E_i), whose sum is I, so finite effect Jensen applies. Apply that result first to f-f(0), then restore constants by unitality. The dilation first stacks sqrt(F_i) on the product carrier k times m, with Gram I; the rectangular isometry is then the upper-right block of an endomorphism contraction on n plus m. Intertwining identifies both CFC compressions. The intermediate supplier CondIciAll includes f(0)<=0; subtracting f(0) discharges that condition. There is no sign restriction on f(0), no complete-positivity hypothesis, and no trace assumption. An empty output carrier is trivial; an empty input with a nonempty output contradicts unitality.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/PositiveMapJensen.positive_unital_jensen`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Lieb/JensenOperatorInequalityIImpIV](JensenOperatorInequalityIImpIV.md)
- Dependency: [D5/S3/Quantum/Matrix/Spectral/IsometricCalculus](../Matrix/Spectral/IsometricCalculus.md)
