# Original two-table idempotent support

## Abstract

The unchanged original directed positive two-table gives the exact norm-product cone bounds and closure of its total response in every actual original idempotent corner.

Let X be an arbitrary complete real normed vector space with the six-law JB data (S,u). Let E be any original real normed label space, J its real bilinear Jordan product, i:E->X a real linear isometry satisfying i(J(a,b))=S(i(a),i(b)), C its exact ambient square cone, and P the unchanged type of original evaluation labels. Thus e belongs to C exactly when i(e) is an actual square in X, and exactly when every original real linear evaluation alpha reads e nonnegatively. Let D:E x E->E be any total map. The table has diagonal alpha(J(a,a)), alpha(J(b,b)), upper entry alpha(J(a,b))-i alpha(D(a,b)), and lower entry alpha(J(b,a))-i alpha(D(b,a)); require this actual directed complex table positive semidefinite for every original alpha,a,b.

**Theorem 1.1 (Quantitative support in the original corner).**

$$\forall X \in CompleteRealNormedSpaces,\; \forall S \in RealBilinearMaps\left(X\right),\; \forall u \in X,\; \forall E \in RealNormedSpaces,\; \forall P \in Types,\; \forall J \in RealBilinearMaps\left(E\right),\; \forall D \in TotalBinaryMaps\left(E\right),\; \forall C \in Sets\left(E\right),\; \forall i \in RealLinearIsometries\left(E, X\right),\; \forall evaluation \in EvaluationFamilies\left(P, E\right),\; OriginalTwoTableHypotheses\left(X, S, u, E, J, D, C, i, P, evaluation\right) \Rightarrow \left(\forall p \in E,\; \forall a \in E,\; \forall b \in E,\; \left(J\left(p, p\right) = p \land \left(S\left(i\left(p\right), i\left(a\right)\right) = i\left(a\right) \land S\left(i\left(p\right), i\left(b\right)\right) = i\left(b\right)\right)\right) \Rightarrow \left(mem\left(scale\left(multiply\left(norm\left(a\right), norm\left(b\right)\right), p\right) + D\left(a, b\right), C\right) \land \left(mem\left(scale\left(multiply\left(norm\left(a\right), norm\left(b\right)\right), p\right) - D\left(a, b\right), C\right) \land S\left(i\left(p\right), i\left(D\left(a, b\right)\right)\right) = i\left(D\left(a, b\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBIdempotentSupport.original_p2_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual original p with J(p,p)=p, write E(p)={a in E:S(i(p),i(a))=i(a)}. For all a,b in E(p), set c=norm(a)norm(b). The conclusions are cp+D(a,b) in C, cp-D(a,b) in C, and D(a,b) in E(p). The norm is the unchanged original norm, and the corner is literally the inverse image of the ambient Peirce two-space. Density, a unit in E and separation may additionally be supplied as in the original setting; the proof establishes this conclusion without needing those extra hypotheses. In particular it applies to the original dense unital faithful Jordan subalgebra without changing its carrier.

The ambient square bound gives 0<=alpha(J(a,a))<=norm(a)^2 alpha(p), and the analogous bound for b. The existing original positive-table transfer theorem gives alpha(D(a,b))^2<=alpha(J(a,a))alpha(J(b,b))-alpha(J(a,b))^2. Since alpha(p)>=0, scalar comparison gives abs(alpha(D(a,b)))<=c alpha(p). Exact detection by the same original evaluations puts cp+D(a,b) and cp-D(a,b) in C. The ambient support theorem then gives S(i(p),i(D(a,b)))=i(D(a,b)). Every square root used here belongs to X; D is called only on the original a,b in E.

In the original unital setting, let e in E be the original unit, with i(e)=u. All original evaluation labels are retained. Their masses alpha(e) may be zero, unequal or subnormalized; no mass is divided out and no additional preparation is introduced. There is no additivity, homogeneity, continuity, NN or Jacobi hypothesis on D. The conclusion includes zero X, p=0, p=e, zero masses and zero inputs. This result supplies the ambient support step for a separately established quotient bound, but proves neither an actual quotient response interface nor the positivity of a proposed quotient-corner readout, nor general response descent or physical reconstruction.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PBIdempotentSupport.original_p2_support`
- Dependency: [D5/S3/Quantum/Algebra/PBOriginalReadoutRealization](PBOriginalReadoutRealization.md)
- Dependency: [D5/S3/Topology/JBAmbientSupport](../../Topology/JBAmbientSupport.md)
