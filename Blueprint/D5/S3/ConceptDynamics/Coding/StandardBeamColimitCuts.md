# Integer cuts in the original stationary row colimit

## Abstract

Integer cuts in the original stationary row colimit.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Integer cuts in the original natural-stage colimit).**

$$\forall M \in Type, addM \in \operatorname{AddCommGroup}\left(M\right), moduleM \in \operatorname{IntModule}\left(M\right), T \in \operatorname{IntEnd}\left(M\right),\; \forall n \in Int, z \in M,\; \operatorname{intStage}\left(T, n\right)\left(z\right) = \operatorname{stage}\left(T, \operatorname{toNat}\left(n\right)\right)\left(\operatorname{power}\left(T, \operatorname{toNat}\left(\operatorname{negate}\left(n\right)\right)\right)\left(z\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts.intStage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M is any AddCommGroup with Module Int M, T : Module.End Int M. stage T N is the original Module.DirectLimit.of at N:Nat with stationaryTransition T i j hij = T^(j-i). intStage T n is stage T n.toNat composed with T^((-n).toNat). For n>=0 it is the original stage; for n<0 it advances to stage zero using the nonnegative power -n. No inverse matrix, transition injectivity or torsion-free premise is used.

**Theorem 1.2 (Every nonnegative upper stage gives the same class).**

$$\forall M \in Type, addM \in \operatorname{AddCommGroup}\left(M\right), moduleM \in \operatorname{IntModule}\left(M\right), T \in \operatorname{IntEnd}\left(M\right),\; \forall n \in Int, N \in Nat, hn \in n \le \operatorname{intCast}\left(N\right), z \in M,\; \operatorname{intStage}\left(T, n\right)\left(z\right) = \operatorname{stage}\left(T, N\right)\left(\operatorname{power}\left(T, \operatorname{toNat}\left(\operatorname{integerDifference}\left(N, n\right)\right)\right)\left(z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts.intStage_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

intCast is the natural-to-integer coercion, integerDifference(N,n) is (N:Int)-n, and the exponent is its toNat. This is the exact n<=(N:Int) hypothesis. The existing direct-limit stage relation proves the equality. intStage_refine then states intStage T n z = intStage T (n+r) (T^r z) for every r:Nat. All powers advance rather than invert T.

**Theorem 1.3 (Moving the cut down by one induces the stationary transition).**

$$\forall M \in Type, addM \in \operatorname{AddCommGroup}\left(M\right), moduleM \in \operatorname{IntModule}\left(M\right), T \in \operatorname{IntEnd}\left(M\right),\; \forall n \in Int, z \in M,\; \operatorname{intStage}\left(T, \operatorname{previousCut}\left(n\right)\right)\left(z\right) = \operatorname{Theta}\left(T\right)\left(\operatorname{intStage}\left(T, n\right)\left(z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts.intStage_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

previousCut(n)=n-1. Theta T is induced T T (Commute.refl T) on StationaryModule T, with Theta(stage N z)=stage N (T z). Refining from n-1 to n proves this direction, including n=0 and cut -1. It is the direction required by the actual left shift x_t -> x_(t+1).

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts.intStage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts.intStage_at`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts.intStage_shift`
- Dependency: [D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy](InertGroupBlockConjugacy.md)
