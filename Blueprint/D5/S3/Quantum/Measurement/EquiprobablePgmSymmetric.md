# Complete symmetric qubit discrimination and PGM failure

## Abstract

Complete symmetric qubit discrimination and PGM failure

**Theorem 1.1 (Shared dual score).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.dual_score`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.dual_score` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For arbitrary matrices rho,E,Gamma, POVM completeness alone gives success=Re tr Gamma-sum_i Re tr[(Gamma-rho_i/N)E_i]. It is a shared algebra helper consumed by the dual bound and complementary-product proofs.

**Theorem 1.2 (Shared dual bound).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.dual_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.dual_bound` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every actual finitePOVM and every dual matrix whose slacks Gamma-rho_i/N are positive semidefinite, actual success<=Re tr Gamma. This shared helper is consumed by the symmetric optimizer classification and the commuting interval proof.

**Theorem 1.3 (Shared complementary products).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.complementary_products`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.complementary_products` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For any actual finitePOVM attaining a feasible dual trace, every actual dual slack has zero product with its corresponding effect. The proof reuses the existing PSD zero-trace-product theorem and is consumed by both the symmetric uniqueness and commuting every-optimum proofs.

**Definition 1.4 (The actual symmetric ensemble).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.rho`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.rho` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For real a,b,c the three matrices, in plus, minus, third order, are rho_+/-=[[a,+/-b],[+/-b,1-a]] and rho_3=diag(c,1-c). The existing success and pgmScore definitions retain equal original priors 1/3.

**Definition 1.5 (The actual two-projector measurement).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pairPovm`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pairPovm` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

The effects are Q_+=(I+X)/2, Q_-=(I-X)/2, and zero, where X=[[0,1],[1,0]]. These are positive semidefinite rank-one projectors summing to the identity; active means nonzero effect.

**Definition 1.6 (The two-active dual certificate).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pairGamma`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pairGamma` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

Gamma=diag(a+b,1-a+b)/3. Its pair slacks are (b/3)(I-X) and (b/3)(I+X), and its third slack is diag(b-(c-a),b+(c-a))/3. Positivity therefore includes both signs of c-a and the equality boundaries.

**Theorem 1.7 (Strictly positive actual density matrices).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.states_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.states_posDef` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every real a,b,c with a>0, 0<c<1, and a(1-a)-b^2>0, all three actual matrices are positive definite and have trace one. In particular the scientific strict domain 0<a,c<1 and 0<b<sqrt(a(1-a)) is included; the determinant form does not impose a spectral floor.

**Theorem 1.8 (Uniqueness throughout the closed two-active region).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pair_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pair_classification` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every real a,b,c with b>0 and |c-a|<=b, pairPovm is an actual finitePOVM, scores (1+2b)/3, and every actual finitePOVM E is optimal among all actual finitePOVMs if and only if E=pairPovm. The optimization statement is stronger than the density-domain restriction: it needs only b>0 and the displayed absolute-value bound, while states_posDef supplies the physical strict-density domain. The certificate inequality applies to every complex Hermitian-positive effect family, not only real or diagonal competitors. Complementary slackness uses the existing zero_trace_mul_eq_zero supplier. The first two effects lie on the two orthogonal X rays. Completeness equates the third effect's diagonal entries; the sum of its two slack equations forces both to zero because b>0. Positivity then forces that whole effect to zero, including its off-diagonals. Completeness fixes both remaining weights to one. Thus delta=+b and delta=-b retain the same unique pair optimum; a singular third dual slack does not produce an extra optimal effect.

**Definition 1.9 (The actual upper three-active effects).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upperPovm`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upperPovm` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For t=b/(c-a), the effects are E_+=outer(t,1)/2, E_-=outer(-t,1)/2 and E_3=diag(1-t^2,0). Here outer(v)=v v†. In the strict upper region 0<b<c-a, one has 0<t<1. The effects are positive, sum to I and are all nonzero. This is the positive-sign form of the verification note's Bloch formula; the opposite sign is handled by actual basis permutation in the classification owner.

**Definition 1.10 (The upper three-active dual certificate).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upperGamma`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upperGamma` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

Gamma=diag(c,1-a+b t)/3. Under (c-a)t=b its first slacks are ((c-a)/3) outer(1,-t) and ((c-a)/3) outer(1,t), and its third slack is diag(0,(c-a+b t)/3). These are actual positive matrices and their complementary products with the displayed effects vanish.

**Theorem 1.11 (Unique optimum in the strict upper three-active region).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upper_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upper_classification` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every real a,b,c with 0<b<c-a, set t=b/(c-a). The displayed upperPovm is a finitePOVM with score (1+c-a+b t)/3, and an arbitrary actual complex finitePOVM E is optimal if and only if it equals upperPovm. On the strict density domain certified by states_posDef, this is P_opt=(1+R)/3 with R=((c-a)^2+b^2)/(c-a). Complementary slackness puts the first effects on the two tilted rays and the third on the first basis ray; completeness fixes both first weights to 1/2 and the remaining weight to 1-t^2. The endpoint |c-a|=b belongs to pair_classification, which proves uniqueness there separately.

**Theorem 1.12 (Two-coordinate spectral inverse square root).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.inverse_sqrt_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.inverse_sqrt_two` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

The inverse square root of diag(u,v), for arbitrary nonnegative u,v including zero, is diag(sqrt(u)^(-1),sqrt(v)^(-1)). This shared CFC evaluation helper is consumed by the actual score and effect calculations; it assumes no invertibility.

**Theorem 1.13 (Both actual symmetric scores).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.symmetric_scores`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.symmetric_scores` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every real a,b,c with 0<a,c<1, the actual original-prior restricted and full CFC scores of rho(a,b,c) satisfy P_{0,1}-1/3=2b^2/(3sqrt(a(1-a))) and P_all-1/3=4b^2/(3sqrt(D))+2(c-a)^2/(3D), D=(2a+c)(3-2a-c). The evaluation does not need a pair determinant hypothesis. When b^2<=a(1-a), the pair is physical, including the singular equality case; strict determinant positivity gives the full strict-PD setting. The proof evaluates the existing diagonal CFC, including its support inverse, and multiplies the actual matrices inside the existing score definition. Hyunho Cha is credited for these symmetric calculations.

**Definition 1.14 (Exchange the two basis coordinates).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.basisFlip`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.basisFlip` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

The actual linear matrix reindexing M(i,j) -> M(rev i,rev j) exchanges the two orthonormal qubit basis vectors. The proof checks positivity, POVM completeness, actual score invariance and the involution; no scalar symmetry bridge is assumed.

**Definition 1.15 (The negative-sign three-active measurement).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.lowerPovm`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.lowerPovm` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For t=b/(a-c), the effects are the basis flips of upperPovm(t). Equivalently E_+=[[1,t],[t,t^2]]/2, E_-=[[1,-t],[-t,t^2]]/2 and E_3=diag(0,1-t^2). In the strict lower region b<a-c, all effects are nonzero.

**Theorem 1.16 (Unique optimum in the negative-sign region).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.lower_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.lower_classification` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every a,b,c with 0<b<a-c, the actual lowerPovm(b/(a-c)) is a finitePOVM with success (1+a-c+b^2/(a-c))/3. Every actual complex finitePOVM E is optimal if and only if it equals that measurement. This is derived by an actual basis permutation from the upper classification, transporting all competitors as well as the candidate.

**Definition 1.17 (The full piecewise actual optimizer).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.optimalPovm`

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.optimalPovm` (`✓ std3`).

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

Use pairPovm when |c-a|<=b, upperPovm(b/(c-a)) when c-a>b, and lowerPovm(b/(a-c)) otherwise. Both equality boundaries are assigned to the unique pair optimum. On the strict density domain 0<a,c<1, 0<b<sqrt(a(1-a)), these are exactly the note’s two-active and three-active effects, in the original label order.

**Theorem 1.18 (Every optimum and its exact active set).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.complete_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.complete_classification` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every b>0 the actual optimalPovm is a finitePOVM, and an arbitrary actual finitePOVM E is optimal among all complex finitePOVMs if and only if E=optimalPovm. Its active set, defined by nonzero effects, is exactly {0,1} when |c-a|<=b and is all three labels otherwise. The physical strict-density theorem is supplied separately by states_posDef; the optimization calculation itself uses no extra positivity assumption on a or c. In the three-active regions the exact success from the two orientation theorems is (1+R)/3 with R=((c-a)^2+b^2)/|c-a|. Both signs and the two equality boundaries are included.

**Theorem 1.19 (The strict score criterion).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pair_failure_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pair_failure_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every 0<a,c<1, the actual pair/full score inequality 2(P_all-1/3)<P_{0,1}-1/3 holds if and only if D>16q and b^2>2(c-a)^2sqrt(q)/(sqrt(D)(sqrt(D)-4sqrt(q))), with q=a(1-a), D=(2a+c)(3-2a-c). Either equality is nonfailure. The actual CFC scores are bound through symmetric_scores; no evaluation bridge is assumed. This scalar-equivalent test concerns the pair label set; the full optimizer theorem additionally needs that set to be active.

**Theorem 1.20 (The actual active-set failure iff).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.active_failure_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.active_failure_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma, Wenlin Zhang (2026). *No universal factor compares centered PGM scores; Verification of the unbounded centered PGM ratio*. URL: <https://github.com/the-omega-institute/trureturing/blob/e766f6c09bc629e934d0b4d1de2162768da42dea/Library/QuantumBounds/mazhang2026pgmratio.md>.

*Commentary.*

For every 0<a,c<1, b>0 and b^2<a(1-a), all three actual rho_i are PD trace-one states. With A the nonzero effects of the actual optimalPovm, the original strict failure (|A|-1)(P_A-1/3)>2(P_all-1/3) holds if and only if |c-a|<=b AND D>16q AND b^2>2(c-a)^2sqrt(q)/(sqrt(D)(sqrt(D)-4sqrt(q))). The pair-region conjunct is essential. With three active labels the comparison is equality. This binds the strict criterion to the exact optimizer and its active labels, over the complete strict physical domain.

**Theorem 1.21 (sqrt_inverse_square).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.sqrt_inverse_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.sqrt_inverse_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every u>=0, (sqrt(u)^(-1))^2=u^(-1), including u=0. This algebra helper is consumed by the actual symmetric CFC scores.

**Theorem 1.22 (sqrt_inverse_product).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.sqrt_inverse_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.sqrt_inverse_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For u>=0 and any real v, sqrt(u)^(-1)sqrt(v)^(-1)=sqrt(uv)^(-1). This CFC-evaluation algebra helper is consumed by the actual symmetric score calculation.

**Theorem 1.23 (Shared rationalized inverse-square-root residual).**

Lean statement: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.inverse_sqrt_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.inverse_sqrt_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u with 1-u>0, 1/sqrt(1-u)-1=u/[sqrt(1-u)(1+sqrt(1-u))]. This algebra helper is consumed by the actual qubit and loading asymptotic estimates.

Source custody: the mechanism manuscript is anonymous (3 November 2026); no license grant was supplied. The old literal byline remains Wenlin Zhang and Haobo / trureturing, and its actual rational proof is reused as EquiprobablePgmActiveSetRefutation.result. The new note is by Haobo Ma then Wenlin Zhang (4 November 2026), with CC BY 4.0 restricted to that new note. Hyunho Cha is credited for the symmetric scores and qubit/commuting constructions. The metadata URLs locate immutable repository citation records, not public manuscript originals. Activity means a nonzero effect, including rank-one effects; the source wording about positive definite effects is ambiguous. General all-pure and positive-spectral-floor comparisons remain open. No priority or publication claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.active_failure_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.basisFlip`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.complementary_products`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.complete_classification`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.dual_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.dual_score`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.inverse_sqrt_residual`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.inverse_sqrt_two`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.lowerPovm`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.lower_classification`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.optimalPovm`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pairGamma`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pairPovm`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pair_classification`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.pair_failure_iff`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.rho`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.sqrt_inverse_product`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.sqrt_inverse_square`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.states_posDef`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.symmetric_scores`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upperGamma`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upperPovm`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmSymmetric.upper_classification`
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Matrix/SpectralPower.md)
- Dependency: [D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity](EquiprobablePgmSupportIdentity.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
