# An Elmer--Kadr Relative Tensor Counterexample

## Abstract

The p=3, q=27, i=j=7 tensor product fails the predicted relative stable isomorphism.

The statement source is Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, Conjecture 3.7(a). The module and stable-category conventions are formulas (11)--(12), Section 2.2 and Lemma 2.1(iii). This development claims no literature priority. The negative result concerns this concrete instance; it does not compute a replacement decomposition.

**Definition 1.1 (The exact relative stable claim).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample.claim`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K is GaloisField 3 3, an actual field of characteristic three and cardinality twenty-seven. G is Multiplicative K, the multiplicative type tag on the additive group of K. Primal K m is the polynomial subspace of degree strictly less than m, acted on by actual translations z maps to z+alpha. The correspondence z^i maps to X^i Y^(m-1-i) identifies its monomial basis and action with formula (11) for S^(m-1)(W). DualPower K m is the actual linear dual, and dualAction is the Mathlib contragredient of primalAction.

The source bridge is checked on the primal monomial basis: dual_action_basis_value proves rho_m(alpha)(e_i)(z^j) = binom(j,i)(-alpha)^(j-i). Thus the coordinate matrix is exactly formula (12), including the negative sign from the inverse group element. No assumption identifying a separately postulated matrix action with the dual is used. TensorSpace is the actual tensor product of the two seven-dimensional duals, and tensorAction is its diagonal representation.

RelativeSpace is the actual direct sum over h=1,...,9 of DualPower K (3h), and relativeAction is the direct-sum action. RelativeProjective means an equivariant retract of X tensor RelativeSpace for an arbitrary bundled representation X, exactly Lemma 2.1(iii). RelativeFactors allows arbitrary intermediate representations with that property. RelativeStableIso asks for two actual equivariant maps whose two composites differ from the respective identities by maps in RelativeFactors. This is the inverse-morphism condition in the original quotient Hom_G/PHom_G,M, not merely the splitting of a selected embedding. The public definition claim has type Prop and asserts this relation between V_13 and V_7 tensor V_7. Since 7=2*3+1, the source residue condition is 1+1<=3, the size condition is 7+7<=27, and the source sum has just the predicted summand V_13.

**Theorem 1.2 (The relative stable isomorphism is impossible).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample.result`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The designated theorem result is literally Not claim. Its helpers prove the obstruction for every characteristic-three field of cardinality twenty-seven and then instantiate the Mathlib finite field. The conclusion quantifies over every pair of actual equivariant maps and every relative-projective intermediate factor. No rational SL2 action, torus equivariance, homogeneous-map assumption or chosen inclusion is imposed.

Write A_k for the degree-k coefficient on V_13 and B_k for the degree-k tensor coefficient. The action degrees are at most twelve. Finite-field power sums prove A_k = -sum_alpha alpha^(26-k)rho_V(alpha), and the analogous B_k formula. Every G-map therefore intertwines these coefficients. With w=e_6 tensor e_6, B_12(e_0 tensor e_0)=w=B_6(e_3 tensor e_3), and the image of B_12 is contained in K w. The image of A_12 is K e_12, while the e_12 coordinate of A_6 is zero because binom(12,6)=924 vanishes in characteristic three. Consequently every g from the tensor to V_13 kills w, and every f in the reverse direction has g f(e_12)=0.

The vectors e_i=(-1)^i A_i e_0 make the diagonal of any G-endomorphism of V_13 constant. Its trace is thirteen times that constant, hence equals its e_12 diagonal coordinate in characteristic three. Thus trace(g f)=0 for all such pairs, whereas trace(id)=1.

The relative-projectivity bridge uses the actual subgroup C3 of translations by the prime field. For each r, the invariant monic modulus (z^3-z)^r identifies polynomial reduction with the original degree<3r space. Multiplication by -z^2 followed by this reduction has conjugation sum id: the three translates of -z^2 sum to one. Translation commutes with reduction because the modulus is invariant. Transposition transfers the identity to the actual dual V_(3r); the direct-sum identity gives a norm-one endomorphism on M. On any X tensor M, tensoring that endomorphism with id_X preserves its conjugation-sum identity under the actual diagonal subgroup action.

If an endomorphism of V_13 factors through a retract of X tensor M, compose the factor maps with the actual retract maps. The resulting endomorphism is the sum of three conjugates of a single endomorphism of V_13. Conjugation leaves its ordinary field trace invariant, so its trace is zero. Only the finite-dimensional target V_13 is traced; X and the retract need no finiteness assumption. Applying this to g f-id in the original relative ideal contradicts trace(g f)=0 and trace(id)=1. The argument never treats the first polynomial coefficient operator as primitive on arbitrary finite-group tensor factors.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample.claim`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample.result`
