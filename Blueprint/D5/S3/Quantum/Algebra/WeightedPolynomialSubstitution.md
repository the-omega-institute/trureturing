# Weighted Polynomial Substitution

## Abstract

Mixed weighted polynomial substitution

Let R be any commutative semiring, sigma and tau arbitrary types in independent universes, and v:sigma->Nat and w:tau->Nat arbitrary weights. Put A=MvPolynomial(tau,R) and use a separate univariate cover variable t of weight one in Polynomial(A). There is no finiteness assumption on either variable type, no positive-weight assumption, and no domain or nontriviality assumption on R. Polynomial and monomial supports make every sum finite. Subtraction alone requires CommRing R.

HasTotalWeight(w,P,N) means that for every r:Nat and d:tau ->_0 Nat, a nonzero scalar coefficient coeff_d(coeff_r(P)) implies weight_w(d)+r=N. It is a support conservation law, not only a degree estimate. In particular r>N forces coeff_r(P)=0. Zero polynomials have every total weight, and zero weights and an empty variable type are included.

The proof uses Mathlib weighted homogeneous polynomials, finite monomial evaluation, and both coefficient-convolution formulas. If a product coefficient is nonzero, some pair of cover degrees and then some pair of coefficient monomials has nonzero product. Each factor coefficient is nonzero even over a semiring with zero divisors; applying the two support laws and adding their weights proves conservation. Induction extends this to powers, finite products and sums. The finite evaluation expansion then preserves the source monomial weight. This shared conservation argument is the substantive reusable inference; constant, cast, additive and signed-coefficient facts are consumed support. These are classical graded-polynomial arguments, not a claim of literature novelty or a solution of a named open problem.

The live application is the original half-Fock translation in LatticeHalfFockChargedLZero. The natural weights are 2k+1 and a translated variable is a difference of two terms of that same mixed weight. Signed coefficient lowering gives N-r without truncated subtraction and is the bridge to the original creation index e+B(a,a)+r. No second natural-subtraction API or unused above-weight wrapper is retained.

**Definition 1.1 (Mixed coefficient and cover weight).**

$$\operatorname{HasTotalWeight}\left(w, P, N\right)\iff\operatorname{supportConservation}\left(w, P, N\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.HasTotalWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For w:tau->Nat, P:Polynomial(MvPolynomial(tau,R)) and N:Nat, the definition quantifies every r:Nat and d:tau ->_0 Nat. Nonzero coeff_d(coeff_r(P)) implies weight_w(d)+r=N. Definitions carry no new-content credit.

**Theorem 1.2 (Constant cover embedding).**

$$\operatorname{Hom}\left(w, p, N\right)\implies\operatorname{HasTotalWeight}\left(w, \operatorname{C}\left(p\right), N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original R,tau,CommSemiring R,w,p,N and hp:IsWeightedHomogeneous w p N, Polynomial.C p has total weight N. Only cover degree zero survives; its coefficient homogeneity is exactly hp. This support lemma is used by the unit and evaluation proofs and by the original translation.

**Theorem 1.3 (Pure cover powers).**

$$\operatorname{HasTotalWeight}\left(w, t^{k}, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.X_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary R,tau,CommSemiring R,w and k:Nat, X^k:Polynomial(MvPolynomial(tau,R)) has total weight k. Its only possible cover coefficient is the coefficient-ring unit at degree k, of coefficient weight zero. Used by the actual translated variable.

**Theorem 1.4 (Conservation through two coefficient convolutions).**

$$\operatorname{HasTotalWeight}\left(w, P, N\right)\land\operatorname{HasTotalWeight}\left(w, Q, M\right)\implies\operatorname{HasTotalWeight}\left(w, PQ, N+M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all original R,tau,CommSemiring R,w,P,Q,N,M and hP,hQ of the indicated total weights, P*Q has weight N+M. The two nonzero summands extracted from cover and coefficient antidiagonals give i+j=r and u+v=d. Additivity of Finsupp.weight gives weight(d)+r=N+M. No cancellation, integral-domain or positivity hypothesis is used. Powers, products, evaluation and translation consume this conservation.

**Theorem 1.5 (Difference at a common weight).**

$$\operatorname{HasTotalWeight}\left(w, P, N\right)\land\operatorname{HasTotalWeight}\left(w, Q, N\right)\implies\operatorname{HasTotalWeight}\left(w, P-Q, N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here R is a commutative ring. For w,P,Q,N and both original total-weight premises, P-Q has total weight N. Negation preserves scalar support and addition uses whichever summand coefficient is nonzero. This is support for the original difference defining halfTranslationVariable, not independent new mathematical content.

**Theorem 1.6 (Exact natural to integer weight conversion).**

$$\operatorname{weight}\left(wZ, d\right)=\operatorname{IntCast}\left(\operatorname{weight}\left(w, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.weight_intCast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any tau, w:tau->Nat and d:tau ->_0 Nat, Finsupp.weight (fun x => (w x:Int)) d equals the integer cast of Finsupp.weight w d. Expand the same finite support sum and commute casts with sums and products. This normalization is consumed by signed lowering and half-frequency energy conversion; it supplies no separate content credit.

**Theorem 1.7 (Signed homogeneous conversion).**

$$\operatorname{Hom}\left(w, p, N\right)\implies\operatorname{Hom}\left(wZ, p, \operatorname{IntCast}\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.homogeneous_intCast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original R,tau,CommSemiring R,w,p,N and hp:IsWeightedHomogeneous w p N, p is homogeneous for integer-cast weights at (N:Int). Apply weight_intCast to each nonzero coefficient. The creation and oscillator-input stages consume it.

**Theorem 1.8 (Signed coefficient lowering).**

$$\operatorname{HasTotalWeight}\left(w, P, N\right)\implies\operatorname{Hom}\left(wZ, \operatorname{coeff}\left(r, P\right), \operatorname{IntCast}\left(N\right)-r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.coeff_homogeneous_int` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all original R,tau,CommSemiring R,w,P,N,hP and r:Nat, P.coeff r is integer-weight homogeneous at (N:Int)-r. Cast the exact equality weight(d)+r=N and subtract in Int. In particular r>N does not turn a negative weight into zero: no coefficient monomial has negative natural weight, so the coefficient vanishes. This is the live signed lowering used by the original charged proof.

**Theorem 1.9 (Generic weighted substitution conservation).**

$$(\forall i, \operatorname{HasTotalWeight}\left(w, \operatorname{f}\left(i\right), \operatorname{v}\left(i\right)\right))\land\operatorname{Hom}\left(v, p, N\right)\implies\operatorname{HasTotalWeight}\left(w, \operatorname{eval2}\left(f, p\right), N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.eval2_totalWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For independent arbitrary types sigma,tau,R, CommSemiring R, v:sigma->Nat, w:tau->Nat, f:sigma->Polynomial(MvPolynomial(tau,R)), hf:forall i, HasTotalWeight w (f i) (v i), p:MvPolynomial(sigma,R), N:Nat and hp:IsWeightedHomogeneous v p N, the original MvPolynomial.eval2 (algebraMap R (Polynomial(MvPolynomial(tau,R)))) f p has total weight N. Expand p over finite monomial support. Each evaluated variable power has its prescribed multiple weight; their product has the source monomial weight N. The scalar coefficient embeds at weight zero and the finite sum keeps N. The actual halfTranslatedPolynomial proof consumes the theorem.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.C`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.HasTotalWeight`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.X_pow`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.coeff_homogeneous_int`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.eval2_totalWeight`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.homogeneous_intCast`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.mul`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.sub`
- Truth anchor: `D5/S3/Quantum/Algebra/WeightedPolynomialSubstitution.weight_intCast`
