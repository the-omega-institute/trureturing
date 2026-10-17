# Integral matrices for Dirichlet translation twists

## Abstract

Integral translation intertwiners at every positive modulus and their actual cusp-space consumer.

**Theorem 1.1 (The integral intertwiner for all residues).**

$$T_{u} \cdot \gamma = M \cdot T_{v}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix.gamma0_translation_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N be any positive natural number, gamma = [a,b;c,d] any actual integral determinant-one matrix in Gamma0(N squared), and u any element of ZMod N. No primality or unit assumption on u is imposed; N=1 and composite moduli are included. The theorem proves that d modulo N is a unit, that N divides d*u.val - a*(d squared*u).val in the integers, and that an actual M in SL(2,Z) intertwines the two real translations. Here v=d squared*u, T_u=upperRightHom(u.val/N), and every mapGL is the actual integral-to-real group homomorphism.

Write c=N squared*h and d*U-a*V=N*t, with U=u.val and V=v.val. The constructed matrix is [a+N*h*U, b+t-h*U*V; N squared*h, d-N*h*V]. Its determinant is one by the two divisibility identities and det(gamma)=1. The real matrix identity follows entry by entry. Modulo N the determinant gives a*d=1, so d has inverse a even when ZMod N is not a field, and d*U-a*V=0 modulo N. These derived facts supply the integral witness rather than assuming it.

This is a classical translation construction from the theory of Dirichlet twists: A. O. L. Atkin and Wen Ch'ing Winnie Li, Twists of Newforms and Pseudo-Eigenvalues of W-Operators, Inventiones Mathematicae 48 (1978), 221-243, Proposition 3.1. The exact integral matrix and its Mathlib realization are the implementation here; no novelty or open-problem resolution is claimed.

**Theorem 1.2 (The actual translated subgroup).**

$$\Gamma_{1}(N^{2}) \subseteq \left(T_{u}\right)^{-1} \cdot \operatorname{SL}\left(2, Z\right) \cdot T_{u}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix.gamma1_le_translation_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement concerns the actual real image of Gamma1(N squared) as a subgroup of GL(2,R). Since d=1 modulo N, the preceding integral matrix theorem has v=u and proves the inclusion in T_u inverse times SL2(Z) times T_u. This auxiliary theorem is consumed by the restriction of each actual translated cusp form.

**Definition 1.3 (The actual cusp-space linear operator).**

$$dirichletTranslationTwist : \operatorname{CuspForm}\left(\operatorname{SL}\left(2, Z\right), k\right) \to \operatorname{CuspForm}\left(\Gamma_{1}(N^{2}), k\right)$$

*Formalization.* `D5/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix.dirichletTranslationTwist` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any integer weight k and any complex Dirichlet character chi modulo N, the definition is a complex-linear map from the actual level-one cusp space into the actual cusp space for Gamma1(N squared). It is the inverse of gaussSum(chi inverse, ZMod.stdAddChar) times the finite sum over every u in ZMod N of chi inverse(u) times the translated form. Pointwise the summands are f(u.val/N + z). The definition does not require primitivity: inversion in C is total.

Each summand uses Mathlib's CuspForm.translate for the real matrix T_u. Its invariance is restricted by the proved subgroup inclusion, its holomorphic field is retained, and its vanishing field at every cusp is transported using IsCusp.mono. Thus the consumer is an actual all-cusp bundle, with no assumed modularity or cusp condition for the output. Finite sums and scalar multiplication then give the linear map.

The Gamma0 character-square transformation law for this same operator, primitive Gauss-sum nonvanishing and normalization, lift and period identities, rational-shift exponentials, convergent HasSum manipulation, and every period-one qExpansion coefficient remain outstanding. This module does not prove the full primitive-twist theorem and does not reuse the level-one prime Hecke endomorphism as the new-level output.

The same-delivery four-slot Reg audit is unfinished: the exact source-selection reconstruction, whole-family variation and sensitivity, and actual observational-dependence bridges for the two public theorems have not been proved. The exact missing bridges and full statements are recorded in https://github.com/the-omega-institute/trureturing/issues/17977; no declared_validated registration is claimed.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix.dirichletTranslationTwist`
- Truth anchor: `D5/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix.gamma0_translation_intertwining`
- Truth anchor: `D5/S3/Arith/ModularForms/PrimitiveDirichletTwistMatrix.gamma1_le_translation_conjugate`
