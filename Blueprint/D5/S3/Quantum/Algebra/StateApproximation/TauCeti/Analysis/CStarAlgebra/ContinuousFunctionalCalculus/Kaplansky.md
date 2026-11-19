# Self-adjoint truncation by functional calculus

## Abstract

Self-adjoint truncation by functional calculus

The real function f(t)=2t/(1+t squared) maps the real line into the closed unit interval in absolute value. Its right inverse there is g(s)=s/(1+sqrt(1-s squared)). Functional calculus gives norm(cfc f a) at most one, and cfc f (cfc g b)=b for every self-adjoint contraction b. Along any filter, pointwise strong convergence of self-adjoint operators to a self-adjoint operator is preserved by cfc f. No uniform norm bound on the approximating operators is assumed. The difference identity with rho(t)=(1+t squared) inverse and tau(t)=t/(1+t squared), whose calculus norms are at most one and one half, supplies the convergence estimate.

**Theorem 1.1 (kaplanskyFun_def).**

$$\forall (t : \mathbb{R} ), Eq.\{1\} (TauCeti.kaplanskyFun t) (HDiv.hDiv.\{0, 0, 0\} (HMul.hMul.\{0, 0, 0\} 2 t) (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.kaplanskyFun_def` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfold kaplanskyFun: the defining real rational function has numerator 2t and denominator 1+t squared. This definitional identity is the rewriting input for the range bound and inverse calculation.

**Theorem 1.2 (kaplanskyFunInv_def).**

$$\forall (s : \mathbb{R} ), Eq.\{1\} (TauCeti.kaplanskyFunInv s) (HDiv.hDiv.\{0, 0, 0\} s (HAdd.hAdd.\{0, 0, 0\} 1 \operatorname{sqrt} (HSub.hSub.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} s 2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.kaplanskyFunInv_def` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfold kaplanskyFunInv: its denominator is 1 plus the nonnegative real square root of 1-s squared. The identity fixes the chosen inverse branch used in kaplanskyFun_kaplanskyFunInv.

**Theorem 1.3 (continuous_inv_one_add_sq).**

$$Continuous.\{0, 0\} fun (t : \mathbb{R} ) \mapsto Inv.inv.\{0\} (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_inv_one_add_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function 1+t squared is continuous by continuous_pow and continuous addition. The helper one_add_sq_pos excludes zero at every real t, so Continuous.inv₀ makes its reciprocal continuous.

**Theorem 1.4 (continuous_div_one_add_sq).**

$$Continuous.\{0, 0\} fun (t : \mathbb{R} ) \mapsto HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_div_one_add_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the identity numerator and 1+t squared denominator are continuous. The strict positivity supplied by one_add_sq_pos permits Continuous.div, giving continuity without restricting t.

**Theorem 1.5 (continuous_kaplanskyFun).**

$$Continuous.\{0, 0\} TauCeti.kaplanskyFun$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_kaplanskyFun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator 2t is continuous, as is the polynomial denominator. Since one_add_sq_pos excludes denominator zeros, Continuous.div proves continuity of kaplanskyFun on the whole real line.

**Theorem 1.6 (continuous_kaplanskyFunInv).**

$$Continuous.\{0, 0\} TauCeti.kaplanskyFunInv$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_kaplanskyFunInv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuous.sqrt applies to the continuous real function 1-s squared, even outside the unit interval. Its square root is nonnegative, so adding 1 gives a strictly positive denominator; Continuous.div proves continuity of the inverse formula everywhere.

**Theorem 1.7 (abs_kaplanskyFun_le_one).**

$$\forall (t : \mathbb{R} ), LE.le.\{0\} (abs.\{0\} (TauCeti.kaplanskyFun t)) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.abs_kaplanskyFun_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrite the absolute value of the rational expression using kaplanskyFun_def and the positive denominator one_add_sq_pos. The resulting inequality 2 abs(t) at most 1+t squared follows from nonnegativity of (abs(t)-1) squared and sq_abs.

**Theorem 1.8 (kaplanskyFun_kaplanskyFunInv).**

$$\forall \{s : \mathbb{R} \}, LE.le.\{0\} (abs.\{0\} s) 1 \to Eq.\{1\} (TauCeti.kaplanskyFun (TauCeti.kaplanskyFunInv s)) s$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.kaplanskyFun_kaplanskyFunInv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From abs(s) at most 1 derive 1-s squared nonnegative. Real.sq_sqrt supplies the square-root identity and Real.sqrt_nonneg makes the inverse denominator nonzero. Substitute kaplanskyFun_def and kaplanskyFunInv_def, clear denominators, and use that square-root identity to reduce the rational expression to s.

**Theorem 1.9 (abs_div_one_add_sq_le).**

$$\forall (t : \mathbb{R} ), LE.le.\{0\} (abs.\{0\} (HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2)))) (1 / 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.abs_div_one_add_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive denominator one_add_sq_pos allows multiplication of the desired bound by 1+t squared. After abs_div and sq_abs, the inequality follows from nonnegativity of (abs(t)-1) squared, as in the bound for kaplanskyFun.

**Theorem 1.10 (cfc_one_add_sq).**

$$\forall \{A : Type u_1\} [Ring.\{u_1\} A] [StarRing.\{u_1\} A] [Algebra.\{0, u_1\} \mathbb{R} A] [TopologicalSpace.\{u_1\} A] [ContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] \{a : A\}, IsSelfAdjoint.\{u_1\} a \to Eq.\{u_1 + 1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2)) a) (HAdd.hAdd.\{u_1, u_1, u_1\} 1 (HPow.hPow.\{u_1, 0, u_1\} a 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_one_add_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use cfc_const_add to split the constant and square terms, then cfc_pow_id for the square. Algebra.algebraMap_eq_smul_one and one_smul identify the constant functional calculus value with the algebra unit.

**Theorem 1.11 (cfc_div_one_add_sq_eq_mul).**

$$\forall \{A : Type u_1\} [Ring.\{u_1\} A] [StarRing.\{u_1\} A] [Algebra.\{0, u_1\} \mathbb{R} A] [TopologicalSpace.\{u_1\} A] [ContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] \{a : A\}, IsSelfAdjoint.\{u_1\} a \to Eq.\{u_1 + 1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a) (HMul.hMul.\{u_1, u_1, u_1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto Inv.inv.\{0\} (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a) a)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_div_one_add_sq_eq_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewrite scalar division as inverse times t using div_eq_inv_mul, and transfer that equality through cfc_congr. Then cfc_mul, with continuous_inv_one_add_sq, separates the factors, and cfc_id' identifies the identity-function factor with a.

**Theorem 1.12 (cfc_div_one_add_sq_eq_mul_left).**

$$\forall \{A : Type u_1\} [Ring.\{u_1\} A] [StarRing.\{u_1\} A] [Algebra.\{0, u_1\} \mathbb{R} A] [TopologicalSpace.\{u_1\} A] [ContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] \{a : A\}, IsSelfAdjoint.\{u_1\} a \to Eq.\{u_1 + 1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a) (HMul.hMul.\{u_1, u_1, u_1\} a (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto Inv.inv.\{0\} (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_div_one_add_sq_eq_mul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use div_eq_mul_inv and cfc_congr to put t first. cfc_mul separates it from the reciprocal factor, using continuous_id and continuous_inv_one_add_sq; cfc_id' then gives a times the reciprocal functional calculus value. This supplies the opposite product order needed by the difference identity.

**Theorem 1.13 (cfc_kaplanskyFun_eq_smul).**

$$\forall \{A : Type u_1\} [Ring.\{u_1\} A] [StarRing.\{u_1\} A] [Algebra.\{0, u_1\} \mathbb{R} A] [TopologicalSpace.\{u_1\} A] [ContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] (a : A), Eq.\{u_1 + 1\} (cfc.\{0, u_1\} TauCeti.kaplanskyFun a) (HSMul.hSMul.\{0, u_1, u_1\} 2 (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_kaplanskyFun_eq_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise kaplanskyFun_def rewrites the scalar function as twice t/(1+t squared). cfc_smul, justified by continuous_div_one_add_sq, moves this scalar multiple outside the functional calculus; cfc_congr matches the two scalar expressions.

**Theorem 1.14 (cfc_kaplanskyFun_sub_cfc_kaplanskyFun).**

$$\forall \{A : Type u_1\} [Ring.\{u_1\} A] [StarRing.\{u_1\} A] [Algebra.\{0, u_1\} \mathbb{R} A] [TopologicalSpace.\{u_1\} A] [ContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] \{a b : A\}, IsSelfAdjoint.\{u_1\} a \to IsSelfAdjoint.\{u_1\} b \to Eq.\{u_1 + 1\} (HSub.hSub.\{u_1, u_1, u_1\} (cfc.\{0, u_1\} TauCeti.kaplanskyFun a) (cfc.\{0, u_1\} TauCeti.kaplanskyFun b)) (HSMul.hSMul.\{0, u_1, u_1\} 2 (HAdd.hAdd.\{u_1, u_1, u_1\} (HMul.hMul.\{u_1, u_1, u_1\} (HMul.hMul.\{u_1, u_1, u_1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto Inv.inv.\{0\} (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a) (HSub.hSub.\{u_1, u_1, u_1\} a b)) (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto Inv.inv.\{0\} (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) b)) (HMul.hMul.\{u_1, u_1, u_1\} (HMul.hMul.\{u_1, u_1, u_1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a) (HSub.hSub.\{u_1, u_1, u_1\} b a)) (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) b))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_kaplanskyFun_sub_cfc_kaplanskyFun` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use cfc_kaplanskyFun_eq_smul and the two product-order formulas for cfc_div_one_add_sq. The inverse and direct values of cfcUnits for 1+t squared multiply to 1, and cfc_one_add_sq identifies the direct factors. Insert these two units into the difference; expanding while preserving factor order yields the stated noncommutative identity, without assuming a and b commute.

**Theorem 1.15 (norm_cfc_kaplanskyFun_le).**

$$\forall \{A : Type u_1\} [NormedRing.\{u_1\} A] [StarRing.\{u_1\} A] [NormedAlgebra.\{0, u_1\} \mathbb{R} A] [IsometricContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] (a : A), LE.le.\{0\} (Norm.norm.\{u_1\} (cfc.\{0, u_1\} TauCeti.kaplanskyFun a)) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.norm_cfc_kaplanskyFun_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar estimate abs_kaplanskyFun_le_one bounds the function on every spectral value. Apply norm_cfc_le with nonnegative bound 1 to obtain the operator norm estimate; the total functional calculus convention also covers elements outside the self-adjoint predicate.

**Theorem 1.16 (norm_cfc_inv_one_add_sq_le).**

$$\forall \{A : Type u_1\} [NormedRing.\{u_1\} A] [StarRing.\{u_1\} A] [NormedAlgebra.\{0, u_1\} \mathbb{R} A] [IsometricContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] (a : A), LE.le.\{0\} (Norm.norm.\{u_1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto Inv.inv.\{0\} (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a)) 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.norm_cfc_inv_one_add_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Since 1+t squared is at least 1, its positive reciprocal is at most 1 by inv_le_one_of_one_le₀. With one_add_sq_pos this bounds the absolute value at every real spectral value, and norm_cfc_le transfers the bound to the algebra.

**Theorem 1.17 (norm_cfc_div_one_add_sq_le).**

$$\forall \{A : Type u_1\} [NormedRing.\{u_1\} A] [StarRing.\{u_1\} A] [NormedAlgebra.\{0, u_1\} \mathbb{R} A] [IsometricContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] (a : A), LE.le.\{0\} (Norm.norm.\{u_1\} (cfc.\{0, u_1\} (fun (t : \mathbb{R} ) \mapsto HDiv.hDiv.\{0, 0, 0\} t (HAdd.hAdd.\{0, 0, 0\} 1 (HPow.hPow.\{0, 0, 0\} t 2))) a)) (1 / 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.norm_cfc_div_one_add_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply norm_cfc_le with the nonnegative bound one half. The scalar bound on every spectral value is exactly abs_div_one_add_sq_le, so the same bound holds for its functional calculus value.

**Theorem 1.18 (cfc_kaplanskyFun_cfc_kaplanskyFunInv).**

$$\forall \{A : Type u_1\} [NormedRing.\{u_1\} A] [StarRing.\{u_1\} A] [NormedAlgebra.\{0, u_1\} \mathbb{R} A] [IsometricContinuousFunctionalCalculus.\{0, u_1\} \mathbb{R} A IsSelfAdjoint.\{u_1\}] \{b : A\}, IsSelfAdjoint.\{u_1\} b \to LE.le.\{0\} (Norm.norm.\{u_1\} b) 1 \to Eq.\{u_1 + 1\} (cfc.\{0, u_1\} TauCeti.kaplanskyFun (cfc.\{0, u_1\} TauCeti.kaplanskyFunInv b)) b$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_kaplanskyFun_cfc_kaplanskyFunInv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use cfc_comp to compose the two continuous scalar functions. For each spectral value s of b, norm_apply_le_norm_cfc applied to the identity function bounds abs(s) by norm(b), hence by 1. kaplanskyFun_kaplanskyFunInv therefore identifies the composition with the identity on the spectrum; cfc_congr and cfc_id' recover b.

**Theorem 1.19 (tendsto_cfc_kaplanskyFun_apply).**

$$\forall \{H : Type u_1\} [NormedAddCommGroup.\{u_1\} H] [InnerProductSpace.\{0, u_1\} \mathbb{C} H] [CompleteSpace.\{u_1\} H] \{\iota : Type u_2\} \{l : Filter.\{u_2\} \iota \} \{x : \iota \to ContinuousLinearMap.\{0, 0, u_1, u_1\} (RingHom.id.\{0\} \mathbb{C} ) H H\} \{y : ContinuousLinearMap.\{0, 0, u_1, u_1\} (RingHom.id.\{0\} \mathbb{C} ) H H\}, (Filter.Eventually (fun (i : \iota ) \mapsto IsSelfAdjoint.\{u_1\} (x i)) l) \to IsSelfAdjoint.\{u_1\} y \to (\forall (v : H), Filter.Tendsto.\{u_2, u_1\} (fun (i : \iota ) \mapsto (x i) v) l (nhds.\{u_1\} (y v))) \to \forall (v : H), Filter.Tendsto.\{u_2, u_1\} (fun (i : \iota ) \mapsto (cfc.\{0, u_1\} TauCeti.kaplanskyFun (x i)) v) l (nhds.\{u_1\} ((cfc.\{0, u_1\} TauCeti.kaplanskyFun y) v))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.tendsto_cfc_kaplanskyFun_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the vectors w1=rho(y)v and w2=sigma(y)v, with rho(t)=1/(1+t squared) and sigma(t)=t/(1+t squared). The difference identity bounds the norm of the desired difference eventually by 2 times (norm(x(i)w1-yw1)+one half times norm(x(i)w2-yw2)), using norm_cfc_inv_one_add_sq_le and norm_cfc_div_one_add_sq_le. Both errors tend to zero by the given pointwise convergence, so squeeze_zero' proves convergence along the original filter without a uniform norm bound on x(i).

## References

- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.abs_div_one_add_sq_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.abs_kaplanskyFun_le_one`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_div_one_add_sq_eq_mul`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_div_one_add_sq_eq_mul_left`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_kaplanskyFun_cfc_kaplanskyFunInv`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_kaplanskyFun_eq_smul`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_kaplanskyFun_sub_cfc_kaplanskyFun`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.cfc_one_add_sq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_div_one_add_sq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_inv_one_add_sq`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_kaplanskyFun`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.continuous_kaplanskyFunInv`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.kaplanskyFunInv_def`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.kaplanskyFun_def`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.kaplanskyFun_kaplanskyFunInv`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.norm_cfc_div_one_add_sq_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.norm_cfc_inv_one_add_sq_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.norm_cfc_kaplanskyFun_le`
- Truth anchor: `D5/S3/Quantum/Algebra/StateApproximation/TauCeti/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Kaplansky.tendsto_cfc_kaplanskyFun_apply`
