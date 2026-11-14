# Effect additivity stability

## Abstract

Binary defect on all actual effects controls real scaling and signed finite families.

Throughout the formulas, Id(d) is the actual identity matrix, real(n) is the real embedding of a natural number, card(J) is the finite type cardinality, and dots denote multiplication or scalar action according to the displayed types. The map ofMatrixInverse is the inverse of the canonical CStarMatrix.ofMatrix equivalence. Type and the anonymous instance brackets retain the universe-polymorphic finite index assumptions.

Write Mat d for Matrix (Fin d) (Fin d) Complex, with d any natural number. An effect E means that E is positive semidefinite and identity minus E is positive semidefinite. Every displayed p is an arbitrary total real function on these actual matrices; only its effect values enter the estimates.

The interval argument applies a supremum contraction to g(t)=p(t*E)-t*p(E). Positivity and normalization bound this function; binary defect gives the contraction. A nonempty weighted list then accumulates its binary and homogeneity errors. Splitting signed coefficients and rescaling by K squared gives the general finite-family estimate. Zero terms are retained throughout.

**Definition 1.1 (Mat).**

$$\forall (d: \mathbb{N}), (\operatorname{Mat}(d) = \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectAdditivityStability.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix space in dimension d is the actual complex square matrix algebra indexed by Fin d.

**Definition 1.2 (IsEffect).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\operatorname{IsEffect}(E) \iff ((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectAdditivityStability.IsEffect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An effect is an actual positive semidefinite complex matrix whose complement to the identity is also positive semidefinite.

**Theorem 1.3 (effect iff order).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\operatorname{IsEffect}(E) \iff ((0 \leq E) \land (E \leq \operatorname{Id}(d)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_iff_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two positive semidefinite conditions defining an effect are equivalent to the native matrix-order interval from zero to the identity.

**Theorem 1.4 (cstar effect bridge).**

$$\forall (d: \mathbb{N}), (\forall (X: \operatorname{CStarMatrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C})), (\operatorname{IsEffect}(\operatorname{ofMatrixInverse}(X)) \iff ((0 \leq X) \land (X \leq 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.cstar_effect_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native C-star matrix equivalence identifies the same actual effects with its order interval from zero to one.

**Theorem 1.5 (bounded interval stability).**

$$\forall (g: \mathbb{R} \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (\forall (M: \mathbb{R}), (((0 \leq \varepsilon) \land (g(1) = 0) \land (\forall (t: \mathbb{R}), (((0 \leq t) \land (t \leq 1)) \implies (\lvert g(t) \rvert  \leq M))) \land (\forall (s: \mathbb{R}), (\forall (t: \mathbb{R}), (((0 \leq s) \land (0 \leq t) \land ((s+t) \leq 1)) \implies (\lvert ((g((s+t))-g(s))-g(t)) \rvert  \leq \varepsilon))))) \implies (\forall (t: \mathbb{R}), (((0 \leq t) \land (t \leq 1)) \implies (\lvert g(t) \rvert  \leq (2 \cdot \varepsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.bounded_interval_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every bounded real function g on the unit interval with g(1)=0 and binary additive defect at most epsilon has absolute value at most twice epsilon throughout that interval. The bound M is arbitrary; no continuity or measurability is assumed.

**Theorem 1.6 (probability bounds).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (((\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (0 \leq p(E)))) \land (\forall (E: \operatorname{Mat}(d)), (\forall (F: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land ((\operatorname{PosSemidef}((E+F))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(E+F)))))) \implies (\lvert ((p((E+F))-p(E))-p(F)) \rvert  \leq \varepsilon)))) \land (p(\operatorname{Id}(d)) = 1)) \implies (((0 \leq p(0)) \land (p(0) \leq \varepsilon)) \land (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies ((0 \leq p(E)) \land (p(E) \leq (1+\varepsilon)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.probability_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegativity on all effects, normalization at the identity and the stated binary defect imply that p(0) lies between zero and epsilon, and every effect value lies between zero and 1+epsilon. No separate sign premise on epsilon is added.

**Theorem 1.7 (effect homogeneity).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (((0 \leq \varepsilon) \land ((\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (0 \leq p(E)))) \land (\forall (E: \operatorname{Mat}(d)), (\forall (F: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land ((\operatorname{PosSemidef}((E+F))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(E+F)))))) \implies (\lvert ((p((E+F))-p(E))-p(F)) \rvert  \leq \varepsilon)))) \land (p(\operatorname{Id}(d)) = 1))) \implies (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (\forall (t: \mathbb{R}), (((0 \leq t) \land (t \leq 1)) \implies (\lvert (p((t \cdot E))-(t \cdot p(E))) \rvert  \leq (2 \cdot \varepsilon)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_homogeneity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual effect and every real scale in the closed unit interval, the homogeneity error is at most 2*epsilon, under precisely the displayed global positivity, normalization and binary-defect hypotheses.

**Theorem 1.8 (finite sum error).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), ((\forall (E: \operatorname{Mat}(d)), (\forall (F: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land ((\operatorname{PosSemidef}((E+F))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(E+F)))))) \implies (\lvert ((p((E+F))-p(E))-p(F)) \rvert  \leq \varepsilon)))) \implies (\forall (n: \mathbb{N}), (\forall (A: \operatorname{Fin}((n+1)) \to \operatorname{Mat}(d)), (((\forall (i: \operatorname{Fin}((n+1))), (\operatorname{PosSemidef}(A(i)))) \land ((\operatorname{PosSemidef}(\sum_{i: \operatorname{Fin}((n+1))} (A(i)))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\sum_{i: \operatorname{Fin}((n+1))} (A(i))))))) \implies (\lvert (p(\sum_{i: \operatorname{Fin}((n+1))} (A(i)))-\sum_{i: \operatorname{Fin}((n+1))} (p(A(i)))) \rvert  \leq (\operatorname{real}(n) \cdot \varepsilon))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_sum_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A list of n+1 positive semidefinite matrices whose total is an effect accumulates at most n*epsilon additive error. Only binary-defect control is assumed; no p(0)=0 or additional epsilon-sign premise is imposed.

**Theorem 1.9 (weighted finite sum error).**

$$\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (((0 \leq \varepsilon) \land ((\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (0 \leq p(E)))) \land (\forall (E: \operatorname{Mat}(d)), (\forall (F: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land ((\operatorname{PosSemidef}((E+F))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(E+F)))))) \implies (\lvert ((p((E+F))-p(E))-p(F)) \rvert  \leq \varepsilon)))) \land (p(\operatorname{Id}(d)) = 1))) \implies (\forall (B: \operatorname{Fin}((n+1)) \to \operatorname{Mat}(d)), (\forall (t: \operatorname{Fin}((n+1)) \to \mathbb{R}), (((\forall (i: \operatorname{Fin}((n+1))), ((\operatorname{PosSemidef}(B(i))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-B(i)))))) \land (\forall (i: \operatorname{Fin}((n+1))), ((0 \leq t(i)) \land (t(i) \leq 1))) \land ((\operatorname{PosSemidef}(\sum_{i: \operatorname{Fin}((n+1))} ((t(i) \cdot B(i))))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\sum_{i: \operatorname{Fin}((n+1))} ((t(i) \cdot B(i)))))))) \implies (\lvert (p(\sum_{i: \operatorname{Fin}((n+1))} ((t(i) \cdot B(i))))-\sum_{i: \operatorname{Fin}((n+1))} ((t(i) \cdot p(B(i))))) \rvert  \leq (((3 \cdot (\operatorname{real}(n)+1))-1) \cdot \varepsilon)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_finite_sum_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n+1 effects with real weights in the closed unit interval and an effect-valued weighted total, the weighted error is at most (3*(n+1)-1)*epsilon, with n interpreted in the reals.

**Theorem 1.10 (weighted fintype error).**

$$\forall (d: \mathbb{N}), (\forall (J: \operatorname{Type}()), ([\operatorname{Fintype}(J)] ([\operatorname{Nonempty}(J)] (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (((0 \leq \varepsilon) \land ((\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (0 \leq p(E)))) \land (\forall (E: \operatorname{Mat}(d)), (\forall (F: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land ((\operatorname{PosSemidef}((E+F))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(E+F)))))) \implies (\lvert ((p((E+F))-p(E))-p(F)) \rvert  \leq \varepsilon)))) \land (p(\operatorname{Id}(d)) = 1))) \implies (\forall (B: J \to \operatorname{Mat}(d)), (\forall (t: J \to \mathbb{R}), (((\forall (i: J), ((\operatorname{PosSemidef}(B(i))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-B(i)))))) \land (\forall (i: J), ((0 \leq t(i)) \land (t(i) \leq 1))) \land ((\operatorname{PosSemidef}(\sum_{i: J} ((t(i) \cdot B(i))))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\sum_{i: J} ((t(i) \cdot B(i)))))))) \implies (\lvert (p(\sum_{i: J} ((t(i) \cdot B(i))))-\sum_{i: J} ((t(i) \cdot p(B(i))))) \rvert  \leq (((3 \cdot \operatorname{real}(\operatorname{card}(J)))-1) \cdot \varepsilon)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_fintype_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same weighted estimate holds for every nonempty finite index type, including zero coefficients, with constant 3*card(I)-1 and all displayed effect, weight and total conditions preserved.

**Theorem 1.11 (finite positive family error).**

$$\forall (d: \mathbb{N}), (\forall (J: \operatorname{Type}()), ([\operatorname{Fintype}(J)] ([\operatorname{Nonempty}(J)] (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (\varepsilon: \mathbb{R}), (\forall (K: \mathbb{R}), (((0 \leq \varepsilon) \land (1 \leq K) \land ((\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (0 \leq p(E)))) \land (\forall (E: \operatorname{Mat}(d)), (\forall (F: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}(F)) \land ((\operatorname{PosSemidef}((E+F))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(E+F)))))) \implies (\lvert ((p((E+F))-p(E))-p(F)) \rvert  \leq \varepsilon)))) \land (p(\operatorname{Id}(d)) = 1))) \implies (\forall (B: J \to \operatorname{Mat}(d)), (\forall (c: J \to \mathbb{R}), (((\forall (i: J), ((\operatorname{PosSemidef}(B(i))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-B(i)))))) \land (\sum_{i: J} (B(i)) \leq (K \cdot \operatorname{Id}(d))) \land (\forall (i: J), (\lvert c(i) \rvert  \leq K))) \implies (\forall (E: \operatorname{Mat}(d)), ((((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \land (E = \sum_{i: J} ((c(i) \cdot B(i))))) \implies (\lvert (p(E)-\sum_{i: J} ((c(i) \cdot p(B(i))))) \rvert  \leq (((K)^{2} \cdot ((6 \cdot \operatorname{real}(\operatorname{card}(J)))+1)) \cdot \varepsilon))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_positive_family_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural matrix dimension and nonempty finite index type I, any effect family with sum at most K times the identity and signed real coefficients of absolute value at most K represents each specified effect E with probability error at most K^2*(6*card(I)+1)*epsilon. The premises require K>=1 and epsilon>=0 and the actual equality for E; the dimension need not be positive in this general helper.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.IsEffect`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.Mat`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.bounded_interval_stability`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.cstar_effect_bridge`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_homogeneity`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.effect_iff_order`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_positive_family_error`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.finite_sum_error`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.probability_bounds`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_finite_sum_error`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectAdditivityStability.weighted_fintype_error`
- Dependency: [D5/S3/Quantum/Foundation/EffectProbabilityExtension](EffectProbabilityExtension.md)
