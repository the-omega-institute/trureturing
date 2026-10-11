# Foucart–Liao Chebyshev-Center Regularization Refutation

## Abstract

A real Chebyshev center need not minimize any positively weighted quadratic regularization objective.

**Definition 1.1 (Model and measurement constraints).**

$$f \in \operatorname{feasible}\left(P, \Lambda, y, \varepsilon, \mathrm{eta}\right) \Leftrightarrow ((\Vert P\left(f\right)\Vert \le \varepsilon) \land (\Vert y - \Lambda\left(f\right)\Vert \le \mathrm{eta}))$$

*Formalization.* `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.feasible` (`✓ std3`).

*Citation.* Simon Foucart; Chunyang Liao (2024). *S-Procedure Relaxation: a Case of Exactness Involving Chebyshev Centers*. DOI: [10.1007/978-3-031-66497-7_1](https://doi.org/10.1007/978-3-031-66497-7_1). URL: <https://arxiv.org/abs/2310.09677v1>.

*Commentary.*

For linear P:ℝⁿ→ℝⁿ and Λ:ℝⁿ→ℝᵐ, data y∈ℝᵐ and bounds ε,η∈ℝ, the feasible set consists of f with ‖Pf‖≤ε and ‖y−Λf‖≤η. The norms are Euclidean. Section 5 uses Q=Id and equal bounds ε=η; the counterexample also has equal bounds.

**Definition 1.2 (Comparison with every enclosing bound).**

$$\operatorname{IsChebyshevCenter}\left(C, c\right) \Leftrightarrow (\forall c': E, \forall M: \mathbb{R}, (\forall f: E, (f \in C) \Rightarrow (\Vert f - c'\Vert \le M)) \Rightarrow (\forall f: E, (f \in C) \Rightarrow (\Vert f - c\Vert \le M)))$$

*Formalization.* `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.IsChebyshevCenter` (`✓ std3`).

*Citation.* Simon Foucart; Chunyang Liao (2024). *S-Procedure Relaxation: a Case of Exactness Involving Chebyshev Centers*. DOI: [10.1007/978-3-031-66497-7_1](https://doi.org/10.1007/978-3-031-66497-7_1). URL: <https://arxiv.org/abs/2310.09677v1>.

*Commentary.*

In a normed additive commutative group E, c is a Chebyshev center of C when every uniform real distance bound for every competing center c′ also bounds distances from c. For the nonempty bounded Euclidean feasible sets in the assertion, this expresses minimization of the worst-case reconstruction distance.

**Definition 1.3 (Quadratic regularization).**

$$\operatorname{IsRegularizer}\left(P, \Lambda, y, \tau, c\right) \Leftrightarrow (\forall f: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right), (1 - \tau) \cdot \Vert P\left(c\right)\Vert^{2} + \tau \cdot \Vert y - \Lambda\left(c\right)\Vert^{2} \le (1 - \tau) \cdot \Vert P\left(f\right)\Vert^{2} + \tau \cdot \Vert y - \Lambda\left(f\right)\Vert^{2})$$

*Formalization.* `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.IsRegularizer` (`✓ std3`).

*Citation.* Simon Foucart; Chunyang Liao (2024). *S-Procedure Relaxation: a Case of Exactness Involving Chebyshev Centers*. DOI: [10.1007/978-3-031-66497-7_1](https://doi.org/10.1007/978-3-031-66497-7_1). URL: <https://arxiv.org/abs/2310.09677v1>.

*Commentary.*

The predicate states global minimization over all f∈ℝⁿ of (1−τ)‖Pf‖²+τ‖y−Λf‖², as in equation (8). The predicate itself allows any real τ; the assertion requires 0<τ<1.

**Definition 1.4 (Every real center is a regularizer).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, \forall m: \mathbb{N}, \forall P: \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)\right), \forall \Lambda: \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right), \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)\right), \forall y: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right), \forall \varepsilon: \mathbb{R}, \forall \mathrm{eta}: \mathbb{R}, (0 < \varepsilon) \Rightarrow ((0 < \mathrm{eta}) \Rightarrow ((\operatorname{Nonempty}\left(\operatorname{feasible}\left(P, \Lambda, y, \varepsilon, \mathrm{eta}\right)\right)) \Rightarrow ((\operatorname{IsBounded}\left(\operatorname{feasible}\left(P, \Lambda, y, \varepsilon, \mathrm{eta}\right)\right)) \Rightarrow (\forall c: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right), (\operatorname{IsChebyshevCenter}\left(\operatorname{feasible}\left(P, \Lambda, y, \varepsilon, \mathrm{eta}\right), c\right)) \Rightarrow (\exists \tau: \mathbb{R}, ((0 < \tau) \land (\tau < 1)) \land (\operatorname{IsRegularizer}\left(P, \Lambda, y, \tau, c\right))))))))$$

*Formalization.* `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.claim` (`✓ std3`).

*Citation.* Simon Foucart; Chunyang Liao (2024). *S-Procedure Relaxation: a Case of Exactness Involving Chebyshev Centers*. DOI: [10.1007/978-3-031-66497-7_1](https://doi.org/10.1007/978-3-031-66497-7_1). URL: <https://arxiv.org/abs/2310.09677v1>.

*Commentary.*

Section 5, Question 2, asks verbatim: “Is the Chebyshev center always obtained via regularization?” The authors explain: “From [10], we know that the answer is affirmative under the specific conditions mentioned above, since the Chebyshev center equals the regularizer f_{τ♯} with parameter τ♯∈(0,1) satisfying the implicit equation (9). Without the specific conditions, we also know from [8] that the answer is affirmative if one considered the complex setting rather than the real setting.” The specific conditions are that P is an orthogonal projector and ΛΛ*=Idₘ. The displayed assertion quantifies over finite-dimensional real Euclidean spaces and arbitrary linear P and Λ, positive bounds ε,η, and every center of each nonempty bounded feasible set. The example uses ε=η=1 and an orthogonal projector, so the negation also addresses the source's equal-bound setting.

**Theorem 1.5 (A center outside every regularization parameter).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.result` (`✓ std3`). ∎

*Resolves.* `Problems/foucart-liao-2024-chebyshev-center-regularization` (refuted) by `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"foucart-liao-2024-chebyshev-center-regularization","declaration_gid":"D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Simon Foucart; Chunyang Liao (2024). *S-Procedure Relaxation: a Case of Exactness Involving Chebyshev Centers*. DOI: [10.1007/978-3-031-66497-7_1](https://doi.org/10.1007/978-3-031-66497-7_1). URL: <https://arxiv.org/abs/2310.09677v1>.

*Commentary.*

Take H=ℝ², P=diag(1,0), Λ(x,z)=((x−z)/2,z), y=(1,0) and ε=η=1. The map P is an orthogonal projector and Λ is invertible, while ΛΛ* has rows (1/2,−1/2) and (−1/2,1), so ΛΛ*≠Id₂. The feasible set is x²≤1 and g=(x−z−2)²+4z²−4≤0. For c*=(3/5,−1/5), put q=(x−3/5)²+(z+1/5)²−4/5. The identity 10(4−x+z)q=(x−1)(4−x+7z)²+(17−11x+2z)g, with 4−x+z>0 and 17−11x+2z≥0 on the feasible set, proves q≤0. The feasible contact points A=(1,3/5), B=(−1/5,−3/5), D=(1,−1) have weights 5/12,1/3,1/4 and satisfy (5/12)‖A−c‖²+(1/3)‖B−c‖²+(1/4)‖D−c‖²=4/5+‖c−c*‖². Consequently c* is the unique center and its radius is √(4/5). The comparator v=(3/5,−7/25) has ‖Pv‖²=‖Pc*‖²=9/25 but ‖y−Λv‖²=49/125<50/125=‖y−Λc*‖². For every τ>0 the objective is smaller at v by τ/125. More generally, no objective a‖Pf‖²+b‖y−Λf‖² with b>0 has c* as a minimizer. The private lemmas feasible_coordinates, contacts and bounded establish the coordinate constraints and admissibility; containment proves the enclosing-ball bound, center_certificate uses the weighted contact identity, and not_regularizer supplies the strict comparison. The proof uses exact rational arithmetic. The radius and uniqueness follow from containment and the weighted identity; they are not separate public theorems. The conclusion concerns the real setting and does not contradict the affirmative complex result or the real result under both specific conditions. It makes no exhaustive priority claim about earlier work on intersections of two ellipsoids.

## References

- Truth anchor: `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.IsChebyshevCenter`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.IsRegularizer`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.claim`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.feasible`
- Truth anchor: `D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.result`
