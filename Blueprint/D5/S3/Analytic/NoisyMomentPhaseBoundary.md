# Noisy Moment Phase Boundary

## Abstract

Assuming every nonconstant dual coefficient is nonzero, every feasible exterior mass satisfies the affine noisy-moment bound, whose equality case has a unique probability pair.

**Theorem 1.1 (Affine bound and exact equality classification).**

$$\begin{gathered}1 \le N, (\forall i, k, i \neq k \Rightarrow x_{i} \neq x_{k}), (\forall i, y \neq x_{i}),\\{}\ell_{i} = \operatorname{Lagrange}\left(x, i\right), c_{i} = \operatorname{eval}\left(\ell_{i}, y\right), p = \operatorname{interpolate}\left(x, 1_{{c_{i} > 0}}\right),\\{}P = \operatorname{p}\left(y\right), L = \sum_{k < N} \operatorname{if}\left(k = 0, 0, \lvert p_{k} \rvert\right),\\{}d_{k} = \operatorname{if}\left(k = 0, 0, \operatorname{if}\left(0 \le p_{k}, 1, -1\right)\right), r_{i} = \sum_{k < N} d_{k}[\ell_{i}]_{k},\\{}e_{k} = w y^{k} + \sum_{i} u_{i} x_{i}^{k} - \sum_{i} v_{i} x_{i}^{k}, \Delta = 1 + \varepsilon L - wP,\\{}A_{i} = \frac{Pr_{i}}{c_{i}} - L, b_{i} = w_{\varepsilon}c_{i} - \varepsilon r_{i}, w_{\varepsilon} = \frac{1 + \varepsilon L}{P},\\{}\operatorname{Feas}\left(\varepsilon, w, u, v\right) \Leftrightarrow (0 \le w \land (\forall i, 0 \le u_{i}) \land (\forall i, 0 \le v_{i}) \land w + \sum_{i} u_{i} = 1 \land \sum_{i} v_{i} = 1 \land (\forall k<N, \lvert e_{k} \rvert \le \varepsilon)),\\{}(\forall k, k < N \Rightarrow k \neq 0 \Rightarrow p_{k} \neq 0) \land 0 \le \varepsilon \longrightarrow \\{}(\forall w, u, v, \operatorname{Feas}\left(\varepsilon, w, u, v\right) \Rightarrow (0 \le \Delta \land (\forall i, 0 \le u_{i} \operatorname{p}\left(x_{i}\right)) \land (\forall i, 0 \le v_{i} (1 - \operatorname{p}\left(x_{i}\right))) \land (\forall k, k < N \Rightarrow 0 \le \operatorname{if}\left(k = 0, 0, \varepsilon \lvert p_{k} \rvert\right) - p_{k} e_{k}) \land \Delta = \sum_{i} u_{i} \operatorname{p}\left(x_{i}\right) + \sum_{i} v_{i} (1 - \operatorname{p}\left(x_{i}\right)) + \sum_{k < N} (\operatorname{if}\left(k = 0, 0, \varepsilon \lvert p_{k} \rvert\right) - p_{k} e_{k}))) \land \\{}(\forall u, v, \operatorname{Feas}\left(\varepsilon, w_{\varepsilon}, u, v\right) \Leftrightarrow ((\forall i, \varepsilon A_{i} \le 1) \land u = (i \mapsto \max(-b_{i}, 0)) \land v = (i \mapsto \max(b_{i}, 0)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct real nodes and an off-node point, the Lagrange 0/1 dual polynomial determines P, the coefficient cost L, the signed perturbation r, and transition slopes A_i=P*r_i/c_i-L. Feas_epsilon(w,u,v) abbreviates exactly the normalized nonnegative weights and all-moment error bounds displayed in the theorem formula. Assuming every nonconstant dual coefficient is nonzero, every such feasible triple has a nonnegative dual gap 1+epsilon*L-w*P, equal to the sum of its nodal and nonconstant noisy-coordinate slacks; in particular, w*P is at most 1+epsilon*L. At w=(1+epsilon*L)/P, feasibility holds exactly when every epsilon*A_i is at most one and the two probability weights are the computed positive and negative parts. The equality decomposition forces each nonconstant noisy moment to saturate and then forces every nodal weight, while the converse construction verifies normalization and all moments. Equality at a transition constraint is included. The result classifies attainment of this affine bound; it makes no assertion about later optimal phases or zero dual coefficients.

## References

- Truth anchor: `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](GoldenTomography/FinitePronyHankelReconstruction.md)
