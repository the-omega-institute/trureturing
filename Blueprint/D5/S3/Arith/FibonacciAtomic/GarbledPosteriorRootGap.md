# Garbled Posterior and Scalar Root Risk

## Abstract

A garbled three-class posterior has a positive proper-risk gap for every scalar root and every affine softmax head, with unrestricted real parameters.

**Theorem 1.1 (A uniform positive gap for both proper losses).**

$$\begin{aligned}\forall m \in \mathbb{N}, \forall z:\operatorname{Input}(m)\to\mathbb{R},\\\forall u,v:\operatorname{Fin}(3)\to\mathbb{R}, p := \operatorname{softmax}(z, u, v):\\\kappa \le R_{2}(p)-b \land \kappa \le R_{log}(p)-h \land\\\kappa = \frac{(\mu)^{2}(\operatorname{log}(\frac{125}{98}))^{2}}{1875} = \frac{193-132\sqrt{2}}{270000}(\operatorname{log}(\frac{125}{98}))^{2} \land 0 < \kappa.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alphabet W is the existing set of five whole windows 000, 100, 010, 101 and 001, written from low to high. Input(m) consists of m+3 independent windows, with each word having mass 5^(-(m+3)). The class is 1 when the high bit of window 0 and the low bit of window 1 are both set. When that event is absent, the class is 2 if the high bit of window 1 and the low bit of window 2 are set; otherwise the class is 0. Windows after index 2 are all retained.

Put s=sqrt(2) and mu=(11-6s)/12. The three posterior rows, in label order 0,1,2, are (5/12,s/2-1/3,mu), (7/24,5/12,7/24), and (mu,s/2-1/3,5/12). The joint mass of (x,j) is the uniform word mass times the j-th coordinate of the row selected by its class. The predictor p is the softmax of u_i z(x)+v_i.

R_2 is the joint-law expectation of the complete three-label Brier loss sum_i (p_i(x)-1[j=i])^2. Its Bayes value b is the word expectation of 1-sum_i rho_i(x)^2. R_log is the joint-law expectation of -log p_j(x), using natural logarithms. Its Bayes value h is the word expectation of -sum_i rho_i(x) log rho_i(x). These are separate risks and their own Bayes values.

No structure is imposed on z. A zero-dimensional root is included by its constant zero scalar embedding. Thus the bound covers every tree, every peak, every internal parameter choice and every tail input. Slopes and biases have no common norm bound.

The three target log-odds form a triangle whose distance from any affine line is bounded below at one entire teacher class. An interior logarithm estimate and a separate large-error case turn this separation into a squared probability error. That class has uniform mass at least 16/125. The finite Pinsker inequality transfers the same bound to logarithmic excess risk. The general softmax rank obstruction is discussed by Yang et al. in arXiv:1711.03953 and by Ganea et al. in ICML 2019; the displayed constant belongs to this specified posterior.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity](FirstRejectionCutCapacity.md)
- Dependency: [D5/S3/TotalVariation/Pinsker](../../TotalVariation/Pinsker.md)
