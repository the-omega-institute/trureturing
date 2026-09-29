# Single-Peak Log-Likelihood Covariances

## Abstract

Uniformly started paths of the single-peak kernel have explicit one-step moments, finite-range log-likelihood covariances, and an exact path-sum variance.

**Definition 1.1 (Even log-likelihood mean function).**

$$\forall u \in \mathbb {R}, \operatorname {phi}(u) = \frac{(1+u) \log (1+u)+(1-u) \log (1-u)}{2}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function phi is the even weighted logarithmic mean associated with a signed transition bias u.

**Definition 1.2 (Odd weighted log-likelihood function).**

$$\forall u \in \mathbb {R}, \operatorname {xi}(u) = \frac{(1+u) \log (1+u)-(1-u) \log (1-u)}{2}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.xi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function xi is the odd part of the same weighted logarithmic expression.

**Definition 1.3 (Even log-likelihood second-moment function).**

$$\forall u \in \mathbb {R}, \operatorname {psi}(u) = \frac{(1+u) \log (1+u)^{{2}}+(1-u) \log (1-u)^{{2}}}{2}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function psi is the even weighted second moment of the logarithmic increment.

**Definition 1.4 (Uniform-start path weight).**

$$\forall X: Type, \operatorname {Fintype}(X), P: X \to X \to \mathbb {R}, s \in \mathbb {N}, x: \operatorname {Fin}(s+1) \to X, \operatorname {pathWeight}(P, s, x) = \frac{1}{\lvert X \rvert } \prod _{t \in \operatorname {Fin}(s)} \operatorname {P}(x_{t}, x_{t+1})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A path of s transitions starts with mass one over the cardinality of X and is weighted by the product of its transition factors.

**Definition 1.5 (Finite-path expectation).**

$$\forall X: Type, \operatorname {Fintype}(X), P: X \to X \to \mathbb {R}, s \in \mathbb {N}, f: (\operatorname {Fin}(s+1) \to X) \to \mathbb {R}, \operatorname {pathExpectation}(P, s, f) = \sum _{x \in \operatorname {Fin}(s+1) \to X} \operatorname {pathWeight}(P, s, x) \operatorname {f}(x)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathExpectation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Expectation is the explicit finite sum of a path observable against the uniform-start path weight.

**Definition 1.6 (Single-step log-likelihood increment).**

$$\forall X: Type, \operatorname {Fintype}(X), chi: X \to \mathbb {R}, z: X, r, q \in \mathbb {R}, s \in \mathbb {N}, t \in \operatorname {Fin}(s), x: \operatorname {Fin}(s+1) \to X, \operatorname {logIncrement}(chi, z, r, q, t, x) = \log (\lvert X \rvert \operatorname {kernel}(chi, z, r, q, \lvert X \rvert , x_{t}, x_{t+1}))$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.logIncrement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time t, the increment is the logarithm of the state-space cardinality times the single-peak transition weight along that edge.

**Definition 1.7 (Finite-path covariance).**

$$\forall X: Type, \operatorname {Fintype}(X), P: X \to X \to \mathbb {R}, s \in \mathbb {N}, f, g \in (\operatorname {Fin}(s+1) \to X) \to \mathbb {R}, \operatorname {pathCovariance}(P, s, f, g) = \operatorname {pathExpectation}(P, s, f g)-\operatorname {pathExpectation}(P, s, f) \operatorname {pathExpectation}(P, s, g)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The covariance of two path observables is their product expectation minus the product of their expectations.

**Definition 1.8 (Finite-path variance).**

$$\forall X: Type, \operatorname {Fintype}(X), P: X \to X \to \mathbb {R}, s \in \mathbb {N}, f: (\operatorname {Fin}(s+1) \to X) \to \mathbb {R}, \operatorname {pathVariance}(P, s, f) = \operatorname {pathCovariance}(P, s, f, f)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The variance of a path observable is its covariance with itself.

**Definition 1.9 (Finite log-likelihood sum).**

$$\forall X: Type, \operatorname {Fintype}(X), chi: X \to \mathbb {R}, z: X, r, q \in \mathbb {R}, s \in \mathbb {N}, x: \operatorname {Fin}(s+1) \to X, \operatorname {logLikelihoodSum}(chi, z, r, q, s, x) = \sum _{t \in \operatorname {Fin}(s)} \operatorname {logIncrement}(chi, z, r, q, t, x)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.logLikelihoodSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite log-likelihood sum adds the increments over all edges of the path.

**Theorem 1.10 (Exact single-peak log-likelihood covariances).**

$$\begin {aligned}&\forall X: Type, \operatorname {Fintype}(X), chi: X \to \mathbb {R}, z: X, r, q \in \mathbb {R}, M \in \mathbb {N},\\ &(\forall x \in X, \operatorname {chi}(x) = 1 \lor \operatorname {chi}(x) = -1) \land \operatorname {chi}(z) = 1 \land 0 < r \land r < 1,\\ &\lvert X \rvert  = 2 M \land \lvert \{x \in X: \operatorname {chi}(x) = 1\} \rvert  = M \land 2 \leq M \land q = \frac{r}{M-1} \Rightarrow \\ &let P = \operatorname {kernel}(chi, z, r, q, \lvert X \rvert ); let \operatorname {L}(x, y) = \log (\lvert X \rvert \operatorname {P}(x, y)); \\ &let k = M-1; let I = \frac{\operatorname {phi}(r)+k \operatorname {phi}(q)}{\lvert X \rvert }; \\ &let J = \frac{\operatorname {xi}(r)-k \operatorname {xi}(q)}{\lvert X \rvert }; let v = \frac{\operatorname {psi}(r)+k \operatorname {psi}(q)}{\lvert X \rvert }-I^{{2}}; \\ &let \ell _{t} = \log (\lvert X \rvert \operatorname {P}(x_{t}, x_{t+1})); (\forall x \in X, \sum _{y \in X} \operatorname {P}(x, y) \operatorname {L}(x, y) = \operatorname {phi}(\operatorname {profile}(chi, z, r, q, x))) \land \\ &(\forall y \in X, \sum _{x \in X} \operatorname {P}(x, y) \operatorname {L}(x, y) = I+J \operatorname {chi}(y)) \land \\ &(\forall n \in \mathbb {N}, \operatorname {pathExpectation}(P, n+1, \ell _{n}) = I) \land \\ &\operatorname {pathCovariance}(P, 2, \ell _{0}, \ell _{1}) = I J \land \\ &(\forall j \in \mathbb {N}, 2 \leq j \Rightarrow \operatorname {pathCovariance}(P, j+1, \ell _{0}, \ell _{j}) = 0) \land \\ &\forall s \in \mathbb {N}, 1 \leq s \Rightarrow \operatorname {pathVariance}(P, s, \sum _{t \in \operatorname {Fin}(s)} \ell _{t}) = s v+2 (s-1) I J\end {aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.exact_single_peak_log_likelihood_covariances` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite sign space of cardinality 2M, with exactly M positive signs and a distinguished positive state z. Assume M is at least two, 0 < r < 1, and q = r/(M - 1). The outgoing conditional mean is phi of the local profile, while the incoming conditional mean is I + J chi(y).

Under the explicit uniform-start path weights, the edge at every time n has mean I. The adjacent covariance is I J, every covariance at lag at least two is zero, and the variance of the sum over s edges is s v + 2(s - 1) I J for s at least one.

The lag cutoff follows from the two-step transition identity: after two transitions, the endpoint is uniform independently of the starting state. The variance then accumulates one-edge second moments and the single adjacent covariance.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.exact_single_peak_log_likelihood_covariances`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.logIncrement`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.logLikelihoodSum`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathCovariance`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathExpectation`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathVariance`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.pathWeight`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.phi`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.psi`
- Truth anchor: `D5/S3/Estimation/TimeArrow/SinglePeakLogLikelihoodCovariance.xi`
- Dependency: [D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent](SinglePeakPathCurrent.md)
