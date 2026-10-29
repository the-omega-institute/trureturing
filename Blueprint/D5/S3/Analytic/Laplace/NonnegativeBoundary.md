# Nonnegative exponential transforms

## Abstract

A positive measure supported on the nonnegative real axis has a singularity at a finite boundary of exponential integrability.

**Theorem 1.1 (Holomorphic extension and exponential integrability).**

Lean statement: `D5/S3/Analytic/Laplace/NonnegativeBoundary.integrable_exp_of_holomorphic_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/NonnegativeBoundary.integrable_exp_of_holomorphic_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu be a measure on the real line supported on the nonnegative axis. Suppose t lies in the interior of the interval where exp(t*x) is integrable. Let F be holomorphic on the complex ball of radius r about t and agree near t with the exponential transform integral exp(z*x) dmu(x). For every h with 0<=h<r, exp((t+h)*x) is integrable. The Taylor coefficients at t are the moments integral x^n*exp(t*x) dmu(x) divided by n factorial. These moments are nonnegative. Taylor convergence at t+h and the monotone interchange of the nonnegative exponential series with integration give the asserted integrability.

**Theorem 1.2 (Continuation along the real ray).**

Lean statement: `D5/S3/Analytic/Laplace/NonnegativeBoundary.integrable_exp_on_real_ray`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/NonnegativeBoundary.integrable_exp_on_real_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu be a measure supported on the nonnegative real axis and suppose its exponential integral converges at some real parameter. Let U be open and contain every real t<a, and let F be holomorphic on U. Suppose F agrees locally with the defining transform at every t<a in the interior of the interval of exponential integrability. Then exp(t*x) is integrable for every t<a. If one such parameter failed, positivity makes the convergence interval downward closed with finite supremum c<a. A ball about c contained in U and the preceding Taylor argument give integrability strictly to the right of c, a contradiction.

**Theorem 1.3 (A singularity at the convergence boundary).**

Lean statement: `D5/S3/Analytic/Laplace/NonnegativeBoundary.nonnegative_exponential_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/NonnegativeBoundary.nonnegative_exponential_boundary` (`✓ std3`). ∎

*Citation.* David Vernon Widder (1941). *The Laplace Transform*. DOI: [10.1515/9781400876457](https://doi.org/10.1515/9781400876457).

*Commentary.*

Let mu be a measure on the nonnegative real axis and c a finite real number. Assume exp(t*x) is integrable for every t<c and is not integrable for any t>c. There is no positive radius r and holomorphic F on the ball about c of radius r which agrees with the exponential transform on the part of that ball with Re(z)<c. Indeed choose t=c-r/4. Taylor convergence on the ball about t of radius r/2 implies integrability at t+r/3>c, contradicting the convergence boundary. Replacing z by -s gives the corresponding nonnegative Laplace-transform theorem at its finite abscissa of convergence. This formulation uses a general positive measure, extending Widder's nonnegative locally integrable function formulation.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/NonnegativeBoundary.integrable_exp_of_holomorphic_extension`
- Truth anchor: `D5/S3/Analytic/Laplace/NonnegativeBoundary.integrable_exp_on_real_ray`
- Truth anchor: `D5/S3/Analytic/Laplace/NonnegativeBoundary.nonnegative_exponential_boundary`
