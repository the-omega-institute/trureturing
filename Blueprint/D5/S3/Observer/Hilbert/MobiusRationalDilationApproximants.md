# Finite Mobius rational-dilation approximants

## Abstract

Finite rational Mobius dilations have exact squared error equal to the reciprocal coefficient energy.

Let mu(k) be the integer arithmetic Moebius function. muQ and muR are its rational and real casts. Every finite coefficient and every dilation parameter n/(j+1) is formed in Q before applying the canonical embedding into R. All integrals below use Lebesgue volume; (0,1) denotes the open unit interval. The natural indices include zero, and a sum over an empty range is zero.

**Definition 1.1 (The literal rational dictionary).**

$$\forall \alpha\in \mathbb{Q},\forall u\in \mathbb{R},\operatorname{phi}\left(\alpha, u\right)=\frac{\operatorname{fract}\left(\alpha u\right)-u}{u}$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fractional part is Int.fract, and alpha is rational. Division is Lean's total real division, so this definition also assigns a value at u=0. Pointwise identities used below impose 0<u<1.

**Definition 1.2 (Rational finite Moebius coefficients).**

$$\forall n\in \mathbb{N}, \operatorname{m}\left(n\right)=\sum_{0\le j< n}\frac{\operatorname{mu}\left(j+1\right)}{j+1}$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.m` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

m(n) is the rational sum of mu(k)/k for 1<=k<=n. In particular m(1)=1.

**Definition 1.3 (Finite rational dilations).**

$$\forall n\in \mathbb{N}, \forall u\in \mathbb{R},\operatorname{H}\left(n, u\right)=\sum_{0\le j< n}\operatorname{mu}\left(j+1\right)\operatorname{phi}\left(\frac{n}{j+1}, u\right)$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H(n,u) uses exactly the rational parameters n/(j+1), weighted by the real Moebius coefficients. No real-parameter closure is used.

**Definition 1.4 (Half-open reciprocal blocks).**

$$\forall n\in \mathbb{N}, \forall u\in \mathbb{R},\operatorname{e}\left(n, u\right)=\frac{1}{u}\mathbf{1}_{\left[\frac{1}{n+1},\frac{1}{n}\right)}(u)$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.e` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

e(n,u) is u inverse times the indicator of [1/(n+1),1/n). The left endpoint is included and the right endpoint excluded. Its definition is total for n=0; the block identities assume n>=1.

**Definition 1.5 (Rational coefficient energy).**

$$\forall N\in \mathbb{N}, \operatorname{S}\left(N\right)=\sum_{0\le j< N}\operatorname{m}\left(j+1\right)^{2}$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S(N) is rational and sums the squares of m(1) through m(N). A displayed real identity uses its canonical real cast.

**Definition 1.6 (The normalized finite approximant).**

$$\forall N\in \mathbb{N}, \forall u\in \mathbb{R},\operatorname{F}\left(N, u\right)=\frac{1}{\operatorname{S}\left(N\right)}\sum_{0\le j< N}\operatorname{m}\left(j+1\right)(\operatorname{H}\left(j+2, u\right)-\operatorname{H}\left(j+1, u\right))$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F is defined for every natural N and real u. The theorems about its error assume N>=1, which makes S(N) strictly positive.

**Definition 1.7 (The literal finite floor sum).**

$$\forall n\in \mathbb{N}, \forall u\in \mathbb{R},\operatorname{floorMoebiusSum}\left(n, u\right)=\sum_{0\le j< n}\operatorname{mu}\left(j+1\right)\lfloor\frac{n}{j+1}u\rfloor$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.floorMoebiusSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The floor is Int.floor, cast to R after evaluation. The dilation n/(j+1) is still formed in Q before coercion.

**Definition 1.8 (The threshold indicator).**

$$\forall n\in \mathbb{N}, \forall u\in \mathbb{R},\operatorname{indicatorThreshold}\left(n, u\right)=\mathbf{1}_{[1,\infty)}(nu)$$

*Formalization.* `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.indicatorThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

indicatorThreshold(n,u) is 1 when 1<=n*u and 0 otherwise.

**Theorem 1.9 (The finite floor bridge).**

$$\forall n\in \mathbb{N}, 0<n\Rightarrow\forall u\in (0,1), \operatorname{floorMoebiusSum}\left(n, u\right)=\operatorname{indicatorThreshold}\left(n, u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.floor_moebius_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural n and every real u in (0,1), the finite floor sum equals the exact threshold indicator. The arithmetic input is the existing MoebiusLogarithmic floor_cancellation identity at the real cutoff n*u. Converting the rational floors to natural division and removing zero terms above floor(n*u) supplies the bridge.

**Theorem 1.10 (The exact block recurrence).**

$$\forall n\in \mathbb{N}, 1\le n\Rightarrow \forall u\in (0,1), \operatorname{H}\left(n+1, u\right)-\operatorname{H}\left(n, u\right)=\operatorname{m}\left(n\right)-\operatorname{e}\left(n, u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.h_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n>=1 and u in (0,1), H(n+1,u)-H(n,u)=m(n)-e(n,u). Subtracting the two threshold indicators gives precisely the half-open block, including the n=1 boundary.

**Theorem 1.11 (Each block has squared integral one).**

$$\forall n\in \mathbb{N}, 1\le n\Rightarrow \int_{(0,1)}\operatorname{e}\left(n, u\right)^{2} du=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.block_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n>=1, integrating u to the power -2 over [1/(n+1),1/n) gives 1. Its support lies in (0,1), and changing an endpoint does not change the Lebesgue integral.

**Theorem 1.12 (Distinct blocks are orthogonal).**

$$\forall p\in \mathbb{N}, \forall n\in \mathbb{N}, 1\le p\Rightarrow 1\le n\Rightarrow p\neq n\Rightarrow\int_{(0,1)}\operatorname{e}\left(p, u\right)\operatorname{e}\left(n, u\right) du=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.block_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every two distinct positive natural indices, the half-open supports are disjoint. Their product vanishes at every real u, so its integral is zero.

**Theorem 1.13 (Strict positivity of the energy).**

$$\forall N\in \mathbb{N}, 1\le N\Rightarrow 0< \operatorname{S}\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.s_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N>=1, the nonnegative square sum contains m(1)^2=1. The theorem states positivity of the real cast of S(N).

**Theorem 1.14 (Integrability of the squared error).**

$$\forall N\in \mathbb{N}, 1\le N\Rightarrow \operatorname{Integrable}\left((u\mapsto (1-\operatorname{F}\left(N, u\right))^{2}), \operatorname{volume}\left(\right)\mid(0,1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.error_sq_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N>=1, u |-> (1-F(N,u))^2 is integrable for volume restricted to (0,1), exactly IntegrableOn in Lean. On this interval, 1-F(N,u) is S(N) inverse times the sum of m(j+1)e(j+1,u). Disjointness eliminates the cross terms; each remaining squared block has compact support away from zero.

**Theorem 1.15 (The exact finite squared error).**

$$\forall N\in \mathbb{N}, 1\le N\Rightarrow \int_{(0,1)}(1-\operatorname{F}\left(N, u\right))^{2} du=\frac{1}{\operatorname{S}\left(N\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.finite_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N>=1, the squared error integral is exactly 1/S(N). The recurrence expresses the error as a finite weighted block sum. Disjoint supports and the unit squared integrals reduce its integral to S(N)^(-2) times S(N). This is a finite identity; no convergence or Riemann-hypothesis conclusion is asserted.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.F`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.H`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.S`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.block_integral`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.block_orthogonality`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.e`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.error_sq_integrable`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.finite_error`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.floorMoebiusSum`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.floor_moebius_bridge`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.h_step`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.indicatorThreshold`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.m`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.phi`
- Truth anchor: `D5/S3/Observer/Hilbert/MobiusRationalDilationApproximants.s_pos`
- Dependency: [D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound](../../Arith/MoebiusLogarithmic/ReciprocalBound.md)
