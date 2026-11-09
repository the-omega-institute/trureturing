# Uniform four-point precision on a logarithmic cusp window

## Abstract

A uniform four-point real precision criterion, with arbitrary positive consecutive gaps and both positive endpoint terms.

**Definition 1.1 (Logarithmic envelope).**

$$\forall t \in \mathbb{R},\; \operatorname{L}\left(t\right) = \operatorname{Real.log}\left(\frac{\operatorname{Real.exp}\left(1\right)}{t}\right)$$

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(t)=log(exp(1)/t). Every use of logarithm identities in the proofs has t>0. The scale t*L(t)^2 tends to zero at the right endpoint 0.

**Definition 1.2 (Concavity deficit).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{psi}\left(v, a, b\right) = v\left(a\right) + v\left(b\right) - v\left(a + b\right)$$

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

psi(v,a,b)=v(a)+v(b)-v(a+b), for an arbitrary real function v and arbitrary real a,b. Positivity is proved later for positive arguments in the controlled window.

**Definition 1.3 (Mixed increment).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall r \in \mathbb{R},\; \operatorname{interaction}\left(v, p, q, r\right) = v\left(p + q\right) + v\left(q + r\right) - v\left(q\right) - v\left(p + q + r\right)$$

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.interaction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

interaction(v,p,q,r)=v(p+q)+v(q+r)-v(q)-v(p+q+r). Its lower bounds come from the actual differential inequality g(t)>=1/(4*t), rather than a desired cofactor premise.

**Definition 1.4 (Both positive endpoint terms).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall r \in \mathbb{R},\; \operatorname{weight}\left(v, p, q, r\right) = \operatorname{interaction}\left(v, p, q, r\right) + \frac{\operatorname{psi}\left(v, p, q\right) \cdot \operatorname{psi}\left(v, q, r\right)}{v\left(q\right)}$$

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

weight(v,p,q,r) is interaction(v,p,q,r)+psi(v,p,q)*psi(v,q,r)/v(q). Both summands remain in every endpoint estimate. Dropping the quotient loses control of extreme ratios.

**Definition 1.5 (Raw local analytic control).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall h \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall delta \in \mathbb{R},\; \operatorname{CuspControl}\left(v, h, g, delta\right) \Leftrightarrow \left(\left(\left(\left(\left(\left(\left(0 < delta \land delta \le \operatorname{Real.exp}\left(-1\right)\right) \land v\left(0\right) = 0\right) \land \operatorname{Continuous}\left(v\right)\right) \land \left(\forall t \in \operatorname{Set.Ioc}\left(0, delta\right),\; \operatorname{HasDerivAt}\left(v, h\left(t\right), t\right)\right)\right) \land \left(\forall t \in \operatorname{Set.Ioc}\left(0, delta\right),\; \operatorname{HasDerivAt}\left(h, -g\left(t\right), t\right)\right)\right) \land \operatorname{ContinuousOn}\left(g, \operatorname{Set.Ioc}\left(0, delta\right)\right)\right) \land \left(\forall t \in \operatorname{Set.Ioc}\left(0, delta\right),\; \left(\left(0 < h\left(t\right) \land h\left(t\right) \le \operatorname{Real.log}\left(\frac{1}{t}\right)\right) \land \frac{1}{4 \cdot t} \le g\left(t\right)\right) \land g\left(t\right) \le \frac{1}{t}\right)\right)$$

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.CuspControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CuspControl(v,h,g,delta) requires 0<delta<=exp(-1), v(0)=0, global continuity of v, v'=h and h'=-g at every 0<t<=delta, continuity of g on this half-open window, h>0, h<=log(1/t), and 1/(4*t)<=g<=1/t. No inverse entry, Schur sign, or deficit-ratio monotonicity is assumed. Global continuity is stronger than needed away from this window but is paid by the actual K.

**Theorem 1.6 (All three gap regimes).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall h \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall delta \in \mathbb{R},\; \operatorname{CuspControl}\left(v, h, g, delta\right) \Rightarrow \left(\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall r \in \mathbb{R},\; \left(\left(\left(0 < p \land 0 < q\right) \land 0 < r\right) \land p + q + r \le delta\right) \Rightarrow v\left(p\right) \cdot v\left(r\right) \le 64 \cdot \left(1 + \operatorname{Real.log}\left(3\right)\right)^{2} \cdot \left(p + q + r\right) \cdot \operatorname{L}\left(p + q + r\right)^{2} \cdot \operatorname{weight}\left(v, p, q, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.uniform_outer_deficit_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under CuspControl and p,q,r>0 with s=p+q+r<=delta, v(p)*v(r)<=64*(1+log(3))^2*s*L(s)^2*weight(v,p,q,r). By reflection assume p<=r. The three exhaustive regimes are q>=r>=p, r>=p>=q, and r>=q>=p. The three regime estimates retain the logarithmic variables and positive-denominator cancellations in each regime. They prove log(1+z)>=(1+log(z))/2 for z>=1 and log(1+exp(y)/2)>=(1+y)/3 for y>=0. The largest gap m satisfies s/3<=m<=s, which gives the final factor (1+log(3))^2. There is no separation-ratio cutoff and no finite-sample argument.

**Theorem 1.7 (Exact integrals at the singular corner).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall h \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall delta \in \mathbb{R},\; \operatorname{CuspControl}\left(v, h, g, delta\right) \Rightarrow \left(\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall r \in \mathbb{R},\; \left(\left(\left(0 < p \land 0 < q\right) \land 0 < r\right) \land p + q + r \le delta\right) \Rightarrow \left(\left(\left(\operatorname{IntervalIntegrable}\left((\lambda u \mapsto \int_{0}^{q}g\left(u + w\right) dw), \operatorname{volume}, 0, p\right) \land \operatorname{psi}\left(v, p, q\right) = \int_{0}^{p}\int_{0}^{q}g\left(u + w\right) dw du\right) \land \operatorname{IntervalIntegrable}\left((\lambda u \mapsto \int_{0}^{r}g\left(q + u + w\right) dw), \operatorname{volume}, 0, p\right)\right) \land \operatorname{interaction}\left(v, p, q, r\right) = \int_{0}^{p}\int_{0}^{r}g\left(q + u + w\right) dw du\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.deficit_integrals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both outer integrands are interval integrable. The first iterated integral equals psi(v,p,q); the shifted one equals interaction(v,p,q,r). For u>0 the inner integral is h(u)-h(u+q), or h(q+u)-h(q+u+r), by the ordinary fundamental theorem. At u=0 the inner singular integral is irrelevant on a singleton of measure zero. The outer improper endpoint is justified by 0<h(u)<=log(1/u), integrability of the logarithm, and continuity of v at 0. No continuity of h at 0 is assumed. The quantitative lower estimates in uniform_outer_deficit_bound use the equivalent derivative-comparison argument, with the same primitive h+log(t)/4.

**Theorem 1.8 (Restrict complex coefficients to real ones).**

$$\forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \operatorname{Matrix.PosDef}\left(\operatorname{Matrix.map}\left(A, \operatorname{Complex.ofReal}\right)\right) \Rightarrow \operatorname{Matrix.PosDef}\left(A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.real_posDef_of_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, positivity of the entrywise complex cast of a real Fin(n) matrix implies real Matrix.PosDef. Hermitian symmetry is read through Complex.re; the positive quadratic form is evaluated on the embedded real coefficient vector. This pays the actual supplier's complex-to-real boundary explicitly.

**Definition 1.9 (Two-point conditioning).**

$$\forall k \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall e \in \mathbb{R},\; \forall f \in \mathbb{R},\; \operatorname{schurCross}\left(k, d, a, b, c, e, f\right) = f - \frac{k \cdot \left(a \cdot c + b \cdot e\right) - d \cdot \left(a \cdot e + b \cdot c\right)}{k^{2} - d^{2}}$$

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.schurCross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

schurCross(k,d,a,b,c,e,f)=f-[k*(a*c+b*e)-d*(a*e+b*c)]/(k^2-d^2). Division is the total real field division. Positive definiteness and the scalar window estimates provide nonzero positive denominators at every sign use.

**Theorem 1.10 (Literal finite inverse formula).**

$$\forall k \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall e \in \mathbb{R},\; \forall f \in \mathbb{R},\; \operatorname{schurCross}\left(k, d, a, b, c, e, f\right) = f - \left(!![a,b] \cdot !![k,d;d,k]^{-1} \cdot !![c;e]\right)\left(0, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.schurCross_eq_matrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar expression equals f minus the row [a,b], the real inverse of [[k,d],[d,k]], and the column [c,e]. This identity uses the actual pinned Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two, and Matrix.det_fin_two. It holds also for a singular conditioning matrix because both inverses use the same total definition.

**Definition 1.11 (Ordered covariance matrix).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall k \in \mathbb{R},\; \forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall r \in \mathbb{R},\; \operatorname{gapGram}\left(v, k, p, q, r\right) = !![k,k - v\left(p\right),k - v\left(p + q\right),k - v\left(p + q + r\right);k - v\left(p\right),k,k - v\left(q\right),k - v\left(q + r\right);k - v\left(p + q\right),k - v\left(q\right),k,k - v\left(r\right);k - v\left(p + q + r\right),k - v\left(q + r\right),k - v\left(r\right),k]$$

*Formalization.* `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.gapGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gapGram(v,k,p,q,r) is the displayed symmetric real 4 by 4 matrix. Its diagonal is exactly k. For v(0)=0 it is the Gram matrix on 0,p,p+q,p+q+r of the even kernel t -> k-v(abs(t)).

**Theorem 1.12 (One endpoint window for all ratios).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall h \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall delta0 \in \mathbb{R},\; \forall k \in \mathbb{R},\; \left(\operatorname{CuspControl}\left(v, h, g, delta0\right) \land 0 < k\right) \Rightarrow \left(\exists delta \in \mathbb{R},\; \left(0 < delta \land delta \le delta0\right) \land \left(\forall p \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall r \in \mathbb{R},\; \left(\left(\left(0 < p \land 0 < q\right) \land 0 < r\right) \land p + q + r \le delta\right) \Rightarrow 0 < \operatorname{schurCross}\left(k, k - v\left(q\right), k - v\left(p\right), k - v\left(p + q\right), k - v\left(q + r\right), k - v\left(r\right), k - v\left(p + q + r\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.exists_uniform_endpoint_cross_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CuspControl and k>0 produce one smaller delta>0 giving a strictly positive endpoint Schur cross for every positive p,q,r with total at most delta. Put P=v(p), Q=v(q), R=v(r), alpha=psi(v,p,q), beta=psi(v,q,r), D=P-alpha, E=R-beta and I=interaction(v,p,q,r). The exact private identity is (2*k-Q)*C=(2*k-Q)*I+k*alpha*beta/Q-(P*R+D*E). Since Q<k, I>0, and 0<D<P and 0<E<R, it bounds the cross below by k*weight-2*P*R. The uniform estimate and t*L(t)^2 -> 0 finish it. The choice uses an eventual bound on the entire interval, so the same delta covers all totals below it.

**Theorem 1.13 (Weighted-ratio monotonicity).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall h \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall delta \in \mathbb{R},\; \forall p \in \mathbb{R},\; \left(\left(\operatorname{CuspControl}\left(v, h, g, delta\right) \land 0 < p\right) \land \operatorname{StrictConvexOn}\left(\mathbb{R}, \operatorname{Set.Ioo}\left(0, delta\right), \operatorname{Function.comp}\left(\operatorname{Real.log}, h\right)\right)\right) \Rightarrow \operatorname{StrictAntiOn}\left((\lambda t \mapsto \frac{\operatorname{psi}\left(v, p, t\right)}{v\left(t\right)}), \operatorname{Set.Ioc}\left(0, delta - p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.strictAntiOn_deficit_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict convexity of log(h) on (0,delta) makes h(p+u)/h(u) strictly increasing on 0<u<=delta-p. Integrating h(p+t)*h(u)-h(t)*h(p+u)>0 over 0<u<t proves the strict sign of the quotient derivative. Both integrals are proved integrable and v(t)>0 is proved. The theorem assumes no extra monotonicity premise for psi/v.

**Theorem 1.14 (Six strict real inverse signs for all distinct nodes).**

$$\forall v \in \mathbb{R} \to \mathbb{R},\; \forall h \in \mathbb{R} \to \mathbb{R},\; \forall g \in \mathbb{R} \to \mathbb{R},\; \forall delta0 \in \mathbb{R},\; \forall k \in \mathbb{R},\; \left(\left(\left(\left(\left(\operatorname{CuspControl}\left(v, h, g, delta0\right) \land 0 < k\right) \land \left(\forall t \in \operatorname{Set.Icc}\left(0, delta0\right),\; 0 < k - v\left(t\right)\right)\right) \land \operatorname{StrictConvexOn}\left(\mathbb{R}, \operatorname{Set.Icc}\left(0, delta0\right), (\lambda t \mapsto \operatorname{Real.log}\left(k - v\left(t\right)\right))\right)\right) \land \operatorname{StrictConvexOn}\left(\mathbb{R}, \operatorname{Set.Ioo}\left(0, delta0\right), \operatorname{Function.comp}\left(\operatorname{Real.log}, h\right)\right)\right) \land \left(\forall x \in \operatorname{Fin}\left(4\right) \to \mathbb{R},\; \left(\operatorname{Function.Injective}\left(x\right) \land \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left|x\left(i\right) - x\left(j\right)\right| \le delta0\right)\right) \Rightarrow \operatorname{Matrix.PosDef}\left((\lambda i \mapsto (\lambda j \mapsto k - v\left(\left|x\left(i\right) - x\left(j\right)\right|\right)))\right)\right)\right) \Rightarrow \left(\exists delta \in \mathbb{R},\; \left(0 < delta \land delta \le delta0\right) \land \left(\forall x \in \operatorname{Fin}\left(4\right) \to \mathbb{R},\; \left(\operatorname{Function.Injective}\left(x\right) \land \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \left|x\left(i\right) - x\left(j\right)\right| \le delta\right)\right) \Rightarrow \left(\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; i \ne j \Rightarrow \left((\lambda i \mapsto (\lambda j \mapsto k - v\left(\left|x\left(i\right) - x\left(j\right)\right|\right)))^{-1}\right)\left(i, j\right) < 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.exists_uniform_four_point_precision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In addition to CuspControl, assume k>0, k-v(t)>0 on [0,delta0], strict convexity of log(k-v) on that closed interval, strict convexity of log(h) on its open interior, and real Matrix.PosDef for every injective four-node map of diameter at most delta0. Then one delta>0 works for every such four-node map: all off-diagonal real inverse entries are strictly negative. The window is chosen before the nodes, with no bound on gap ratios.

The private adjacent-pair proofs use G(x,y)=k-v(y-x)-(k-v(x))*(k-v(y))/k. For 0<x<y, G increases strictly in x and decreases strictly in y; continuity extends the comparisons to the diagonal. For the distance-two pair the exact identity is C=alpha-(Q/V)*U+(k*U/V-P)*beta/(2*k-V), with V=v(q+r) and U=psi(v,p,q+r). The first summand is positive by strictAntiOn_deficit_ratio; the second is positive by the three-point strict log-convex inequality k*U>P*V.

The endpoint theorem supplies the sixth sign. Six explicit real adjugate identities give adj(A)(i,j)=-(k^2-d^2)*C for the appropriate conditioning correlation d. Real positive definiteness supplies det(A)>0, and Matrix.inv_def turns these into strict inverse signs. Finset.orderIsoOfFin sorts any injective Fin 4 node map; Matrix.inv_submatrix_equiv transports the signs through the resulting permutation. Translation of the sorted nodes gives the three positive gaps.

The arithmetic substitution is v(t)=K(0)-K(t), h(t)=-D1(t) and g(t)=D2(t). Intersecting the derivative-control window with the positive-definite window pays every scalar and matrix hypothesis. Restricting the complex positive quadratic form to real coefficients gives the real input. The resulting conclusion concerns all four distinct nodes in one common window. An arbitrary-dimensional precision theorem remains open.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.CuspControl`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.L`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.deficit_integrals`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.exists_uniform_endpoint_cross_pos`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.exists_uniform_four_point_precision`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.gapGram`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.interaction`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.psi`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.real_posDef_of_complex`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.schurCross`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.schurCross_eq_matrix`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.strictAntiOn_deficit_ratio`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.uniform_outer_deficit_bound`
- Truth anchor: `D5/S3/Analytic/Fourier/PositiveDefinite/UniformFourPointPrecision.weight`
