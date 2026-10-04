# Original energy on the quadratic and quartic source plane

This is a conditional paper estimate with directed numerical evidence
for the [original minimal even theta form](../../../Library/Weil/fukushima2011dirichlet.md).
It reuses that realization, the original-series theta supplier,
the existing legal five-mode FIB partition and
[validated ball integration and tensor Gauss bounds](../../../Library/Analytic/johansson2018ballintegration.md).
It introduces no generic quadrature, core or spectral theorem and no
Lean certificate or originality claim.

Under those same actual-model and numerical-supplier premises, the
[saved acquisition](theta-polynomial-energy-bounds-result.json) supports

$$
D(c_1x^2+c_2x^4)-\tfrac12\operatorname{Var}_\nu(c_1x^2+c_2x^4)
\ge10^{-12}(|c_1|^2+|c_2|^2),\qquad c_1,c_2\in\mathbb C. \tag{P1}
$$

The coefficient gap is measured in this fixed monomial basis; it is
not a uniform spectral floor on all even inputs. The
[same minimal-domain cutoff argument](../../../Library/Weil/fukushima2011dirichlet.md#even-polynomials-in-the-same-minimal-form-norm)
places both inputs in the original form domain. The existing
[mixed critical-source identity](../../../Library/Weil/lagarias2004li.md)
then transports (P1), with unchanged right side, to
$h=c_0+c_1x^2+c_2x^4+n$ for any $c_0\in\mathbb C$ and $n\in N$.
This uses mixed nullity against every form-domain input; zero self-energy
alone would not pay the cross term.

## Retained energy is a lower form

Write $d\nu(x)=2\Phi(x)\cosh(x/2)dx$ and
$\psi_\Gamma(t)=e^{-t/2}/(1-e^{-2t})$. For even $h$, folding the
original Gamma energy gives exactly

$$
E_\Gamma(h)=\int_0^\infty\int_0^\infty
\Phi(r)\Phi(s)[\psi_\Gamma(|r-s|)+\psi_\Gamma(r+s)]
|h(s)-h(r)|^2\,dr\,ds.
$$

Retain only $[0,R]^2$, $R=3/2$. Symmetry reduces it to twice
$0\le r\le s\le R$. Set

$$
s=r+(R-r)t,\quad 0\le t\le1,\quad d=s-r,\quad u=s+r,
\quad b=r^2+s^2.
$$

The differences of $x^2,x^4$ are $du(1,b)$.
For their three symmetric matrix entries the transformed integrands are

$$
2(R-r)\Phi(r)\Phi(s)[u^2g(d)+d^2g(u)](1,b,b^2), \tag{P2}
$$

where the removable singularity is cancelled analytically by

$$
g(z)=z^2\psi_\Gamma(z)
=\frac{z e^{z/2}}{2\,{}_0F_1(3/2;z^2/4)}.
$$

This is the classical identity
$\sinh z/z={}_0F_1(3/2;z^2/4)$, including zero. Every joint complex
rectangle used for the Gauss estimate must enclose both Bernstein
ellipses, preserve the theta supplier's analytic contract, and exclude
zero in the denominator enclosure. No complex absolute square is used.

The existing depth-two FIB tiling partitions both $[0,R]$ and $[0,1]$
into 21 legal cells. Each product cell uses 24 validated Gauss nodes
in each variable and ellipse parameter $\rho=2$. If $M$ bounds one
holomorphic matrix integrand on the joint ellipse enclosure, the
existing tensor estimate pays an error at most

$$
(\text{cell area})M\frac{64}{15(\rho-1)\rho^{47}}. \tag{P3}
$$

The Gauss nodes and weights themselves are balls. Summed allowances
for the three entries are at most $8.661\cdot10^{-15}$,
$3.955\cdot10^{-15}$ and $2.222\cdot10^{-15}$. FIB addresses organize
the same retained integration domain; no gain over other legal tilings
or arithmetic consequence from the labels is claimed.

For a prime power $n$ put $t_n=\log n$ and use the centered coordinate
$y=x+t_n/2$. The retained prime matrix contribution is

$$
\frac{2\Lambda(n)}{\sqrt n}\int_0^R
4y^2t_n^2\Phi(y-t_n/2)\Phi(y+t_n/2)
(1,b_n,b_n^2)\,dy,\quad b_n=2y^2+t_n^2/2. \tag{P4}
$$

The factor two folds the even centered integrand. The retained set is
**every prime power at most 16**:
$2,3,4,5,7,8,9,11,13,16$.
The existing `acb.integral` supplier encloses these 30 scalar integrals.
Rejected analytic boxes return nonfinite values for subdivision;
finite output enclosures, rather than requested tolerances, supply the
bounds. All other Gamma regions, prime powers and prime integration
regions remain in the original $D$: their energy matrices are PSD.
Omitting them therefore supplies a lower form for every complex
coefficient vector simultaneously. It is not an entrywise lower bound
on every off-diagonal entry of the full matrix.

## The covariance retains the whole line

Let $m_j=\nu(x^j)$ for $j=2,4,6,8$. The **full** covariance is

$$
V=\begin{pmatrix}
m_4-m_2^2&m_6-m_2m_4\\
m_6-m_2m_4&m_8-m_4^2
\end{pmatrix}.
$$

Each moment combines a validated integral of
$4\Phi(r)\cosh(r/2)r^j$ over $[0,R]$ with a positive tail enclosure.
The [original derivative supplier](theta_translation_bounds.py)
provides $C_0$ with folded density at most
$4C_0e^{5r-\pi e^{2r}}$. The elementary bound $r^j\le e^{jr}$
and its existing exponential-integral helper give

$$
0\le\int_R^\infty r^j\,d\mu(r)
\le4C_0T_{2+j/2}(R),\qquad
T_k(R)=\frac1{2\sqrt{e^{2R}}}\int_{e^{2R}}^\infty u^ke^{-\pi u}\,du.
$$

The four tail upper bounds are below
$2.780\cdot10^{-23}$, $5.676\cdot10^{-22}$,
$1.160\cdot10^{-20}$ and $2.369\cdot10^{-19}$.
Interval products enclose the covariance, including its correlations;
no truncated variance replaces $V$.

## Directed matrix decision and its limit

Let $A$ be the retained Gamma matrix plus retained prime matrix minus
$V/2$. Its displayed entries are approximately

$$
A\approx\begin{pmatrix}
5.1402265\cdot10^{-6}&-1.52265013\cdot10^{-6}\\
-1.52265013\cdot10^{-6}&4.5105668\cdot10^{-7}
\end{pmatrix}.
$$

The decision uses the exact dyadic interval endpoints in the saved
result, not these decimal summaries or midpoint eigenvalues. For
$A-10^{-12}I$, the first principal minor exceeds $5.1402\cdot10^{-6}$
and the determinant exceeds $6.43\cdot10^{-17}$. Sylvester's criterion
therefore certifies (P1) under the named supplier premises. The positive
energy omission and complete covariance are essential to its direction.

The acquisition's `Unreviewed` scope and pending-review field are
acquisition-stage metadata, not a mathematical premise or a current
review verdict. Its source bytes and producer hash are preserved;
publication assessment belongs to this report and its delivery review.
Neither source nor result carries a Lean/kernel certificate.

The [same-form polynomial core application](../../../Library/Weil/fukushima2011dirichlet.md#even-polynomials-in-the-same-minimal-form-norm)
connects arbitrary even tests to **all** polynomial degrees. This
certificate pays only the first two nonconstant directions. It supplies
no higher-degree matrix signs, quantitative exhaustion rate or comparison
on the full remaining subspace. The original all-input half-bound,
RH and Robin remain unproved.

Reproduction from the repository root, using the existing pinned
dependencies:

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 --with numpy==2.5.3 python docs/reports/theta-mixed-matrix/theta_polynomial_energy_bounds.py --nodes 24 --output /tmp/theta-polynomial-energy-bounds-result.json
```
