# Fractional means and residual support geometry

## Abstract

A fractional logarithmic mixture lies strictly below its mean vector. When the mean variance is below the distance floor, the actual lower-corner budget determines nested positive support points.

Write f(x)=log(1-exp(-x)) for real x>0. The two-point distance v=gridDistance(a,m,c,d) is the minimum of the distances from c and d to the closed interval [a,m]. All scalar parameters below are real.

**Theorem 1.1 (Strict concavity on positive arguments).**

$$(1-\theta)\operatorname{f}\left(c\right)+\theta\operatorname{f}\left(d\right)<\operatorname{f}\left(z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.logValue_strictConcaveOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function f is strictly concave on (0,infinity). Equivalently, for every pair of distinct positive real numbers c,d and every 0<theta<1, let z=(1-theta)c+theta*d; the displayed inequality holds. The second derivative is -exp(x)/(exp(x)-1)^2<0 throughout the positive half-line, and f is continuous there.

**Theorem 1.2 (The branch whose mean variance meets the floor).**

$$(1-\theta)\operatorname{f}\left(c\right)+\theta\operatorname{f}\left(d\right)+\sum_{i \neq j}\operatorname{f}\left(\operatorname{t}\left(i\right)\right)<\sum_{i}\operatorname{f}\left(\operatorname{y}\left(i\right)\right) \le \operatorname{psiK}\left(k, m, V\right) \le \operatorname{psiK}\left(k, m, V_{0}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_mean_branch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k>=2 be a natural number, let j belong to Fin k, and let t:Fin k->R. Assume 0<c<d, 0<theta<1, and t(i)>0 for i distinct from j. Put z=(1-theta)c+theta*d, y(j)=z and y(i)=t(i) otherwise. Assume the saturated budget z+sum_{i!=j}t(i)=km. Set s=z-m, W=sum_{i!=j}(t(i)-m)^2, and V=s^2+W. For every V0 with 0<=V0<=V, the three displayed comparisons hold.

The positive vector y has mean m>0, total squared deviation V, and V<k(k-1)m^2. Its genuinely fractional row gives the first, strict comparison. The positive-coordinate envelope gives the second comparison, and variance antitonicity gives the third. The cases V=V0, V0=0, and V=V0=0 are included. No nonzero variance or distinct Hermite nodes are assumed.

**Theorem 1.3 (A residual gap forces both endpoints outside the interval).**

$$|s|<v \land c<a \land m<d \land v=\operatorname{min}\left(a-c, d-m\right) \land 0<v$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.residual_distance_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a<m and c<z<d. Let W and V0 be arbitrary real numbers, put s=z-m and v=gridDistance(a,m,c,d), and assume s^2+W<V0<=v^2+W. No sign assumption on W or the endpoints is needed for this statement.

Nonnegativity of distance and the strict squared inequality give |s|<v. An endpoint in [a,m] would make v zero. If c>=m, its distance to m is smaller than z-m; if d<=a, its distance to a is smaller than m-z. Both possibilities contradict |s|<v. Thus c<a<m<d. The nearest interval points to c and d are respectively a and m, giving v=min(a-c,d-m)>0.

**Theorem 1.4 (The lower-corner budget gives nested positive support).**

$$|s|<v \land c<a \land m<d \land v=\operatorname{min}\left(a-c, d-m\right) \land kv \le (k-1)(m-c)-s \land 0<c \le C<m-v<z<m+v=D \le d$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_residual_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k>=2 be a natural number, j in Fin k, and t:Fin k->R. Assume 0<c<d, 0<theta<1, and a<m. Put z=(1-theta)c+theta*d, s=z-m, W=sum_{i!=j}(t(i)-m)^2, and v=gridDistance(a,m,c,d). Assume z+sum_{i!=j}t(i)=km, ka<=c+sum_{i!=j}t(i), and s^2+W<V0<=v^2+W. Positivity of the other coordinates is not required by this geometric implication.

Define n=k-1, A=(kv+s)/n, C=m-A, and D=m+v. Here C and D denote the inner endpoints c' and d'. The residual distance result gives c<a<m<d, v=min(a-c,d-m)>0, and -v<s<v. The actual lower-corner budget then gives kv<=k(a-c)<=(k-1)(m-c)-s. Consequently A<=m-c and v<A, proving the full displayed support chain. These are analytic support points; no membership in the original two-point grids or feasibility as an actual corner is asserted.

**Theorem 1.5 (The exhaustive two-branch alternative).**

$$(V_{0} \le V \land (1-\theta)\operatorname{f}\left(c\right)+\theta\operatorname{f}\left(d\right)+\sum_{i \neq j}\operatorname{f}\left(\operatorname{t}\left(i\right)\right)<\sum_{i}\operatorname{f}\left(\operatorname{y}\left(i\right)\right) \le \operatorname{psiK}\left(k, m, V\right) \le \operatorname{psiK}\left(k, m, V_{0}\right)) \lor (V<V_{0} \land |s|<v \land c<a \land m<d \land v=\operatorname{min}\left(a-c, d-m\right) \land kv \le (k-1)(m-c)-s \land 0<c \le C<m-v<z<m+v=D \le d)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_branch_alternative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k>=2, j in Fin k, t:Fin k->R, 0<c<d, 0<theta<1, and a<m. Require t(i)>0 for i distinct from j. Use z=(1-theta)c+theta*d, y(j)=z and y(i)=t(i) otherwise, s=z-m, W=sum_{i!=j}(t(i)-m)^2, V=s^2+W, v=gridDistance(a,m,c,d), C=m-(kv+s)/(k-1), and D=m+v. Assume z+sum_{i!=j}t(i)=km, ka<=c+sum_{i!=j}t(i), and 0<=V0<=v^2+W.

Comparison of V0 and V gives exactly one of the displayed branches. When V0<=V, strict concavity and the moment envelope give all three objective comparisons. When V<V0, the distance and lower-corner budget give all the nested support inequalities. Equality of the two variances belongs to the first branch.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_branch_alternative`
- Truth anchor: `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_mean_branch`
- Truth anchor: `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.fractional_residual_support`
- Truth anchor: `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.logValue_strictConcaveOn`
- Truth anchor: `D5/S3/Analytic/Interpolation/FractionalBranchGeometry.residual_distance_geometry`
- Dependency: [D5/S3/Analytic/Interpolation/EnvelopeKMonotone](EnvelopeKMonotone.md)
