# Original Delannoy Matrix Square

## Abstract

Upper-circle phase crossings construct distinct roots of the original Delannoy matrix-square rows.

Mao and Wang, The Narayana transformation, arXiv:2607.01572v1, Conjecture 4.1 asks for real nonpositive roots of A squared and D squared. Only the original D squared clause is selected here. The all-degree complex-root assertion remains unproved in this module.

Step words use east, north and northeast. Their endpoint sums count east and north with weight one and northeast with weight two. The finite set paths(n) contains exactly the words ending at a point whose coordinate sum is n. Filtering by the second coordinate k therefore counts paths to (n-k,k), and there are no entries above the diagonal. squareEntry(n,k) is the sum of D(n,j)D(j,k) over k <= j <= n. squareRow(n) uses precisely these product coefficients.

**Theorem 1.1 (Path Correspondence, Divided Difference and Endpoint Exclusion).**

Lean statement: `D5/S1/Recurrence/Algebraic/DelannoySquareRoots.source_correspondence`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DelannoySquareRoots.source_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jianxi Mao and Lijie Wang (2026). *The Narayana transformation*. URL: <https://arxiv.org/abs/2607.01572v1>.

*Commentary.*

The disjoint east, north and northeast path images give the ordinary-row recurrence T_(n+2)=(1+x)T_(n+1)+xT_n. Coefficient extraction yields column k as g f^k, with g=1/(1-t) and f=t(1+t)/(1-t). The actual matrix-square sum then gives F=g times T(f). Formal substitution proves [(1-t)(1-2t-t²)-xt(1+t)(1+t²)]F=1-t in the power-series ring with integer polynomial coefficients. This proves the source correspondence from actual paths rather than assuming a recurrence-only representation.

For every n, T_n(1-sqrt(2)) is nonzero. Evaluate T_n first in the integer quadratic ring at 1-sqrt(2). Mathlib's injective real embedding shows that a zero there would be a zero element of that ring. The conjugate embedding would then give T_n(1+sqrt(2))=0. Its actual recurrence has positive initial values and positive weights at 1+sqrt(2), so that evaluation is strictly positive. The quadratic-ring embedding and polynomial homomorphism laws are reused from pinned Mathlib.

For nonzero complex u and v with u+v+uv=1 and yuv=1, the theorem proves y(v-u)(-1)^n G_n(-y) = T_n(-u)/u^(n+1)-T_n(-v)/v^(n+1) for every n. The series whose coefficients are T_n(-u)/u^(n+1) is the reciprocal of q_u=t²+(u-1)t+u. The transformed source denominator factors as y q_u q_v. Subtracting the two reciprocal series and extracting coefficients gives the original squared-row identity. Its multiplied form permits u=v; division by v-u requires distinctness.

**Theorem 1.2 (Distinct Roots from the Upper Circle).**

Lean statement: `D5/S1/Recurrence/Algebraic/DelannoySquareRoots.upper_circle_roots`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/DelannoySquareRoots.upper_circle_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jianxi Mao and Lijie Wang (2026). *The Narayana transformation*. URL: <https://arxiv.org/abs/2607.01572v1>.

*Commentary.*

For every degree n, the theorem constructs n distinct positive ordinary-row zeros z_i and proves T_n(-w)=(-1)^n product_i(w-z_i) over the complex numbers. Each z_i differs from sqrt(2)-1. The scaled Chebyshev-U recurrence and its pinned root formula supply these factors inside the proof. If N counts the z_i above sqrt(2)-1, an injective family of N actual squared-row roots has the form -y_i, where 3-2 sqrt(2) < y_i < 3+2 sqrt(2).

Write u(phi)=-1+sqrt(2)(cos(phi)+i sin(phi)). On the closed upper arc, u and all u-z_i are nonzero. Their arguments equal arccos of the real part divided by the norm, so the argument functions are continuous even at the negative real endpoint. The continuous phase sum_i arg(u-z_i)-(n+1)arg(u) has endpoint values N pi and -pi. The intermediate value theorem gives one interior crossing for each j pi, 0 <= j < N. Distinct levels force distinct crossing parameters; no phase monotonicity is used.

The polar factorization makes T_n(-u)/u^(n+1) real at every crossing. The circle identity gives v=conjugate(u), u+v+uv=1 and yuv=1 for y=1/(3-2 sqrt(2) cos(phi)). The multiplied divided difference then gives G_n(-y)=0. The imaginary part of u is strictly positive in the interior, so the factor v-u can be cancelled. Strict decrease of cosine makes the y parameters injective and places them in the stated open interval. These are roots of the actual path-count matrix square, with no root-count premise.

For P_n(y)=(-1)^n G_n(-y), the formal bridge factors the source denominator into two quadratics indexed by u and v=(1-u)/(1+u), where y=1/(uv). A divided difference connects P_n to the ordinary rows. The upper circle supplies N=n-k distinct roots, where k counts ordinary zeros below sqrt(2)-1. The disjoint real Chebyshev sign intervals still have to supply k-1 further roots when k is positive. That complementary count, the original row degree and factor closure, and coefficient positivity remain unformalized obligations. No simplicity, interlacing, higher-power or Eulerian claim follows from the source bridge.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/DelannoySquareRoots.source_correspondence`
- Truth anchor: `D5/S1/Recurrence/Algebraic/DelannoySquareRoots.upper_circle_roots`
