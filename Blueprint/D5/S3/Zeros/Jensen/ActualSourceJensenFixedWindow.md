# Actual source Jensen fixed window

The normalized entire function is
`sourceF(z)=cosineSquareTransform(sourceThetaDensity,z)`. The raw half-line
function is `rawF(z)=cosineSquareTransform(sourceThetaKernel,z)/2`. Their
relation is `sourceF=(2/fullZ)*rawF`, with `fullZ>0`. The finite polynomial is
`sourcePolynomial n=(sourceP n).map(Real→Complex).comp(C(-1)*X)`; at real `t`
its value is `originalJ n t`. Its parameter derivative is `fullD`, and

```text
fullD(n,t) = -sourceP(n)'(-t),
(2n+1) fullG(n,t) = 2n fullD(n,t) - fullM2(n,t)/2.
```

For every `T>0`, the target supplies `n0` such that, for every `n>=n0` and
**every actual node** satisfying `0<t<=T` and `originalJ n t=0`,

```text
fullD(n,t)*fullG(n,t) >= fullD(n,t)^2/2 > 0.
```

The threshold depends on `T`. At each such node `D` and `G` are nonzero.
Writing `ell=(n+1)/n`, the adjacent parameter derivative is
`HasDerivAt(originalJ(n+1),G,ell*t)`, its value is `t*G/n`, and that value is
nonzero. The zero of `sourceQ n` at `1/t` is simple and has a nonzero simple
cofactor. For `xi=n/(n+1)/t` and `q=sourceQ(n+1)`, the exact consequences are

```text
xi>0,
q'(xi)=0,
(n+1)q(xi)=xi^n G,
xi^2 q''(xi)=-n xi^n D,
q(xi) q''(xi)=-(n/(n+1))*xi^(2n-2)*D*G,
q(xi) != 0, q''(xi) != 0,
sourceCoupling(n+1,xi)*D^2=(xi^2/n)*(D*G)>0.
```

Thus `xi` is a critical point of the adjacent polynomial. The simple zero
belongs to degree `n` at `1/t`.

For every `t0>0` with `sourceF(t0)=0`, every exact finite order `m>=1`, and
**every original isolating radius** `delta>0`, the target supplies `C,d>0` and
`N` such that every `n>=N` has `m` injectively indexed positive real nodes
`nodes:Fin m→Real`. Every node lies strictly in the original disk, is an actual
`originalJ n` zero, and is a simple `sourcePolynomial n` zero. For every index,

```text
|nodes(i)-t0| <= C/sqrt(n),
|fullD(n,nodes(i))| >= d/(sqrt(n))^(m-1),
|fullM2(n,nodes(i))| <= n*|fullD(n,nodes(i))|.
```

The original disk has no boundary roots and contains exactly `m` complex root
occurrences. More precisely, its filtered polynomial root multiset equals the
multiset map of all indices `Fin m` under `i↦nodes(i)`. Each value occurs once,
and every node has a nonzero polynomial cofactor. The signed inequality and
all adjacent/reflected consequences above apply at **each `nodes(i)` for that
same degree `n`**.

The coefficient construction separates `e0(j)=1` from
`e(r+1,j+1)=e(r+1,j)+j*e(r,j)`. Its falling-factorial representation uses
simultaneous induction over every `r`, and its top correction coefficient uses
the vanishing coefficient above support. The residual includes both `j<=n`
and `j>n`, with all derivative orders requiring a summable majorant on a
larger open disk. The separately quantified order-zero function estimate is
needed for `h=-4z*sourceF''-2sourceF'`; when `m>=2`, its order is `m-2`.

The disk comparison uses an analytic unit on the whole original disk,
a principal-log boundary primitive for `P/sourceF`, and integration of the
polynomial root multiset with repetitions. Local Taylor estimates use
`sigma=min(delta/2,t0/2,1)`; boundary estimates use
`Rdisk=max(1,t0+delta)`. These radii have different purposes. The caller's
`delta` is retained exactly in the count and occurrence equality.

The target assumes neither RH, simplicity of limiting zeros, global Jensen
hyperbolicity, a preselected actual root list, nor an error or count bound.
The all-degree, growing-window, global signed comparison and RH conclusions
remain outside this fixed-window statement.
