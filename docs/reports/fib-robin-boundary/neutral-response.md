# Two moments and local increments do not supply the missing signed estimate

The actual Binet response kernel from FIB §§384–387 is reused. The program
reads the published inverse coefficients in `binet-inverse-tail.json`; it
does not regenerate the inverse or run the earlier numerical producers.
The two actual-input moment identities are classical partial-summation
applications. FIB §390 gives their exact centering formula and a paper
construction testing what these identities alone can control.
The unrestricted two-moment sampling obstruction in FIB §389 is reused;
this probe additionally bounds every adjacent input increment.

For a probe sequence $f$, the two homogeneous constraints are

$$
\sum_{m\ge1}\frac{f(m)}{m(m+1)}=0,
\qquad
\sum_{m\ge1}f(m)
\left(\frac{\log m}{m}-\frac{\log(m+1)}{m+1}\right)=0.
$$

The actual FIB input has second moment $-\mathcal B(1)$, rather than zero.
These probes are homogeneous perturbations preserving its two scalar
moments; they do not preserve its full arithmetic-source identity.

For each integer $J\ge2$, the paper construction uses $N=64J^3$ and
isolated quotient centers $m_j=\lfloor N/j\rfloor$, $2\le j\le J$.
Three translated discrete tents at each center cancel both moments on the
same input. Their weights also give

$$
\sup_{m\ge1}\frac{|f(m)|}{\sqrt m}\le1,
\qquad |f(m)-f(m-1)|\le1.
$$

Each pulse can be reached by precisely one divisor index, so the response is

$$
(\mathcal T_kf)(N)=\frac12\sum_{j=2}^J k(j)R_j,
\qquad R_j=\left\lfloor\frac{\sqrt{m_j}}8\right\rfloor\ge J.
$$

The paper lower bound is $K(J)/(16\sqrt J)$ after dividing by $\sqrt N$.
The already established lower estimate $k(j)\ge\mathfrak c\log j$ makes
this lower bound unbounded. This disproves a uniform transmission bound
on this restricted probe class. The input varies with $J$; no assertion
about divergence for one fixed finitely supported input follows.

The directed finite acquisitions are:

| $J$ | $N$ | $(\mathcal T_kf)(N)/\sqrt N$ |
|---:|---:|---:|
| 8 | 32,768 | 1.021401313728 |
| 34 | 2,515,456 | 4.944374777036 |
| 144 | 191,102,976 | 17.390949642898 |

The exported data contain dyadic interval endpoints for all 183 pulse
weights, both moment residuals and the responses. An interval containing
zero checks compatibility with the exact moment identities; exact zero
comes from the displayed barycentric formulas, not from a numerical
zero-containing interval. Integer quotient isolation and the geometry
certificates are exact integer comparisons.

Run from any directory with Python and `python-flint` available:

```sh
python /absolute/path/neutral_response.py --output /path/to/neutral-response.json
```

The default input path is relative to the producer, and its hash is pinned.
Cutoffs must be distinct increasing integers at least two and fit the
published coefficient prefix. Input-artifact and producer overwrite,
including hardlink overwrite, are rejected. No whole-integer grid up to
$N$ is required; the finite tents and exact quotient intervals suffice.
The numerical payload retains its completed acquisition. The current section
locator and producer hash are synchronized as metadata; the arithmetic was
not regenerated.

The program is an independently usable method probe. The paper construction
and the actual moment/centering application have not been Lean-verified.
No actual-$H$ square-root bound, Robin signed-tail estimate, RH result or
originality claim is supplied. Future arithmetic estimates must retain
relations stronger than these two moments and the bounded-increment
condition.
