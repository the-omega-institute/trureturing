# Actual Robin kernel diagonal scalar

The [producer](robin_kernel_diagonal.py) and
[directed scalar data](robin-kernel-diagonal.json) supply the actual parameter
in FIB §398's same-source high-moment and diagonal-limit identities. They
do not execute the existing inverse-prefix, PNT or prime-panel producers.

For $q=(3-\sqrt5)/2$, $\beta_n=\log(1-(-q)^n)$ and
$\mathcal B(s)=\sum_n\beta_n n^{-s}$, the supplied scalar is

$$
c_{\mathrm{diag}}=
\frac{\mathcal B'(1)^2}{\mathcal B(1)^3}
-\frac{\mathcal B''(1)}{2\mathcal B(1)^2}
+\frac{\gamma_1}{\mathcal B(1)}.
$$

The complete directed enclosure verifies

$$
-\frac{13}{1000}<c_{\mathrm{diag}}<-\frac{12}{1000},
\qquad c_{\mathrm{diag}}\approx-0.01245369410060373105.
$$

Every omitted Binet term is paid. Using $|\beta_n|\le q^n/(1-q)$
and $\log n\le n$, a retained head through $N$ has the three tail
allowances

$$
\begin{aligned}
|B-B_N|&\le\frac{q^{N+1}}{(N+1)(1-q)^2},\\
|B'-B_N'|&\le\frac{q^{N+1}}{(1-q)^2},\\
|B''-B_N''|&\le
\frac{q^{N+1}[(N+1)-Nq]}{(1-q)^3}.
\end{aligned}
$$

The last allowance uses $(\log n)^2/n\le n$. The signed heads
receive two-sided outward radii before the rational expression is formed.
The Stieltjes input uses [FLINT's `acb.stieltjes`](https://flintlib.org/doc/acb.html)
at $a=1$; the sign convention is checked against the first coefficient
of the deflated zeta series. These two interfaces provide a convention
comparison, not a claim of independent numerical algorithms.
The standard convention is
$\zeta(1+z)=1/z+\gamma-\gamma_1z+O(z^2)$; see
[DLMF §25.2.4](https://dlmf.nist.gov/25.2.E4).

The paper derivation in
[FIB §398](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#398-真实积分尾权重的低商显式核同源有符号尾与对角负号)
connects this scalar to
$\int_1^\infty R(y)y^{-2}dy-D$ and
$m^2\log m\,J_m(m)$. The scalar enclosure alone does not prove those
analytic identities. They remain without complete Lean verification.
No explicit threshold for the eventual diagonal negative sign is
certified here, and the fixed-$x$ asymptotic is not asserted uniformly
in $x$.

## Reproduction and limits

The retained result uses 64 Binet terms and 192 bits with the runtime
reported in the JSON:

```sh
uv run --offline --no-project --python 3.13 --with python-flint==0.9.0 python docs/reports/fib-robin-boundary/robin_kernel_diagonal.py --output /tmp/robin-kernel-diagonal.json
```

The entry accepts the head length, precision and output path. A runtime
for the declared offline command must be installed or cached. The entry was
exercised on macOS arm64 from a different working directory, with spaces in
the producer and output paths and a disabled login shell, using 16 terms and
128 bits; other platforms were not exercised. Exact
dyadic endpoints, the producer hash and the complete tail allowances are
retained. The computation provides no numerical bound on $C_H$, no
sign for the complete $\sum_m H_mJ_x(m)$, and no RH or full Robin proof.
