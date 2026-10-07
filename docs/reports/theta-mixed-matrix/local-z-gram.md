# A localized whole-line Gram block and the actual high norm

This supplier consumes the [local $H,PH$ enclosures](local-high.md)
for the same four columns $Z=QH_{1024,64}EB$. It reuses orthogonal
projection, strip transport and Poisson summation. The results are
paper-model applications with directed arithmetic, not new general
theorems or Lean certification.

## Integrate a localized factor

Orthogonality and self-adjointness of $Q$ give

$$
\langle Z_i,Z_j\rangle=\langle H_i,Z_j\rangle. \tag{LG1}
$$

The saved columns are real and even, so the integral uses
$H_i(x)Z_j(x)$ and its holomorphic polarization $H_i(z)Z_j(z)$.
Rapid strip decay of $H_i$, and the unused-margin bound on $Z_j$,
give the integrable strip-decay hypothesis of the existing Poisson
source. Both line $L^2$ norms are bounded by $D_\delta F_B$; sharp-$Q$
contraction applies to the same weighted Fourier space. The product
line $L^1$ norm is therefore at most $(D_\delta F_B)^2$.
Its infinite trapezoid error is at most

$$
q_G=2(D_\delta F_B)^2
 \frac{e^{-2\pi\delta/h}}{1-e^{-2\pi\delta/h}},
\quad \delta=1/8,\ h=1/256. \tag{LG2}
$$

For the tail, use the real saved $R_0$ bound and (CP6):

$$
\|Z_j\|_\infty\le
C_H(2/b)^2e^{-2}+\sqrt{64/\pi}\,R_0F_B=:Z_\infty,
\quad b=\pi/2.
$$

The actual finite trapezoid omits $|kh|>4$. By (CP8),

$$
h\sum_{|kh|>4}|H_i(kh)Z_j(kh)|\le Z_\infty J_X. \tag{LG3}
$$

The same coefficient bounds the continuous tail by (CP7). These are
two uses of one tail coefficient, not two errors to add to (LG2).
Directed scalar products of the retained $H$ and $H-PH$ intervals pay
sample/rounding errors without assuming independent column errors.

Rounded outward, $q_G<5.476\cdot10^{-70}$ and
$Z_\infty J_X<4.979\cdot10^{-2018}$. Exact lower/upper endpoints
for all16 entries are in [local-z-gram-result.json](local-z-gram-result.json).
All six transpose pairs overlap. The entries are approximately

$$
\begin{pmatrix}
0.984409135& 0.011016577&-0.012544714& 0.008110287\\
0.011016577& 0.991546374& 0.008910890&-0.006032946\\
-0.012544714&0.008910890&0.989251528&0.007373462\\
0.008110287&-0.006032946&0.007373462&0.994313119
\end{pmatrix}.
$$

This rounded matrix is for reading; only the saved exact interval
endpoints participate in the numerical bounds.

## Use the same Gram for the real family norm

The actual Gram $G=Z^*Z$ is Hermitian. Its operator norm is bounded by
its maximum absolute row sum, so directed entry bounds give

$$
\|Z\|\le\sqrt{\max_i\sum_j|G_{ij}|}. \tag{LG4}
$$

For $g=Qv_0$, combine this with the existing ground norm on the same
five coefficients by Cauchy–Schwarz:

$$
\|(g,Z)\|\le\sqrt{\|g\|^2+\|Z\|^2}. \tag{LG5}
$$

This does not assume the two maxima are attained at once. The
[replay program](local_z_gram.py) transports the existing ground upper
dyadic and saves these real norm bounds. They do not replace the
separate strip/derivative bounds: a small real norm alone does not
control analytic transport or an unbounded operator action.

Rounded outward, the saved data give $\|Z\|<1.0090$ and
$\|(g,Z)\|<1.00904$. These are real norms of the specified whole-line
vectors, not of the periodic vectors in the earlier screen.

The reader checks source hashes, parameters, complete ordered rows and
finite endpoint order. Correct enclosure of the original vectors is
an input premise supplied by the forward producer and paper argument;
a syntactically valid arbitrary JSON array is not thereby certified.
Replay reads the saved data and evaluates this integral without running
the forward solver or its DFTs again.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/local_z_gram.py
```

The program is project-authored and uses python-flint/FLINT. Other
generator, action and cross blocks, whole-line $CZ$, the complete common
residual Gram, exact projected-ground direction and restricted Schur
sign remain unpaid. No cofinal, Robin, RH or Lean conclusion follows
from this one block.
