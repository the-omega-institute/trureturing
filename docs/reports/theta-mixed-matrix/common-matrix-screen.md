# Common high-corrector numerical screen

This program chooses explicit trials for the
[complete sharp-center residual problem](sharp-center.md). It uses the
existing inverse-residual comparison, actual theta callbacks, full mean
correction and both retained prime directions. Its floating-point results
are uncertified screens. Periodic FFT, physical truncation, frequency
quadrature and approximate ground deflation have unpaid errors, so none
of the displayed signs is a positivity certificate.

## Common family and comparison

The 95 input generators are the exact orthonormal Fourier Legendre
polynomials of degrees $0$ through $94$ on $[0,64]$, mapped by the even
cosine transform. The numerical implementation approximates their
integrals using 384 Gauss–Legendre nodes, evaluates them on $|x|\le3$
and zeroes them elsewhere. The theta callback retains six series terms.
The finite Fourier grid uses a periodic digamma action, rather than the
original whole-line operator. Every prime power through 64 is retained,
giving 27 terms; both shifts and the rank-one mean are included.

For the exact future calculation, let $K_E=KE$ and let $Z$ be one common
high trial family in $D(C)$. Choose $d_0=\delta/2$, where
$\delta=0.0383682545007734$ is the inherited complete high floor. Define

$$
\begin{aligned}
G_K&=K_E^*K_E,\\
H_Z&=(CZ-d_0Z)^*K_E,\\
J_Z&=(CZ)^*(CZ)-d_0Z^*CZ.
\end{aligned}
$$

When the actual $J_Z$ is positive definite, minimizing the existing
inverse-residual upper comparison over $Y=ZA$ gives

$$
A=J_Z^{-1}H_Z,\qquad
K_E^*C^{-1}K_E\preceq
d_0^{-1}(G_K-H_Z^*J_Z^{-1}H_Z).
$$

Only one $C$ action on each specified high trial is required. The Gram
formula does not apply $C^2$ to a trial or $T$ to an arbitrary residual.
This is a use of the existing residual comparison, rather than a new
general block theorem.

The screen diagonalizes its finite computed high-image Gram to select
four trial columns with eigenvalues above $10^{-8}$. These are numerical
choices from a known finite matrix, not an assumed eigenbasis of $C$.
It solves the common finite $J_Z A=H_Z$ system and measures the resulting
comparison. The lower comparison with $Y=0$ is also reported.

## Saved diagnostics

The [radius-32 data](common-matrix-screen-16384-32-corrected.json) and
[radius-64 data](common-matrix-screen-32768-64-corrected.json) give:

| Diagnostic | Grid 16,384, radius 32 | Grid 32,768, radius 64 |
|---|---:|---:|
| Deflated center minimum | $0.125$ | $0.125$ |
| Zero-corrector lower comparison, continuous coupling | $-1.36685414898$ | $-1.36685414898$ |
| Zero-corrector lower comparison, FFT coupling | $-1.39130842836$ | $-1.37594360380$ |
| Continuous/FFT coupling Gram difference | $0.001100272259$ | $0.000409187644$ |
| Selected high trials | 4 | 4 |
| Corrected lower comparison minimum | $0.124999994124$ | $0.124999994443$ |
| Corrector Gram minimum | $0.01431077115$ | $0.01429649211$ |

The two runs share the physical grid spacing $1/256$; the larger radius
changes the periodic interval and its Fourier spacing. The agreement
does not bound discretization error or certify convergence. Roundoff
negative minima of coupling/inverse Gram matrices are retained in the
data, not clipped to zero. The exact ground constraint is not imposed.

The negative zero-corrector allowance is an insufficient numerical lower
comparison; it is not a negative direction of the actual operator. The
positive corrected screen motivates certifying this explicit family but
does not prove a sign for the actual matrix.

## Exact trial choices and remaining obligations

The export fixes every entry of $B$ and $A$ on the exact $2^{-40}$ dyadic
grid using nearest rounding of the binary float as an exact rational.
The [trial file](common-trials.json) contains the arrays, basis definition,
selection parameters and producer hash. No spectrum or positivity is
certified by fixing the coefficients. The actual whole-line trials and
exact ground lift are defined in [high-trials.md](high-trials.md); they
differ from the periodic screening vectors, including its full-digamma
selection action. The [separate high-trial supplier](high-trial-bounds-result.json)
pays their omitted action tails using their own weighted derivatives.

The actual retained integrals, Fourier projection, Gram and residual
enclosures still need directed computation with those fixed choices.
The exact $p_0=Pv_0$ ground direction, common coefficient map and complete
mean must remain in that computation. An actual Loewner lower sign must
pay the independent $e_{94}<0.04383817677622261$ discarded-center bound.
No retained PSD, cofinal $c\uparrow1/2$, Lean, Robin or RH result follows
from this screen.

## Reproduce

```sh
uv run --no-project --python 3.13.12 --with numpy==2.3.3 --with scipy==1.16.2 --with threadpoolctl==3.6.0 python docs/reports/theta-mixed-matrix/common_matrix_screen.py --correctors
uv run --no-project --python 3.13.12 --with numpy==2.3.3 --with scipy==1.16.2 --with threadpoolctl==3.6.0 python docs/reports/theta-mixed-matrix/common_matrix_screen.py --grid 32768 --radius 64 --correctors --export-trials docs/reports/theta-mixed-matrix/common-trials.json
```

Results are written beside the program. The export destination is an
explicit path. The pinned data chooses one family; rerunning selection
may choose different signs or bases in close numerical eigenspaces.
Use the saved dyadic arrays for any subsequent directed certification.
The implementation is project-authored and uses NumPy/SciPy numerical
APIs; their packages supply dependency licensing. No third-party
certificate or implementation is copied.
