# Local enclosures of the fixed whole-line high vectors

Keep the exact dyadic $B$, $H=H_{1024,64}EB$ and $Z=QH$ from
[high-trials.md](high-trials.md). This supplier evaluates those vectors
at local real points, using the [coherent root](strip-root.md) and
[continuous sinc projection](continuous-projection.md). Classical
Bessel, Fourier, convolution and Poisson formulas are reused; no new
general method, originality or Lean certification is claimed.

The retained forward action uses its specified finite Gamma sum. Its
definition does not change to the full digamma action used in the old
[uncertified screen](common-matrix-screen.md).

## Exact inputs and finite action

The published Legendre integral
[DLMF 10.54.2](https://dlmf.nist.gov/10.54.E2) gives

$$
p_j(x)=\sqrt{\frac{64(2j+1)}\pi}\,
 j_j(32x)\cos(32x+j\pi/2),\quad 0\le j\le94,
$$

where $j_j$ is the spherical Bessel function. The program evaluates
$j_{94},j_{95}$ through
$j_j(z)=z^j\,{}_0F_1(j+3/2;-z^2/4)/(2j+1)!!$ and reuses the
[published recurrence](https://dlmf.nist.gov/10.51.E1) downward. At
$x=0$, only $p_0(0)=\sqrt{64/\pi}$ is nonzero. The four inputs are
the same exact $EB$, evaluated with directed arithmetic.

For $a_k=2k+1/2$, $J=1024$, the finite symbol is

$$
m_J(\xi)=\operatorname{Re}\psi(1/4+i\xi/2)-\psi(1/4)
 +\psi(J+1/4)-\operatorname{Re}\psi(J+1/4+i\xi/2).
\tag{LH1}
$$

Here $\psi$ is the digamma function. Use
$c_\Gamma=\psi(1/4)-\log\pi$, both prime directions for every retained
prime power through64, and the real mean of $v_0EB$. Prime shifts
evaluate the inputs directly at $x\pm\log n$; they use no interpolation.
The finite mean sum and multiplier DFT are approximations whose errors
are paid below, not new definitions of $H$.

## Periodic multiplier and physical sample allowances

Let $h=1/256$, $R=128$, $X=4$, $\delta=1/8$,
$\Delta=2\pi/R$ and $\nu=\pi/h$. All local action outputs in this
step are lattice points with $|x|\le X$. For $f=sEBa$, strip transport
gives its nonunitary Fourier bound

$$
\left|\int f(x)e^{-i\xi x}dx\right|
\le B_\delta e^{64\delta}F_Be^{-\delta|\xi|}\|a\|.
$$

On periodic frequencies, the DFT folds $\xi+2\pi q/h$ to its finite
representative. Since $0\le m_J\le M_J$, the difference of multiplier
values costs at most $M_J$. Its complete folded-mode pointwise error is

$$
\frac{2M_J}R B_\delta e^{64\delta}F_B
\frac{e^{-\delta\nu}}{1-e^{-\delta\Delta}}\|a\|. \tag{LH2}
$$

For the physical core, the summed wrapped kernels obey

$$
\sum_{k\ge0,n\ne0}e^{-a_k|x-y+nR|}
\le W_R:=\frac{2e^{-(R-2X)/2}}
 {(1-e^{-R/2})(1-e^{-2(R-2X)})},\quad |x|,|y|\le X.
$$

Because $\|sEBa\|_1\le B_\delta F_B\|a\|$, the core wrap costs
$W_RB_\delta F_B\|a\|$. Use the real (CP5) envelope with
$b=\pi/2$, $U_X=e^{2X}$ and $C_s$ as there. The physical and omitted
lattice $L^1$ mass of $f$ is bounded by

$$
J_f=C_s\sqrt{64/\pi}F_Be^{-bU_X}
                  (U_X/b+1/b^2).
$$

For every real argument, the periodic exponential kernel is bounded
by $\coth(a_kR/2)\le\coth(R/4)<2$. This gives $2JJ_f$ for the tail
wrap. Local periodization of the $M_Jf$ term costs $M_JJ_f/h$ at
lattice outputs. Deleting full-periodization samples from the DFT
costs another $M_JJ_f/h$, since each discrete convolution matrix
entry has absolute value at most $M_J$. The complete physical allowance
is therefore $(2M_J/h+2J)J_f\|a\|$.

The mean integrand has horizontal-line $L^1$ norm at most
$V_\delta e^{64\delta}F_B\|a\|$. Its trapezoid error is
$2V_\delta e^{64\delta}F_Be^{-2\pi\delta/h}/(1-e^{-2\pi\delta/h})$,
and its omitted physical/lattice mean tail is bounded by
$\sqrt{64/\pi}F_B\,2C_se^{-bU_X}(U_X/b+1/b^2)$.
Multiply their sum by $c\|v_0\|_\infty$, using
$\|v_0\|_\infty\le2C_s(2/b)^2e^{-2}$.

The Gamma allowances multiply by the real $A_0$ for the outer $s$.
Their combination with the mean allowance is below
$5.847\cdot10^{-23}$ on the same coefficient unit ball. Numerical
DFT, special-function, mean and direct-shift errors are already in
their directed column balls; they are not replaced by this analytic
constant.

## Continuous projection and saved data

The producer feeds enlarged $H$ column balls into the physical sinc
convolution with the actual cutoff64, then adds (CP4) and (CP8).
Outside the core, the real (CP6) envelope bounds $H$ by a zero-centered
ball. This gives local $Z=H-PH$ column enclosures through $|x|\le33/4$.
It does not already evaluate off-lattice $Z$ prime shifts.

[local-high-input-samples.json](local-high-input-samples.json) retains
all1025 nonnegative $H$ and $PH$ rows in the physical core, as exact
lower and upper dyadic endpoints. Evenness supplies the negative rows.
These reusable enclosures permit later scalar integrals without
recomputing the forward solver. The [producer](local_high_samples.py)
also saves parameter/source hashes and representative local $Z$ values
in [local-high-result.json](local-high-result.json).

At192 bits, the saved maximum local column radius is below
$2.056\cdot10^{-19}$. It is a maximum column radius, not a joint
operator error: a four-column pointwise error combines as
$\sqrt{\sum_a r_a(x)^2}$, potentially twice the maximum.

The [localized Gram supplier](local-z-gram.md) consumes the core data.
Whole-line $CZ$, off-lattice high outputs, action/cross blocks, complete
common residual Gram, projected-ground direction, restricted Schur
sign, cofinal positivity, Robin and RH remain separate obligations.

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/local_high_samples.py
```

The project-authored program uses python-flint/FLINT and copies no
third-party implementation code. Its optional precision and output
paths do not alter the specified mathematical vectors.
