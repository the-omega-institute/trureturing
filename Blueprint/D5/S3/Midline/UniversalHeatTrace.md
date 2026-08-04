# The Universal Heat-Trace Midline

## Abstract

The abscissa of a nonnegative heat trace canonically determines its l2, resonance, and half-density midline.

**Theorem 1.1 (Heat coefficients have the half-abscissa boundary).**

$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M:A\to\mathbb{R},\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\\ \forall\sigma\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\sigma M(a)})\Leftrightarrow\alpha<\sigma\\ \Rightarrow\quad \operatorname{MemLp}(a\mapsto e^{-sM(a)},2)\Leftrightarrow\frac{\alpha}{2}<\Re(s). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.heat_coefficient_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The abscissa alpha is characterized by the displayed summability equivalence; it is not constructed in this module. Squaring coordinate norms doubles the real parameter, so square summability begins exactly to the right of alpha over two.

**Theorem 1.2 (Norm square is the vertical-invariant heat trace).**

$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\\ \forall\rho\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\rho M(a)})\Leftrightarrow\alpha<\rho,\quad \frac{\alpha}{2}<\sigma\\ \Rightarrow\quad \left\Vert\mathbf{Z}_{M}(\sigma+it)\right\Vert^{2}=D_M(2\sigma)=\sum_{a\in A}e^{-2\sigma M(a)}. \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.heat_vector_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every vertical parameter t, the squared lp norm is the same heat trace at twice sigma. Thus imaginary translation changes phases but not the norm.

**Theorem 1.3 (The source pairing is the heat kernel).**

$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\\ \forall\rho\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\rho M(a)})\Leftrightarrow\alpha<\rho,\quad \frac{\alpha}{2}<\Re(s),\ \frac{\alpha}{2}<\Re(w)\\ \Rightarrow\quad \left\langle\mathbf{Z}_{M}(s),\mathbf{Z}_{M}(w)\right\rangle=D_M(s+\overline{w}). \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.heat_vector_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source-ordered inner product is the heat trace at s plus conjugate w. In this module resonance names the affine equation s plus conjugate w equals alpha; it does not assert meromorphic continuation or the existence of a pole.

**Theorem 1.4 (Resonance and half-density select the same midline).**

$$\begin{gathered} A\ \text{countable},\ 0\in A,\ M:A\to\mathbb{R},\ M(0)=0,\ (\forall a,\ 0\le M(a)),\ (\exists a,\ M(a)\neq0),\ 0<\alpha,\\ \forall\sigma\in\mathbb{R},\ \operatorname{Summable}(a\mapsto e^{-\sigma M(a)})\Leftrightarrow\alpha<\sigma\\ \Rightarrow\quad \left[\operatorname{MemLp}(\mathbf{Z}_{M}(s),2)\Leftrightarrow\frac{\alpha}{2}<\Re(s)\right],\\ \left[s+\overline{s}=\alpha\Leftrightarrow\Re(s)=\frac{\alpha}{2}\right],\\ \left[(\forall a,\ |e^{\alpha M(a)/2}e^{-sM(a)}|=1)\Leftrightarrow\Re(s)=\frac{\alpha}{2}\right]. \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-summability boundary, self-resonance line, and coordinatewise unit-modulus half-density line all equal alpha over two. This free triple coincidence uses no functional equation. The companion resonance theorem also derives the unique partner w = alpha - conjugate s and proves that this partner map is an involution.

**Theorem 1.5 (Reflection center equals the abscissa).**

$$\forall\alpha,c\in\mathbb{R},\quad \left[\forall s\in\mathbb{C},\ s=c-\overline{s}\Leftrightarrow\Re(s)=\frac{\alpha}{2}\right]\Leftrightarrow c=\alpha.$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.reflection_center_eq_abscissa_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A separately supplied reflection s maps to c minus conjugate s has the universal heat-trace midline as its fixed line exactly when its center c is the heat-trace abscissa alpha.
