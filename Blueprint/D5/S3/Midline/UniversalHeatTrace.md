# The Universal Heat-Trace Midline

## Abstract

A genuine heat abscissa determines strict-side l2 behavior, resonance, and the half-density midline while leaving boundary convergence explicit.

**Theorem 1.1 (Heat coefficients have the half-abscissa boundary).**

$$\operatorname{MemLp}(a\mapsto e^{-sM(a)},2)\Leftrightarrow\operatorname{Summable}(a\mapsto e^{-2\Re(s)M(a)}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.heat_coefficient_mem_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Boundary behavior is extracted from the genuine abscissa definition: it prescribes convergence for sigma greater than alpha and divergence for sigma less than alpha, but says nothing at sigma equal to alpha. The flat iff in atom (i) implicitly assumes the separately named boundary-divergent convention. Squaring coordinate norms doubles the real parameter; the general theorem gives the exact summability criterion and the two strict-side implications.

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

$$\begin{gathered} \operatorname{IsHeatAbscissa}(M,\alpha)\\ \Rightarrow [\operatorname{MemLp}(\mathbf{Z}_{M}(s),2)\Leftrightarrow\operatorname{Summable}(a\mapsto e^{-2\Re(s)M(a)})],\\ [\Re(s)>\alpha/2\Rightarrow\operatorname{MemLp}(\mathbf{Z}_{M}(s),2)],\quad[\Re(s)<\alpha/2\Rightarrow\neg\operatorname{MemLp}(\mathbf{Z}_{M}(s),2)],\\ [s+\overline{s}=\alpha\Leftrightarrow\Re(s)=\alpha/2],\quad[(\forall a,|e^{\alpha M(a)/2}e^{-sM(a)}|=1)\Leftrightarrow\Re(s)=\alpha/2]. \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general theorem leaves equality at the boundary open. Self-resonance and coordinatewise unit modulus still select alpha over two and do not use boundary behavior. The companion resonance theorem also derives the unique partner w = alpha - conjugate s and proves that this partner map is an involution.

**Theorem 1.5 (Boundary divergence restores the flat iff).**

$$\operatorname{BoundaryDivergentAbscissa}(M,\alpha)\Rightarrow[\operatorname{MemLp}(\mathbf{Z}_{M}(s),2)\Leftrightarrow\alpha/2<\Re(s)].$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline_of_boundary_divergent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the explicitly stronger class required by the original atom (i). Boundary behavior has not been folded into the genuine abscissa predicate; the strict flat iff is recovered only after boundary divergence is supplied.

**Theorem 1.6 (Reflection center equals the abscissa).**

$$\forall\alpha,c\in\mathbb{R},\quad \left[\forall s\in\mathbb{C},\ s=c-\overline{s}\Leftrightarrow\Re(s)=\frac{\alpha}{2}\right]\Leftrightarrow c=\alpha.$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/UniversalHeatTrace.reflection_center_eq_abscissa_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A separately supplied reflection s maps to c minus conjugate s has the universal heat-trace midline as its fixed line exactly when its center c is the heat-trace abscissa alpha.

## References

- Truth anchor: `D5/S3/Midline/UniversalHeatTrace.heat_coefficient_mem_iff`
- Truth anchor: `D5/S3/Midline/UniversalHeatTrace.heat_vector_inner`
- Truth anchor: `D5/S3/Midline/UniversalHeatTrace.heat_vector_norm_sq`
- Truth anchor: `D5/S3/Midline/UniversalHeatTrace.reflection_center_eq_abscissa_iff`
- Truth anchor: `D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline`
- Truth anchor: `D5/S3/Midline/UniversalHeatTrace.universal_heat_trace_midline_of_boundary_divergent`
