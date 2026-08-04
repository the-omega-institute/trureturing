# Finite Poisson Summation

## Abstract

Finite Poisson summation on an arbitrary additive subgroup of a positive cyclic group.

**Theorem 1.1 (Finite Poisson summation on a cyclic subgroup).**

$$\begin{gathered}
m>0,\quad H\leq \mathbb{Z}/m\mathbb{Z},\quad
H^\perp=\{k:\forall h\in H,\ e^{2\pi i kh/m}=1\},\\
\widehat f(k)=\sum_{x\in\mathbb{Z}/m\mathbb{Z}}f(x)e^{-2\pi i kx/m}
\quad\Rightarrow\quad
\sum_{h\in H}f(h)=\frac{|H|}{m}\sum_{k\in H^\perp}\widehat f(k).
\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/FinitePoisson.finite_poisson_summation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The annihilator is defined explicitly by triviality of the standard character on H. Its identification with the complete character group of the quotient supplies both character orthogonality and the cardinal identity |H||H-perp| = m. Expanding the pinned ZMod discrete Fourier transform and exchanging the two finite sums then yields the stated normalization without assuming either identity.

**Theorem 1.2 (The even subgroup has an explicit Poisson witness).**

$$H=\{0,2\},\quad f(x)=\mathbf{1}_{x=0}
\quad\Rightarrow\quad
\sum_{h\in H}f(h)=1=\frac{|H|}{4}\sum_{k\in H^\perp}\widehat f(k).$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/FinitePoisson.finite_poisson_mod_four_even_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Kernel-reduced membership checks prove that 2 belongs to H while 1 does not. The branch witnesses then prove 2 belongs to the annihilator and 1 does not; character orthogonality evaluates to 2 at x = 2 and to 0 at x = 1. For the delta function at zero, both sides of Poisson summation reduce to the explicit value 1.
