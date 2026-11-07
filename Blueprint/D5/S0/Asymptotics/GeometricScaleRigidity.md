# Geometric Scale Rigidity

For a continuous profile \(h : \mathbb{R}\to\mathbb{R}\), a nonnegative contraction ratio \(\rho<1\), and a fixed \(M\), constancy along the geometric orbit \(\rho^nM\) forces the profile value at \(M\) to equal its value at zero:

$$
\begin{aligned}
&h:\mathbb{R}\to\mathbb{R},
\quad \operatorname{ContinuousAt}(h,0),
\quad 0\le\rho<1,\\
&\qquad\left(\forall n\in\mathbb N,\ h(\rho^nM)=h(M)\right)
\quad\Longrightarrow\quad h(M)=h(0).
\end{aligned}
$$

*Proof.* The powers \(\rho^n\) tend to zero. Multiplication by \(M\) preserves this limit, and continuity at zero sends \(h(\rho^nM)\) to \(h(0)\). The orbit is constant at \(h(M)\), so uniqueness of limits gives the conclusion. ∎

The kernel-checked truth anchor is `D5/S0/Asymptotics/GeometricScaleRigidity.geometric_scale_rigidity`.

This is the shrinking-scale step in Continuation XII, §2, equation (2.17). It formalizes only that step; the surrounding quantum orbit, rate, and response hypotheses remain separate obligations.
