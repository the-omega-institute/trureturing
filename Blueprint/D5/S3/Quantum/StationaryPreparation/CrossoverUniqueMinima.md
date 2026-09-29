# Unique Ordered Minima of the Crossover Costs

## Abstract

The explicit crossover costs have unique interior global minima, with the minimum for denominator power two strictly preceding that for power one.

All variables are real. Set g(z)=1+(z squared-sqrt(z to the fourth+4))/2, A(z)=c+(h-z) squared, D(z)=1-gamma g(z), and F_j(z)=A(z)/(D(z) raised to the power j), for j=1,2. The feasible set S consists of all z with 0 <= z <= h and D(z)>0.

**Theorem 1.1 (Strict global minima on the full feasible set).**

$$\forall c,h,\gamma\in \mathbb{R}, (\frac{12}{5}<c\land 0<h<\frac{31}{20}\land 0<\gamma)\implies \ \exists z_2,z_1\in \mathbb{R}, 0<z_2<z_1<h\land z_2\in S\land z_1\in S\land \ (\forall z\in S, z\neq z_2\implies F_2(z_2)<F_2(z))\land \ (\forall z\in S, z\neq z_1\implies F_1(z_1)<F_1(z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/StationaryPreparation/CrossoverUniqueMinima.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write r=h-z, v=z squared/sqrt(z to the fourth+4), p=z(1-v), and q=(1-v)(1-2v-2v squared). Then g'=p and p'=q. For H_t=g+t A p/r, where 1/2 <= t <= 1, differentiation gives H_t'=(1-t)p+t[c p/r squared+(r+c/r)q].

The expression in brackets is strictly positive on 0<z<h. After division by a positive factor, the assertion is z+r(1+r squared/c)(1-2v-2v squared)>0. For z<=4/5, v<=8/25 makes the final factor positive. On the next three intervals, bounded above by 1, 6/5, and h respectively, the negative part K=2v+2v squared-1 is bounded above by 1/3, 1, and 3. The corresponding r bounds are 3/4, 11/20, and 7/20; together with c>12/5 they give r(1+r squared/c)K<z.

The continuous expression r(g-1/gamma)+t A p is negative at zero and positive at h, so it vanishes at an interior point a. There gamma H_t(a)=1, and H_t(a)>g(a) implies D(a)>0. Strict increase of H_t gives uniqueness of its root. Since H_1>H_(1/2) in the interior, their roots satisfy z2<z1.

For j=1,2 the derivative of F_j is 2r D to the power -(j+1) times (gamma H_(j/2)-1). It is negative below its root and positive above. Strict increase of g ensures positivity of D on every comparison interval ending at a feasible point. Continuity then includes zero and h whenever those endpoints are feasible. Thus each root has strictly smaller cost than every other point of S, which also proves uniqueness.

This statement concerns the two scalar costs. Dependence of the minima on gamma, convexity of a Pareto curve, asymptotic expansions, and attainment by physical preparations are separate assertions.

## References

- Truth anchor: `D5/S3/Quantum/StationaryPreparation/CrossoverUniqueMinima.result`
