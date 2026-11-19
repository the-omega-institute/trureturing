# Finite stochastic phase residuals and moving averages

## Abstract

A finite stochastic matrix admits a short near-return phase, with a uniform bound for nonresonant moving averages.

Let I be any finite nonempty state type, S its cardinality, and P a real matrix with nonnegative entries and each row summing to one. complexMatrix(P) is the same matrix acting on complex columns. The norm of a column is its maximum coordinate modulus. In the formulas, FiniteNonempty(I) means finite and nonempty; residual(P,w,v) is v-w complexMatrix(P)v, and normInf is the column maximum norm. All sums over I use the whole state type. No irreducibility, aperiodicity, normality, mixing, or lower bound on a positive transition is assumed.

**Theorem 1.1 (A short return phase controls the residual).**

$$\forall I:Type, ((FiniteNonempty(I))\implies (\forall P:Matrix(I,I,\mathbb{R}), ((RowStochastic(P))\implies (\forall w:\mathbb{C}, ((\lvert w\rvert =1)\implies (\forall v:I\to\mathbb{C}, ((v\neq0)\implies (\exists r:\mathbb{N}, ((1\leq r)\land(r\leq card(I))\land(((\lvert 1-(w)^{r}\rvert )^{2})\cdot(normInf(v))\leq (8)\cdot(card(I))\cdot(normInf(residual(P,w,v)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow.phase_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit complex w and nonzero complex column v, one natural return length r between 1 and S satisfies |1-w^r|^2 times the maximum norm of v at most 8S times the maximum norm of v-wP(v). Roots of unity and w=1 are included. In particular, a zero residual forces a return phase among the first S powers.

Choose a coordinate c of v with maximal modulus M>0, and put E equal to the maximum residual modulus. At time t, consider the real part of w^t v(i) conjugate(c). A stochastic weighted average is bounded above by one of its coordinates. The residual identity therefore propagates a supporting value of at least M^2-tME to some coordinate at every natural time t.

The selected coordinate at time t has squared distance from c, after multiplication by w^t, at most 2tME. Among times 0 through S, two selected coordinates coincide, at a<b. With r=b-a, subtracting their two deviations after rotation gives c(w^r-1). The squared triangle bound and a+b at most 2S yield M^2|1-w^r|^2 at most 8SME. Cancellation of the positive M proves the result.

ProbabilityRow(alpha) means nonnegative real coordinates summing to one, and ReportBox(b) means every real coordinate lies in [0,1]. For a real probability row alpha and a real report b with every coordinate in [0,1], write q(n)=alpha dot (P^n b). For an integer j, including negative j, phaseWindow is exactly N^{-1} times the sum, for 0<=k<N, of z^{j(m+k)} q(m+k). The displayed absolute value is the complex modulus. The starting time m is arbitrary and N is a positive natural number.

**Theorem 1.2 (A positive phase gap bounds every moving window).**

$$\forall I:Type, ((FiniteNonempty(I))\implies (\forall P:Matrix(I,I,\mathbb{R}), ((RowStochastic(P))\implies (\forall z:\mathbb{C}, ((\lvert z\rvert =1)\implies (\forall j:\mathbb{Z}, ((j\neq0)\implies (\forall gamma:\mathbb{R}, ((0<gamma)\implies ((\forall r:\mathbb{N}, (((1\leq r)\land(r\leq card(I)))\implies (gamma\leq \lvert 1-(z)^{(j)\cdot(r)}\rvert )))\implies (\forall alpha:I\to\mathbb{R}, (\forall b:I\to\mathbb{R}, (((ProbabilityRow(alpha))\land(ReportBox(b)))\implies (\forall m:\mathbb{N}, (\forall N:\mathbb{N}, ((0<N)\implies (\lvert phaseWindow(P,alpha,b,z,j,m,N)\rvert \leq \frac{(16)\cdot(card(I))}{(N)\cdot((gamma)^{2})})))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow.window_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume |z|=1, j is a nonzero integer, and gamma>0 is a lower bound for |1-z^{jr}| for every natural r between 1 and S. Then the modulus of phaseWindow is at most 16S/(N gamma^2), uniformly in m. Taking z=w and j=1 gives the bound for any unit phase w. Taking gamma to be the positive minimum of the finitely many phase gaps gives the usual minimum-gap formulation.

Set w=z^j and u(t)=P^t b on complex columns. Stochasticity gives maximum norm at most one for every u(t), and the probability row alpha has functional norm at most one. Apply the preceding residual estimate to V=sum_{k<N} w^k u(m+k). Its residual is exactly u(m)-w^N u(m+N), so it has norm at most two. The case V=0 is handled directly; otherwise the short return length and the gamma hypothesis give gamma^2 times the norm of V at most 16S.

The original real matrix powers and real dot product agree exactly with their complex casts. Integer powers satisfy (z^j)^t=z^{jt} for every natural t, including negative j. Thus the unnormalized original sum is w^m alpha(V); its modulus is at most the norm of V. Division by the positive N completes the estimate. A zero phase gap is excluded by the explicit positive hypothesis, and no inverse operator is needed.

These estimates concern finite stochastic readouts and phase averages. They establish neither the complete native finite-memory separation theorem, the algebraic phase gap for the original system, nor its original state realization.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow.phase_residual`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow.window_average`
