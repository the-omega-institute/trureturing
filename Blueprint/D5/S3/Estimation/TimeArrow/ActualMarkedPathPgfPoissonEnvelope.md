# Forward Marked Path Transfer

## Abstract

Actual forward paths and their finite transfer.

**Theorem 1.1 (Finite Poisson envelope).**

$$\forall M,q,T,k:Nat, \forall r,eta:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, 1\leq q<M \land 0<r<1 \land \operatorname{compensation}(M, q, r)<1 \land (k=1 \lor k=2) \land \operatorname{injective}(m) \land 0\leq eta\leq \frac{1}{4} \land \lvert \operatorname{driftA}(r, S, m, zp, zm) \rvert\leq eta \land \lvert \operatorname{driftB}(r, S, m, zp, zm) \rvert\leq eta \land (T) \cdot ({eta}^{2})\leq \frac{1}{10} \Rightarrow \lvert \operatorname{actualPGF}(r, S, m, zp, zm, T)-\operatorname{exp}((T) \cdot (\operatorname{driftA}(r, S, m, zp, zm))) \rvert\leq (((20) \cdot (T)) \cdot ({eta}^{2})) \cdot (\operatorname{exp}((T) \cdot (\operatorname{Re}(\operatorname{driftA}(r, S, m, zp, zm)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.actual_marked_path_pgf_poisson_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 1 <= q < M, 0 < r < 1, and c = rq/(M-q) < 1, where M-q is the natural difference. A support has exactly q positive states. There are one or two distinct positive marked states, with arbitrary complex tilts. If 0 <= eta <= 1/4, both drift norms are at most eta, and T eta squared is at most 1/10, the native generating function differs from exp(TA) by at most 20 T eta squared times exp(T Re A).

Finite product identities turn actual count powers into edge factors without dividing by a tilt. Appending the last state to a complete history gives the forward endpoint sum. Its tilted mass at y is (F_t + chi(y) G_t)/(2M), with F_0 = 1 and G_0 = 0. The physical endpoint recurrence is F_(t+1) = (1+A) F_t + A G_t and G_(t+1) = B F_t + B G_t. Summing endpoints gives F_T.

Normalize by h = 1+A, whose norm is at least 3/4. The parity feedback is a finite geometric sum with ratio B/h. Running maxima bound the normalized increments using theta = norm(AB)/(norm(h)(norm(h)-norm(B))) <= (8/3) eta squared. The total normalized error is at most 2 T theta.

The complex logarithm remainder is bounded by kappa = norm(A) squared/(2(1-norm(A))) <= (2/3) eta squared. Exponentiation then compares h to exp(A), and the two errors combine with coefficient 52/3 <= 20. The sole logarithm is applied to h. All divisions have positive uniform bounds, so T = 0, eta = 0, A = 0, B = 0, and zero tilt coordinates remain included.

This finite generating-function estimate does not supply relative point-mass estimates, coefficient extraction, growing-window uniformity, or entropy asymptotics.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.actual_marked_path_pgf_poisson_envelope`
- Dependency: [D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient](MarkedPoissonCoefficient.md)
