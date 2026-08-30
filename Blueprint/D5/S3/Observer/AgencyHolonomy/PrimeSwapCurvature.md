# Prime Swap Curvature

## Abstract

Stable prime-memory lifts have a gauge-invariant adjacent-swap defect that detects disagreement between nonresonant observer-origin estimates.

**Theorem 1.1 (Prime swap curvature specification).**

Let \(K\) be a field. Define

\[
U_{a,b,\lambda}(x,z)=(ax+bz,\lambda z),
\]

\[
C_{p,q}=(a-\lambda_q)b_p-(a-\lambda_p)b_q,
\]

and, when \(a-\lambda_p
eq0\),

\[
c_p=rac{b_p}{a-\lambda_p}.
\]

For \(a-\lambda_p
eq0\) and \(a-\lambda_q
eq0\):

\[
egin{aligned}
\pi_1(U_qU_p(x,z))-\pi_1(U_pU_q(x,z))&=C_{p,q}z,\\
\pi_2(U_qU_p(x,z))&=\pi_2(U_pU_q(x,z)),\\
C_{q,p}&=-C_{p,q},\\
C_{p,q}(b_p+(a-\lambda_p)c,\ b_q+(a-\lambda_q)c)&=C_{p,q}(b_p,b_q),\\
C_{p,q}&=(a-\lambda_p)(a-\lambda_q)(c_p-c_q),\\
C_{p,q}=0&\Longleftrightarrow c_p=c_q.
\end{aligned}
\]

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature.prime_swap_curvature_spec`.

*Source.* Repository-derived.

*Commentary.*

The scalar channel is insensitive to the order of the two local factors. The memory channel records their adjacent-swap curvature. A common change of memory origin adds the same coboundary pattern to every local injection and leaves the curvature unchanged. Away from resonance, zero curvature is exactly agreement of the two inferred observer origins.

The theorem is algebraic. It does not identify the parameters with Euler factors or prove any extraction-depth limit.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PrimeSwapCurvature.prime_swap_curvature_spec`
