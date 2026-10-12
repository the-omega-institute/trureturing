# Omitted Euler Tail on the Next Prime Clock

## Abstract

The full omitted-prime Euler deficit retains the first omitted atom and the finite Euler prefactor.

Let K=log(4)+4. For a prime p put L=log(p), A_p=sum over primes q<=p of log(q)/q, and h_p=K-(A_p-L)+L/p. The cumulative B_p(t) sums log(q)/q over p<=q<=t. Its exact identity is A_t-A_p+L/p, so the original first omitted atom L/p remains present. The existing first-Mertens supplier gives B_p(t)<=log(t/p)+h_p for t>=p.

**Theorem 1.1 (A bound for the entire inclusive omitted prime series).**

Lean statement: `D5/S3/Arith/Robin/OmittedEulerClockTail.prime_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OmittedEulerClockTail.prime_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p and every u>0, the actual series over prime q>=p of q^(-1-u) is summable and is at most p^(-u)*(1/(u*L)+h_p/L). Every finite set of the actual omitted primes is represented by its positive atomic integral over t>p. Its cumulative logarithmic weight is bounded by B_p(t), and the complete majorant integral is p^(-u)*(1/u+h_p). The uniform bound for all finite subsets proves summability and the full series bound. This does not infer an infinite conclusion from a single finite window.

The analytic primitive and its zero limit are reused from LogarithmicMellinReserve at their original declaration sites. The first-Mertens estimate is reused from the existing Apache-licensed PrimeNumberTheoremAnd port pinned at 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01; its original attribution is preserved. The prime series estimate is consumed by the actual Euler deficit theorem below.

**Theorem 1.2 (The actual Euler deficit keeps its common finite Euler factor).**

Lean statement: `D5/S3/Arith/Robin/OmittedEulerClockTail.actual_euler_defect`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OmittedEulerClockTail.actual_euler_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be the least prime greater than the real cutoff z, and use the existing literal finite Euler product E_z(s)=product over q<=z of (1-q^(-s)). For every u>0, Z(u)=Re(zeta(1+u)) is the real positive zeta value, and 0<=E_z(1+u)-1/Z(u)<=E_z(1+u)*p^(-u)*(1/(u*L)+h_p/L). No assumption supplies the deficit bound. The proof derives it from the actual finite products, the complete prime series estimate, and Mathlib's zeta Euler product limit.

For every finite prime superset, the ordered product identity bounds its loss by the sum of its omitted prime factors. Passing to the exact zeta limit pays the whole omitted product. The least-next-prime hypothesis identifies every omitted prime with q>=p; the original finite Euler factor remains on the right.

This is the pointwise supplier for the positive Euler-tail term and the negative next-prime-clock term in the CS.11 Robin pairing. Its clock is L=log(p). Complete integral comparison, strict negativity, exponential-integral normalization, and the other terms of the full Robin pairing are not asserted by this unit. The full Riemann hypothesis and Robin goal remain open.

## References

- Truth anchor: `D5/S3/Arith/Robin/OmittedEulerClockTail.actual_euler_defect`
- Truth anchor: `D5/S3/Arith/Robin/OmittedEulerClockTail.prime_tail_bound`
- Dependency: [D5/S3/Arith/Robin/LogarithmicMellinReserve](LogarithmicMellinReserve.md)
- Dependency: [D5/S3/Arith/Robin/PrimorialGlobalLaplaceEnvelope](PrimorialGlobalLaplaceEnvelope.md)
