# FinitePulseKernelTransport

## Abstract

Signed bounds from exclusion and a local envelope

**Theorem 1.1 (Exact accounting before exclusion).**

Lean statement: `D5/S3/Arith/Robin/FinitePulseKernelTransport.kernel_atom_accounting`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FinitePulseKernelTransport.kernel_atom_accounting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a price curve, a<y, 1<t<=B and any D, actualKernel(y)-referenceKernel(a) equals the closed-pulse indicator at t times (price(t)-price(B))/D, minus D inverse times the interval integral of the closed-pulse weight over [t,B].

The equality includes a=t, y=t, the terminal endpoint B, and atoms beyond B. The difference between open and closed integration cutoffs is a single null point, whereas the initial correction retains the literal closed endpoints. No initial actual atom is silently removed.

**Theorem 1.2 (Finite closed-pulse transport identity).**

Lean statement: `D5/S3/Arith/Robin/FinitePulseKernelTransport.finite_pulse_accounting`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FinitePulseKernelTransport.finite_pulse_accounting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite index set I with a(i)<y(i), sum h(i)*(actualKernel(y(i))-referenceKernel(a(i))) equals delta(t)*(price(t)-price(B))/D minus the integral of delta(x)*weight(x) over [t,B], divided by D. Here delta(x)=sum h(i)*1_[a(i),y(i)](x).

Finite summation and integrability of the cutoff weight prove the identity. The weights h need not be nonnegative for this identity. It is consumed by the signed bounds.

**Theorem 1.3 (Signed bounds from exclusion and a local envelope).**

Lean statement: `D5/S3/Arith/Robin/FinitePulseKernelTransport.finite_pulse_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FinitePulseKernelTransport.finite_pulse_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume additionally h(i)>=0, D>0, t outside every closed pulse, and delta(x)<=L on [t,B]. Then the finite response lies between -(price(t)-price(B))*L/D and zero.

Exclusion removes the initial correction only after the exact accounting identity. The nonnegative weighted integral supplies the sign and the local envelope supplies the lower bound. There is no assumption that an integrated selected kernel is globally nonincreasing. The original specialization supplies its envelope, denominator and every prime exclusion.

## References

- Truth anchor: `D5/S3/Arith/Robin/FinitePulseKernelTransport.finite_pulse_accounting`
- Truth anchor: `D5/S3/Arith/Robin/FinitePulseKernelTransport.finite_pulse_bounds`
- Truth anchor: `D5/S3/Arith/Robin/FinitePulseKernelTransport.kernel_atom_accounting`
- Dependency: [D5/S3/Arith/Robin/DelayedAtomTransport](DelayedAtomTransport.md)
