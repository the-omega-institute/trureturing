# C139 Fourier Cross-Term Rigidity

## Abstract

Three phase readouts on three spanning probe directions recover a complex cross-term vector.

**Theorem 1.1 (Nine common unit probes determine the Fourier cross term).**

$$\operatorname{primitiveCubicPhase}(zeta) \land \operatorname{fourierWindow}(B) \land \operatorname{ninePhaseProbeReadouts}(zeta, B, x, y) \Rightarrow\\\operatorname{crossTermCovariance}(B, x, y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/C139FourierOverlapRigidity.nine_phase_probes_recover_cross_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let ζ be a primitive cubic phase, B a three-coordinate Fourier window, and x,y the old and transformed cross-term columns. Assume the nine common probes, formed from the three directions (1,-1,0), (0,1,-1), and (1,-ζ,0) with phases ζ^r, all have zero signed real readout.

The proof uses the zero-phase readout to eliminate the real part of each probe value and the first nontrivial cubic phase to eliminate its imaginary part. The first two directions give z0=z1=z2 for z=x-By; the third gives z0=conjugate(ζ)z1. Primitivity forces all three coordinates to vanish, hence x=By. The unitary identity B*B=I then gives y=B*x.

This is the finite algebraic content of AURIC C139 continuation Theorem 1.4. It formalizes the cross-term recovery step and does not add any new physical readout, continuity assumption, or unframed projection domain.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/C139FourierOverlapRigidity.nine_phase_probes_recover_cross_term`
