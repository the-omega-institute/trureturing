# Finite Cyclic Window Register

## Abstract

Finite cyclic clock and shift matrices obey Weyl, periodicity, unitarity, and scalar-commutant relations.

**Theorem 1.1 (The window phase is a primitive root).**

$$\forall M \in \mathbb{N}_{>0},\ \operatorname{IsPrimitiveRoot}(e^{\frac{2\pi i}{M}}, M)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowRegister.windowRoot_isPrimitiveRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural window cardinality M, the standard phase omega_M = exp(2 pi i/M) is a primitive M-th root of unity. The positivity condition is the displayed form of the formal NeZero M instance; the declaration makes no claim for a zero-cardinality window.

**Theorem 1.2 (The clock and shift obey the finite Weyl relation).**

$$\forall M \in \mathbb{N}_{>0},\ V_{M}U_{M} = \omega_{M}\cdot (U_{M}V_{M})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowRegister.window_weyl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write V_M for the diagonal clock with entries omega_M raised to the standard representatives of Z/MZ, and U_M for the circulant shift whose entry at (r,s) is one exactly when r - s = 1. With these conventions the formal matrix identity has the displayed orientation.

The proof is entrywise. At the unique nonzero shift entry, additivity of the standard Z/MZ character advances the clock phase by omega_M; every other entry vanishes on both sides. The section-3 provenance is restricted here to this fixed finite matrix window: no crossed-product universal property or central winding relation is asserted.

**Theorem 1.3 (The cyclic shift closes at the window cardinality).**

$$\forall M \in \mathbb{N}_{>0},\ U_{M}^{M} = I_{M}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowRegister.shiftMatrix_pow_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The circulant shift U_M is the permutation matrix for translation by one on Z/MZ. Applying that permutation M times is the identity, so its M-th matrix power is I_M. This is only the fixed-window closure U_M^M = I_M; it does not introduce a central winding phase.

**Theorem 1.4 (The clock phases close at the window cardinality).**

$$\forall M \in \mathbb{N}_{>0},\ V_{M}^{M} = I_{M}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowRegister.clockMatrix_pow_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each diagonal entry of V_M is a power of the primitive phase omega_M. Raising V_M to the M-th power therefore raises every entry to a multiple of M, giving the identity matrix I_M.

**Theorem 1.5 (The finite-window generators are unitary).**

$$\forall M \in \mathbb{N}_{>0},\ U_{M}^{*}U_{M} = I_{M} \land V_{M}^{*}V_{M} = I_{M}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowRegister.window_unitary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift U_M is a permutation matrix, so its conjugate transpose is its inverse. The clock V_M is diagonal and every diagonal phase has complex norm one. Consequently both displayed star-products are the identity.

**Theorem 1.6 (The joint commutant consists of scalars).**

$$\begin{gathered}\forall M \in \mathbb{N}_{>0},\\\forall A \in M_{M}(\mathbb{C}),\\(AV_{M} = V_{M}A \land AU_{M} = U_{M}A) \Rightarrow\\\exists \lambda \in \mathbb{C},\ A = \lambda\cdot I_{M}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WindowRegister.window_commutant_eq_scalars` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be an M-by-M complex matrix indexed by Z/MZ. Commutation with the clock V_M forces every off-diagonal entry of A to vanish because distinct indices carry distinct powers of the primitive phase. Commutation with the shift U_M then propagates equality around the diagonal. Thus A is lambda times I_M for a complex scalar lambda.

This is the scalar joint-commutant statement for the two concrete finite generators. The section-3 provenance supplies the motivating observer language only; the theorem does not identify an abstract crossed product, a continuous field, or a holonomy class.

## References

- Truth anchor: `D5/S3/Observer/WindowRegister.clockMatrix_pow_card`
- Truth anchor: `D5/S3/Observer/WindowRegister.shiftMatrix_pow_card`
- Truth anchor: `D5/S3/Observer/WindowRegister.windowRoot_isPrimitiveRoot`
- Truth anchor: `D5/S3/Observer/WindowRegister.window_commutant_eq_scalars`
- Truth anchor: `D5/S3/Observer/WindowRegister.window_unitary`
- Truth anchor: `D5/S3/Observer/WindowRegister.window_weyl`
- Dependency: [D5/S3/Fourier/FinitePoisson](../Fourier/FinitePoisson.md)
