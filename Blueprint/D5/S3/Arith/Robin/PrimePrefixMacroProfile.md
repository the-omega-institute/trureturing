# The Complete Prime-Prefix Macro Profile

## Abstract

The literal complete-prefix macro profile has a strict quantitative decrease on the positive axis.

Write Q(u)=u*Re(zeta(1+u)) and C=exp(Euler's constant). The macro profile is C/Q(u). The domain is the entire positive real axis.

**Theorem 1.1 (A strict decrease bound for the literal macro profile).**

Lean statement: `D5/S3/Arith/Robin/PrimePrefixMacroProfile.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PrimePrefixMacroProfile.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<a<b, the profile drop C/Q(a)-C/Q(b) is strictly greater than C*(b-a)/(2*Q(a)*Q(b)).

The existing Fermi Mellin formula is converted to a complete Bose integral after paying both Gamma majorants on the whole positive axis. The exact doubled-scale identity and a positive cancellation factor give the literal Q integral. The Gamma density ratio crosses once. Equal total masses and first moments, together with the strictly increasing remainder chi(t)=t/(1-exp(-t))-t/2, imply Q(b)-Q(a)>(b-a)/2. Positive denominators then yield the profile bound.

The Fermi supplier retains its Sanftenberg (2026), Apache-2.0 provenance. Gamma and Bose representations are classical (NIST DLMF 5.9.1 and 25.5.1). The finite-prefix Euler error, eventual crossing, matched damping constant, and complete Robin pairing require further proofs.

## References

- Truth anchor: `D5/S3/Arith/Robin/PrimePrefixMacroProfile.result`
- Dependency: [D5/S3/Weil/ZetaBridge/FermiMellin](../../Weil/ZetaBridge/FermiMellin.md)
