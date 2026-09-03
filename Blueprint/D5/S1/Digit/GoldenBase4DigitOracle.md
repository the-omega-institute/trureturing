# Golden Base-Four Digit Oracle

## Abstract

Exact floor arithmetic supplies the base-four golden digit oracle and canonical power samples.

**Theorem 1.1 (Canonical power samples decode exactly).**

$$\operatorname{decode}(\operatorname{powerOccupiedIndices}(i)) = \operatorname{pow}(4, i).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/GoldenBase4DigitOracle.decode_powerOccupiedIndices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input sample reuses the canonical Zeckendorf occupied-index representation already supplied by WDigits.

The output oracle is the final radix-four remainder of the exact natural floor of 4^(i+1) times the golden ratio.

Bit-stream serialization and the published Walnut input convention remain explicit later obligations.

## References

- Truth anchor: `D5/S1/Digit/GoldenBase4DigitOracle.decode_powerOccupiedIndices`
- Dependency: [D5/S0/Conventions/WDigits](../../S0/Conventions/WDigits.md)
