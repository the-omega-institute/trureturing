# Local Carry Rules

## Abstract

Four local Fibonacci carry rules preserve the value of finite raw W digits.

`D5/S1/Digit/Carry` defines the local, value-preserving carry rewrites on raw W-digit strings: adjacent ones merge upward, and doubled coefficients split by the Fibonacci identities for indices zero, one, and the general shifted case. Each rule carries its own value-preservation theorem against `rawValue`.

Termination and the normalization map are deliberately absent here; they live in `D5/S1/Digit/Normalize` with an explicit well-founded measure, so no rule in this file claims more than one local step.

## References

- Narrative reference: [D5/S1/Digit/Carry](Carry.md)
