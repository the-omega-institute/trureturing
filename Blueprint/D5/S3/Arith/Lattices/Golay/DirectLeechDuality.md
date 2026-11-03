# Direct real selfduality from integer Golay congruences

## Abstract

Direct real selfduality from integer Golay congruences

**Theorem 1.1 (Coordinate probes belong to the literal construction).**

Lean statement: `D5/S3/Arith/Lattices/Golay/DirectLeechDuality.eight_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/DirectLeechDuality.eight_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eight times each coordinate vector satisfies the parity, binary code and modulo-eight sum conditions. These vectors both constrain real dual coordinates and prove that the actual lattice spans the full real coordinate space.

**Theorem 1.2 (Direct selfduality without determinant or covolume assumptions).**

Lean statement: `D5/S3/Arith/Lattices/Golay/DirectLeechDuality.raw_integer_construction_dual_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/DirectLeechDuality.raw_integer_construction_dual_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any binary selfdual doubly even code, the real integer image of its literal parity, quotient-code and modulo-eight sum conditions is selfdual under dot divided by eight, provided its pairing is integral. The proof constructs every probe from those conditions. Eight times a coordinate vector forces dual coordinates integral. Four times coordinate differences forces common parity. Twice each binary codeword lift forces code membership by binary selfduality. The vector one minus four times the zeroth coordinate vector recovers the complete sum condition. The proved integral pairing gives the converse inclusion directly.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/DirectLeechDuality.eight_mem`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/DirectLeechDuality.raw_integer_construction_dual_eq`
