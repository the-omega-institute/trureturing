# Ramanujan expansion of a finite sieve

## Abstract

Ramanujan sums and additive character orthogonality identify finite sieve frequencies.

**Theorem 1.1 (Addition of phases).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_character_add`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_character_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive phase exp(2 pi i t) sends addition of real frequencies to multiplication. This identity splits the residue and shift phases in weighted sieve sums.

**Theorem 1.2 (The uniform character average).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_character_orthogonality`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_character_orthogonality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let each positive q_i divide Q. The average over x modulo Q of exp(2 pi i x sum_i r_i/q_i) is one when the rational total frequency is an integer and zero otherwise. Writing the frequency over Q reduces the statement to the primitive additive character on ZMod Q. Its trivial-character sum is Q, cancelling the uniform-average denominator. There is no conjugation or additional Q factor.

**Theorem 1.3 (The centred Ramanujan expansion).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_centered_ramanujan_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_centered_ramanujan_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For squarefree positive Q, write P=Q/phi(Q). The function P times the indicator that x+d is coprime to Q, minus one, equals the sum over nontrivial divisors q of Q of mu(q)c_q(x.val+d)/phi(q). Multiplicativity gives the prime-factor expansion. At a prime p the Ramanujan sum is p-1 if p divides the argument and -1 otherwise; the resulting product is the reduced-residue indicator times P. The divisor q=1 has coefficient and Ramanujan sum both equal to one, so centring removes exactly this term. Natural shifts including zero and reduction of x+d modulo Q are retained. This pointwise identity supplies the frequencies for weighted moment expansions.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_centered_ramanujan_expansion`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_character_add`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRamanujan.sieve_character_orthogonality`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/RamanujanSums](RamanujanSums.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergDefs](SieveKuperbergDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/TotientPrimeProducts](TotientPrimeProducts.md)
