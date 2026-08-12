# Prime Address Support

## Abstract

Every nonzero finitely supported prime-address motion has a nonempty address.

**Theorem 1.1 (Nonzero prime-address motions have nonempty support).**

$$\forall u : \operatorname{PrimeAddressMotion}, u \neq 0 \Rightarrow \operatorname{Nonempty}(\operatorname{Support}(u)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/PrimeAddressSupport.nonempty_support_of_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prime addresses are natural numbers carrying primality certificates. A motion is represented by a finitely supported function on those addresses, so every address in its support is prime by construction.

This records only the mathematical support clause of the source atom. The separate repository discipline for changes outside the generated prime ledger is not claimed by this theorem.

Pinned Mathlib was searched before proving. The exact supporting result is Finsupp.support_nonempty_iff, which states that a finitely supported function has nonempty support exactly when it is nonzero. The Lean theorem is a direct wrapper over that library equivalence.

## References

- Truth anchor: `D5/S3/Axis/PrimeAddressSupport.nonempty_support_of_ne_zero`
