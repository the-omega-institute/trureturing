# Fresh Prime-Power Height Bound

## Abstract

A finite palette of unused prime-power labels bounds an actual pure prime-power height through a private source and a complete repair.

**Theorem 1.1 (Unused repair labels bound the original height).**

Lean statement: `D5/S3/Arith/Covering/FreshPrimePowerHeightBound.fresh_prime_power_height_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/FreshPrimePowerHeightBound.fresh_prime_power_height_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a whole cover with n pairwise distinct odd moduli greater than one, having the smallest possible number of classes among all such covers. Let p and r be distinct primes. Assume that F contains actual classes with moduli p, r^a and r^H, and fix a private point x of the actual r^H class: x belongs to that class and to no other original class.

Choose p minus one distinct heights j, each between one and a. For every chosen j, require that the numerical modulus p r^j is absent from the entire original family. Then H is at most a plus the integer quotient of p minus three by r minus one. Oddness of the primes follows from the actual original moduli.

For H greater than a, use the complete original period and the same private point x. At each r-digit level from a through H minus one, construct r minus one points whose first difference from x occurs there. Preserve all lower r-digits and the complete prime-to-r coordinate. Whole coverage supplies an original class for every such point. Privacy of x forces its r-depth to exceed that level. Different first differences have different suppliers, and none is the original r^H class.

Together with the r^H class, these suppliers form one plus (H minus a) times (r minus one) distinct original classes. Their moduli are divisible by r^(a+1), and their residues agree with x modulo r^a. Move the actual r^a class to that phase and delete this packet. The moved parent covers every deleted class.

The unchanged pure-p class covers its own p-root in the old parent. Assign the other p minus one roots bijectively to the chosen fresh labels p r^j. Their fixed CRT residues use the old parent's r-prefixes. They cover the rest of the entire old parent, so every original liability is paid. Distinct heights give distinct inserted labels, and global freshness prevents collisions with retained labels.

If the stated height bound failed, the constructed packet would contain more than p minus one classes. The parity step uses the odd lower count one plus (H minus a) times (r minus one), not an assumption that every class in that phase has odd total count. Replacing the packet by p minus one repair classes would give a smaller whole odd distinct cover, contradicting count minimality.

The private-source count is a pure-power instance of the classical directional mismatch method of Lettl and Sun, On covers of abelian groups by cosets, Acta Arithmetica 131 (2008), 341-350. The proof constructs the needed suppliers and repair directly. It does not assume a supplier bound or replacement coverage, require H to be the largest original r-height, or use modulus-sum minimality. Existence of the required original powers and fresh palette remains a separate application condition; the unrestricted odd covering problem is not settled.

## References

- Truth anchor: `D5/S3/Arith/Covering/FreshPrimePowerHeightBound.fresh_prime_power_height_bound`
- Dependency: [D5/S3/Arith/Covering/ConcentratedPrimeSingleton](ConcentratedPrimeSingleton.md)
