# Terminal Donor Descent

## Abstract

A pure prime-power class can supply a terminal prefix while the other deleted classes supply continuing prefixes, reducing the sum of the actual covering moduli.

**Theorem 1.1 (One whole replacement preserves distinctness and oddness).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/TerminalDonor.terminal_donor_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/TerminalDonor.terminal_donor_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let finitely many progressions A_i = [r_i] modulo d_i cover all natural numbers, with every d_i greater than one. Repeated and even input moduli are allowed. Let q be prime and G, k, W natural numbers, with W coprime to 3q. Suppose every d_i divides 9 q^G W, and fix an actual donor j with d_j = q^(k+1).

Let P_j contain the points in A_j missed by every other original progression. Let s be the number of residues modulo 9 attained by this complete private region. If q is greater than 27 and 27s + 1 is at most q + 9, there is one finite output family covering all natural numbers, with moduli greater than one, no more classes, and a strictly smaller sum of numerical moduli. For this same output family, injectivity of the input modulus array implies injectivity of the output modulus array, and oddness of every input modulus implies oddness of every output modulus.

An empty private region makes the donor redundant. A different deleted class contained in the donor can also be removed directly. In the remaining case, complete prime-prefix liability identifies the full deletion hole while retaining the entire 9W coordinate and the literal q^k parent.

A short ternary prefix is served directly by the actual donor. The other prefixes use one fixed continuing code. Each deleted original has at most one continuing inverse, and its enclosure retains its own cofactor phase. The donor's label is 27 q^k; a continuing original 3^a q^(k+t) m receives 3^(3t+a) q^k m. The new ternary heights separate these labels from retained originals and decode the original numerical labels when those labels are distinct.

Whole coverage uses one common source and the complete deletion hole. Every selected modulus decreases because 27 is less than q, including when the class count stays equal. No irredundancy or extremality hypothesis is required. The result is a conditional covering-system exchange; unrestricted odd distinct noncoverage is a separate claim.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/TerminalDonor.terminal_donor_descent`
- Dependency: [D5/S3/Arith/Congruence/ConditionalComparison/PrefixLiability](PrefixLiability.md)
