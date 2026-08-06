# Seat-Tower Consequences

## Abstract

Record exact residue, Jacobi, cosecant, gap, and combination-counting consequences from the seat-tower frontier.

This module records six formal consequences with every structural premise exposed. It does not supply the finite conflict table, the selector-numerator bridge, an orbit-to-choice bijection, or any finite experimental certificate. No finite observation or measurable claim is closed.

**Theorem 1.1 (A residue modulo ninety-six fixes its coarser residues).**

$\forall a,b\in\mathbb{Z},\ a\equiv b\ [\operatorname{mod}\ 96] \Rightarrow a\equiv b\ [\operatorname{mod}\ 24] \land a\equiv b\ [\operatorname{mod}\ 48]$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerConsequences.mod_ninety_six_refines_twenty_four_and_forty_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An explicit congruence modulo 96 implies congruence modulo 24 and modulo 48. This does not supply the finite conflict table or identify a residue with an orbit selector.

**Theorem 1.2 (An identified selector numerator splits into three Jacobi factors).**

$$\forall \beta,j\in\mathbb{Z},\ \forall n\in\mathbb{N},\ j=\left(\frac{2(-1)\beta}{n}\right) \Rightarrow j=\left(\frac{2}{n}\right)\left(\frac{-1}{n}\right)\left(\frac{\beta}{n}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerConsequences.jacobi_factorization_of_selector_numerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selector is assumed to equal the Jacobi symbol with numerator 2(-1)beta. Multiplicativity then yields the three factors; the Zolotarev congruence bridge and the 144-case certificate remain open.

**Theorem 1.3 (The peak equation rearranges to the cosecant expression).**

$$\forall r,\theta\in\mathbb{R},\ \sin\theta\neq 0 \land 2r\sin\theta=\sqrt{3} \Rightarrow r=\frac{\sqrt{3}}{2\sin\theta}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerConsequences.cosecant_peak_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero sine and the explicit peak equation imply the displayed quotient. The theorem does not derive that equation from pin data or choose an angle branch.

**Theorem 1.4 (The leading term controls the finite-sum gap).**

$$\forall \alpha,\ \forall a\in\mathbb{Z},\ \forall S\subset_{\mathrm{fin}}\alpha,\ \forall f:\alpha\to\mathbb{Z},\ |a|-\sum_{i\in S}|f(i)|\leq\left|a+\sum_{i\in S}f(i)\right|$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerConsequences.dominant_term_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse triangle inequality bounds the absolute full sum below by the leading absolute value minus the total absolute remainder. No continued-fraction dominance premise or 66-case certificate is inferred.

**Theorem 1.5 (There are n singleton choices among n labeled factors).**

$\forall n\in\mathbb{N},\ \operatorname{card}\{S\subseteq\operatorname{Fin}(n)\mid |S|=1\}=n$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerConsequences.singleton_stationing_choice_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-element subsets of n labeled factors have cardinality n. This is a combination-counting statement and does not identify actual orbits with those subsets.

**Theorem 1.6 (Three labeled factors have three singleton choices).**

$\operatorname{card}\{S\subseteq\operatorname{Fin}(3)\mid |S|=1\}=3$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerConsequences.three_split_primes_have_three_singleton_choices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing the combination count to three gives three choices. This does not identify actual orbits of the 1729 example or prove the required orbit-to-choice bijection.
