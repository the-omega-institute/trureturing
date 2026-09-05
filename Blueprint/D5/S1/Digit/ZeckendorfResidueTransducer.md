# Zeckendorf Residue Transducer

## Abstract

A least-significant-first Fibonacci residue transducer computes canonical Zeckendorf values modulo every prime.

**Theorem 1.1 (Every finite prefix preserves the Fibonacci residue invariant).**

$$\begin{aligned}\forall p \in \operatorname{Primes}(\mathbb{N}),\\\forall bits \in \operatorname{List}(\operatorname{Fin}(2)),\\\forall k \in \mathbb{N},\\\forall r \in \operatorname{ZMod}(p),\\\operatorname{residue}(\operatorname{runResidueStateFrom}(p, (r, \operatorname{fib}(k), \operatorname{fib}(k + 1)), bits)) = r + \operatorname{cast}(\operatorname{fibonacciWeightedSumFrom}(k, bits), \operatorname{ZMod}(p)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfResidueTransducer.residue_step_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any prime p, least-significant-first bit word, Fibonacci index k, and starting residue r, the final residue is r plus the cast of the Fibonacci-weighted bit sum into ZMod p.

The proof folds the state transition (r,u,v) to (r + b*u,v,u+v). Its private induction keeps u and v equal to the consecutive Fibonacci residues F_k and F_(k+1).

**Theorem 1.2 (Every finite bit word evaluates to its Fibonacci sum modulo the prime).**

$$\begin{aligned}\forall p \in \operatorname{Primes}(\mathbb{N}),\\\forall bits \in \operatorname{List}(\operatorname{Fin}(2)),\\\operatorname{runResidueBits}(p, bits) = \operatorname{fibonacciWeightedSumFrom}(2, bits) \bmod p.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfResidueTransducer.run_residue_eq_sum_fib_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The initial state is exactly (0,F_2,F_3), and the input word is read least-significant first. Taking the natural representative of the prefix invariant gives the ordinary remainder modulo p.

This theorem applies to every finite Fin 2 word; it does not assume Zeckendorf admissibility or canonicality.

**Theorem 1.3 (Canonical Zeckendorf digits compute the original value modulo the prime).**

$$\begin{aligned}\forall p \in \operatorname{Primes}(\mathbb{N}),\\\forall n \in \mathbb{N},\\\operatorname{runZeckendorfResidueTransducer}(p, \operatorname{wdigits}(n)) = n \bmod p.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/ZeckendorfResidueTransducer.zeckendorfResidueTransducer_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repository's sparse descending wdigits list is expanded into a dense least-significant-first word beginning at Fibonacci index two.

Canonicality proves that the dense word has the same Fibonacci-weighted sum as wdigits. The frozen decode_wdigits theorem is used only in the final rewrite from that sum to n.

## References

- Truth anchor: `D5/S1/Digit/ZeckendorfResidueTransducer.residue_step_invariant`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidueTransducer.run_residue_eq_sum_fib_mod`
- Truth anchor: `D5/S1/Digit/ZeckendorfResidueTransducer.zeckendorfResidueTransducer_correct`
- Dependency: [D5/S0/Conventions/WDigits](../../S0/Conventions/WDigits.md)
