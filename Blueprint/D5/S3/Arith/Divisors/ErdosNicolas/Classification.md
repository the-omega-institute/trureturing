# Strong induction from six checked finite certificate obligations

## Abstract

Strong induction from six checked finite certificate obligations

**Theorem 1.1 (The complete strengthened induction).**

$$BaseOK \Rightarrow \left(SmallLiftsOK \Rightarrow \left(LargeLiftsOK \Rightarrow \left(ResidueTreeOK \Rightarrow \left(MainBoxOK \Rightarrow \left(ExtraOK \Rightarrow \left(\forall n \in \mathbb{N},\; 0 < n \Rightarrow \operatorname{Good}\left(n\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/Classification.good_of_finite_certificates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

Good(n) states τ(n)<Ĥ(n) and 7Ĥ(n)<8τ(n) for n in E={12,24,60,120,180,240,360,420,720,840,1260,1680,2520,5040}; outside E it states Ĥ(n)<τ(n). The six finite obligations are the base interval, exceptional small lifts, exceptional large lifts, residue-tree leaves, the main exponent box, and six extras. Strong induction uses only the positive smaller inputs n/p and n/pᵃ. Two exponent cutoffs, largest-prime cutoffs 677 and 107, and modular chains reduce every remaining branch to one of the six obligations. ResidueTreeOK is conditional on the bound for the smaller input; it does not assume the desired current conclusion.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/Classification.good_of_finite_certificates`
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains](ResidueChains.md)
