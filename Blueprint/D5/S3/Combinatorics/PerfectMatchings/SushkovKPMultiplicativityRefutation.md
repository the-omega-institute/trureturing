# KP multiplicativity necessity at H = N = 1

## Abstract

The normalized KP tau function 1 + t₁ gives a nonmultiplicative coefficient family in Sushkov's equation (6.1).

**Definition 1.1 (The necessity implication).**

Lean statement: `D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sushkov, arXiv:2611.02795v1, §6 item 1, asks whether multiplicativity is necessary for the Frobenius image of (6.1) to be a KP tau function. At H = N = 1, every Jucys–Murphy factor is the group-algebra unit. An arbitrary complex family a gives the coordinates of the unscaled class sums in each degree n, including degree zero. By (2.15), the degree-n Frobenius component is the sum of (a(ρ) / z(ρ)) p(ρ) over the partitions ρ of n.

The premise requires constant term one and vanishing of the formal KP bilinear residue in every output time weight d. The conclusion requires one complex value for each positive part size whose multiset product equals a(ρ) for every partition ρ. Repeated parts contribute repeatedly and the empty product is one.

Use pⱼ = j tⱼ and two independent time sequences t and s. The Miwa substitutions send pⱼ to j tⱼ − z⁻ʲ and j sⱼ + z⁻ʲ. Multiplying the image of each variable by zʲ clears a common z⁻ᵐ in an input component of weight m. The exponential is exp(∑ⱼ (tⱼ − sⱼ)zʲ) over all positive indices. After clearing the shifts in input weights m and n, the coefficient of zᵈ has time weight d and represents the residue precisely when m + n = d + 1. Each weight therefore uses a finite sum.

**Theorem 1.2 (The affine counterexample).**

Lean statement: `D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set a(∅) = a((1)) = 1 and set a(ρ) = 0 in every degree at least two. The two supported partitions have z(ρ) = 1, so the weighted Frobenius components are those of 1 + p₁, giving τ(t) = 1 + t₁. The part (1) forces the multiplicative value for size one to be 1. The coefficient of (1,1) is zero although the square of that value is one.

Put A = 1 + t₁ and B = 1 + s₁. Clearing z⁻² from the shifted product gives (Az − 1)(Bz + 1). The residue is coefficient one of this polynomial times the full exponential. Its value is A − B − (t₁ − s₁) = 0 because the exponential has constant coefficient one and linear coefficient t₁ − s₁. In weight zero the two input pairs (0,1) and (1,0) cancel. Weight one uses (1,1), and every higher weight requires a zero input component.

Classifying all coefficient families giving KP tau functions remains open here.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/SushkovKPMultiplicativityRefutation.result`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2](DeformedJucysMurphyC2.md)
