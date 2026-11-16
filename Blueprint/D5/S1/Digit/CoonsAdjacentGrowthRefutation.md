# Equal adjacent growth exponents in Coons's partition question

## Abstract

The actual bounded-digit radix-four counts with bounds five and six both have upper logarithmic growth exponent one half.

Source: Michael Coons, arXiv:2611.08109v1, Section 3, final strict adjacent-multiplicity logarithmic limsup question, with the count defined by the product in Section 2. The source is licensed CC BY 4.0. The question quantifies over every natural radix ell at least two and every natural k at least ell minus one, including ell=2,k=1. It asks for strict growth from k to k+1 at the same radix. The introductory index typo is resolved by the Section 2 product. The separate liminf and first-linear-threshold questions are outside this statement. The source attribution identifies the question and its count convention; it does not establish historical priority for the counterexample.

**Definition 1.1 (Source weighted value).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.weight`

*Formalization.* `D5/S1/Digit/CoonsAdjacentGrowthRefutation.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell in the natural numbers and a : Nat →₀ Nat, weight ell a is the sum over support(a) of a(i) times ell^i. All terms are natural numbers. The support is intrinsic to the function, so zero padding has no identity.

**Definition 1.2 (Actual finite-support source carrier).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.Partitions`

*Formalization.* `D5/S1/Digit/CoonsAdjacentGrowthRefutation.Partitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Partitions k ell n is exactly the subtype of finitely supported Nat-valued functions a with a(i) at most k for every natural i and weight ell a=n. Each function occurs once. No word length or selected subsequence enters this definition.

**Definition 1.3 (Finite cardinality).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count`

*Formalization.* `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

count k ell n is Nat.card (Partitions k ell n). Finiteness is proved for every k,n and every ell at least two. The private count_zero lemma proves count k ell 0=1: positivity of every power forces all coefficients of a zero-weight function to vanish. That lemma is consumed by count_positive.

**Definition 1.4 (Natural-input logarithmic readout).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.readout`

*Formalization.* `D5/S1/Digit/CoonsAdjacentGrowthRefutation.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

readout k ell n is Real.log (count k ell n) / Real.log n. At n=0,1 this uses Mathlib's total real logarithm and division conventions. Every tail starts at least at two; positivity of the count and of log n is proved wherever the asymptotic estimates use division.

**Definition 1.5 (Extended-real every-tail limsup).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.exponent`

*Formalization.* `D5/S1/Digit/CoonsAdjacentGrowthRefutation.exponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

exponent k ell is the infimum, over natural N with 2≤N, of the supremum, over every natural n with N≤n, of the real readout embedded in EReal. This is the ordinary extended-real tail definition itself. There is no real-limsup boundedness premise and no replacement by block maxima.

**Definition 1.6 (The complete universal event).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.claim`

*Formalization.* `D5/S1/Digit/CoonsAdjacentGrowthRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

claim : Prop is ∀ ell : Nat, 2≤ell → ∀ k : Nat, ell-1≤k → exponent k ell < exponent (k+1) ell. It has no finiteness conjunct, extra parameter hypothesis or excluded endpoint.

**Theorem 1.7 (Support restriction proves actual finiteness).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.partitions_finite`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CoonsAdjacentGrowthRefutation.partitions_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k ell n and hell : 2≤ell, Finite (Partitions k ell n). If n<ell^L, any nonzero coefficient at i≥L contributes at least ell^L, a contradiction. Restriction to Fin L is injective into Fin L → Fin(k+1). One can take L=n+1. The pack and weight_window bridges prove that extension by zeros has exactly the original support sum.

**Theorem 1.8 (Ordinary radix representations are admitted).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_positive`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k ell n with 2≤ell and ell-1≤k, 0<count k ell n. The digits Nat.digits ell n lie below ell, and Nat.ofDigits_digits gives their weighted value n. Extension by zeros yields an actual finite-support member. At zero the unique zero function gives count one.

**Theorem 1.9 (The uniform bound at every natural input).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_upper`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k,m,n, k≤6 and n<4^(m+1) imply count k 4 n≤2^m. Map a partition to the m quotients a(i)/4 for i<m. Each quotient is zero or one, and the top quotient is zero because n<4^(m+1). Equal weighted sums determine equal units digits modulo four; equality of the quotients then determines equal full digits. Induction after removing the equal head proves injectivity. The finite cardinality bound is thus for actual functions. Taking m=Nat.log 4 n proves count(k,4,n)^2≤n for every n≥1, without a recurrence surrogate.

**Definition 1.10 (The unbounded lower family).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.repunit`

*Formalization.* `D5/S1/Digit/CoonsAdjacentGrowthRefutation.repunit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

repunit m is the sum of 4^i for 0≤i<m+1. Its bounds are 4^m≤repunit m<4^(m+1). The index m counts interior binary carries; the repunit has m+1 digits.

**Theorem 1.11 (Distinct carries attain the count bound).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_repunit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_repunit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k,m with 5≤k≤6, count k 4 (repunit m)=2^m. An arbitrary v : Fin m → Fin 2 supplies carries c(1),...,c(m), with c(0)=c(m+1)=0. Set a(i)=1+4c(i+1)-c(i) for i<m+1, and zero elsewhere. These natural digits lie in {0,1,4,5}. The balance a(i)+c(i)=1+4c(i+1), multiplied by 4^i and summed, telescopes to the repunit value. Equality of the functions recursively recovers all carries from c(0)=0, including a top digit equal to zero. The injection gives 2^m distinct partitions, and count_upper gives equality.

**Theorem 1.12 (Every entire natural tail has supremum one half).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.tail_supremum`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CoonsAdjacentGrowthRefutation.tail_supremum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all k,N with 5≤k≤6 and 2≤N, the EReal supremum of readout(k,4,n) over all natural n≥N equals the real number 1/2 embedded in EReal. The square bound and positive logarithms give 0≤readout≤1/2 for every n≥2. At repunit m, count=2^m and log(repunit m)≤(m+1)log 4, hence readout≥m/(2(m+1)). Given any real r<1/2 and any N≥2, choose natural m larger than both N and 2r/(1-2r). Then repunit m≥N and r<m/(2(m+1)). Density of real numbers in EReal proves the lower bound for that whole tail supremum, including the infinite endpoint possibilities. This proves finiteness rather than assuming it.

**Theorem 1.13 (Both adjacent exponents).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.exponent_eq_half`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CoonsAdjacentGrowthRefutation.exponent_eq_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k with 5≤k≤6, exponent k 4=(1/2 : Real), embedded in EReal. Every tail supremum equals that value, so its infimum does too; the set of permitted tails contains N=2.

**Theorem 1.14 (Literal refutation of the complete event).**

Lean statement: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/CoonsAdjacentGrowthRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/coons-strict-adjacent-multiplicity-growth` (refuted) by `D5/S1/Digit/CoonsAdjacentGrowthRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"coons-strict-adjacent-multiplicity-growth","declaration_gid":"D5/S1/Digit/CoonsAdjacentGrowthRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The theorem has literal type Not claim. Instantiate its putative universal strict inequality at ell=4,k=5, an admissible pair. The two exact exponents for k=5 and k+1=6 are both one half, contradicting strictness. The conclusion concerns the entire original universal event and uses the same radix on both sides.

## References

- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.Partitions`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.claim`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_positive`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_repunit`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.count_upper`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.exponent`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.exponent_eq_half`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.partitions_finite`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.readout`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.repunit`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.result`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.tail_supremum`
- Truth anchor: `D5/S1/Digit/CoonsAdjacentGrowthRefutation.weight`
