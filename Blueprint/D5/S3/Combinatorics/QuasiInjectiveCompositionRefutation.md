# Quasi-Injectivity Is Not Closed Under Composition

## Abstract

Squaring and collapsing the squares are quasi-injective while their composite is not.

**Definition 1.1 (Quasi-injectivity).**

$$\forall f \in \mathrm{Nat} \to \mathrm{Nat},\; (\operatorname{QuasiInjective}\left(f\right)) \Leftrightarrow (\forall a \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; (1 \le a) \Rightarrow ((1 \le b) \Rightarrow ((\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\operatorname{f}\left(a \cdot n\right) = \operatorname{f}\left(b \cdot n\right))) \Rightarrow (a = b))))$$

*Formalization.* `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.QuasiInjective` (`✓ std3`).

*Citation.* Prapanpong Pongsriiam (2021). *Quasi-Injectivity of Some Arithmetic Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf>.

*Commentary.*

Definition 1 of the source reads verbatim: "We call a function f : N to C a quasi-injective function if for all a, b in N, the condition f(an) = f(bn) for all n in N implies a = b." The source works with the positive integers, so the quantifiers over a, b and n carry positivity. The condition is weaker than injectivity: it only asks that the whole family of values on the multiples of a determine a.

**Definition 1.2 (Squaring).**

$$\forall n \in \mathrm{Nat},\; \operatorname{square}\left(n\right) = n \cdot n$$

*Formalization.* `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.square` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inner factor of the counterexample. It is injective, hence quasi-injective, and it is completely multiplicative; it is not surjective, which is why it does not meet the sufficient condition the source names.

**Definition 1.3 (Collapsing the squares).**

$$\forall n \in \mathrm{Nat},\; ((\operatorname{sqrt}\left(n\right) \cdot \operatorname{sqrt}\left(n\right) = n) \Rightarrow (\operatorname{collapse}\left(n\right) = 1)) \land ((\neg (\operatorname{sqrt}\left(n\right) \cdot \operatorname{sqrt}\left(n\right) = n)) \Rightarrow (\operatorname{collapse}\left(n\right) = n))$$

*Formalization.* `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.collapse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outer factor of the counterexample: every perfect square is sent to one and every other value is left alone. The test is written with the natural-number square root, which squares back to the input exactly on the perfect squares.

**Definition 1.4 (The question asked of composites).**

$$(claim) \Leftrightarrow (\forall f \in \mathrm{Nat} \to \mathrm{Nat},\; \forall g \in \mathrm{Nat} \to \mathrm{Nat},\; (\operatorname{QuasiInjective}\left(f\right)) \Rightarrow ((\operatorname{QuasiInjective}\left(g\right)) \Rightarrow (\operatorname{QuasiInjective}\left(f \circ g\right))))$$

*Formalization.* `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.claim` (`✓ std3`).

*Citation.* Prapanpong Pongsriiam (2021). *Quasi-Injectivity of Some Arithmetic Functions*. URL: <https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf>.

*Commentary.*

The first question of Question 19 of the source reads verbatim: "Suppose f and g are quasi-injective. Is the composition f o g quasi-injective?" The statement displayed here is the affirmative reading. The source adds that an obvious sufficient condition for the composite to be quasi-injective is that g is both surjective and completely multiplicative, and asks whether a weaker condition exists; that classification question is separate and is not addressed here.

**Theorem 1.5 (Composites need not be quasi-injective).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/quasi-injective-composition-refutation` (refuted) by `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"quasi-injective-composition-refutation","declaration_gid":"D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The answer is no. Squaring is quasi-injective because agreement at n equal to one already gives a squared equal to b squared. Collapsing the squares is quasi-injective for a different reason: given distinct positive a and b, choose a prime p larger than their product, so p divides neither. If a times p were a square, say k times k, then p would divide k times k and hence k, so p squared would divide a times p and p would divide a, which it does not; so a times p is not a square, and neither is b times p, whence the two values are a times p and b times p and they differ. But the composite sends every n to the collapse of n times n, which is one; so it agrees on the multiples of one and on the multiples of two while one and two differ, and it is not quasi-injective.

## References

- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.QuasiInjective`
- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.collapse`
- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.square`
