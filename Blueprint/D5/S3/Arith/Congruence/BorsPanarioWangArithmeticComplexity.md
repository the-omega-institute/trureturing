# Arithmetic complexity of singleton partitions

## Abstract

The arithmetic complexity of singleton partitions has a positive normalized lower limit.

A family of congruences separates the residues modulo m when no two standard representatives have the same truth values for all its tests. For each prime p dividing m, tests whose moduli lack the full p-power are constant on the fibres modulo m/p. Representatives outside the remaining tests inject into those fibres. Counting these representatives and summing prime-power charges bounds the sum of the prime-power totients by the number of tests. A finite least-common-multiple estimate and Chebyshev's bound then give a normalized ratio at least 1/64 whenever log m is at least 64. All logarithms are real natural logarithms; the lower limit is in EReal, with the natural index tending to infinity.

**Definition 1.1 (Congruences with modulus dividing m).**

$$\forall m \in \operatorname{Nat},\; \operatorname{MCongruence}\left(m\right):\operatorname{Type} \{a:\operatorname{Nat}; b:\operatorname{Int}; 1 \le a; a \mid m\}$$

*Formalization.* `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.MCongruence` (`✓ std3`).

*Citation.* Alexander Bors, Daniel Panario, and Qiang Wang (2023). *Functional graphs of generalized cyclotomic mappings of finite fields*. DOI: [10.4171/MEMS/23](https://doi.org/10.4171/MEMS/23). URL: <https://arxiv.org/abs/2304.00181v1>.

*Commentary.*

Pages 10-11: "For a given positive integer m, we define the notion of an m-(in)congruence to be an (in)congruence of the form ν(x ≡ b (mod a)) where ν ∈ {∅, ¬} is a “logical sign”, and a, b are integers with a ≥ 1 and a | m." The record stores the positive modulus a as a natural number, b as an integer, and proofs of 1 ≤ a and a ∣ m. Positive integer moduli and positive natural moduli describe the same congruences. The displayed braces list its fields.

**Definition 1.2 (Truth of a congruence).**

$$\forall m \in \operatorname{Nat},\; \forall c \in \operatorname{MCongruence}\left(m\right),\; \forall x \in \operatorname{Nat},\; (\operatorname{MCongruence}.\operatorname{Holds}\left(c, x\right)) \Leftrightarrow (\operatorname{Int}.\operatorname{ModEq}\left((\operatorname{MCongruence}.\operatorname{a}\left(c\right):\operatorname{Int}), (x:\operatorname{Int}), \operatorname{MCongruence}.\operatorname{b}\left(c\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.Holds` (`✓ std3`).

*Citation.* Alexander Bors, Daniel Panario, and Qiang Wang (2023). *Functional graphs of generalized cyclotomic mappings of finite fields*. DOI: [10.4171/MEMS/23](https://doi.org/10.4171/MEMS/23). URL: <https://arxiv.org/abs/2304.00181v1>.

*Commentary.*

Page 10: "We identify the elements of Z/mZ with their standard representatives in {0, 1, . . . , m − 1}." Holds evaluates x ≡ b (mod a) by Int.ModEq, with the natural representative and modulus cast to integers.

**Definition 1.3 (Separation of standard representatives).**

$$\forall m \in \operatorname{Nat},\; \forall K \in \operatorname{Nat},\; \forall c \in \operatorname{Fin}\left(K\right) \to \operatorname{MCongruence}\left(m\right),\; (\operatorname{SpansTrivial}\left(c\right)) \Leftrightarrow (\forall x \in \operatorname{Nat},\; \forall y \in \operatorname{Nat},\; (x < m) \Rightarrow ((y < m) \Rightarrow ((\forall j \in \operatorname{Fin}\left(K\right),\; (\operatorname{MCongruence}.\operatorname{Holds}\left(c\left(j\right), x\right)) \Leftrightarrow (\operatorname{MCongruence}.\operatorname{Holds}\left(c\left(j\right), y\right))) \Rightarrow (x = y))))$$

*Formalization.* `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.SpansTrivial` (`✓ std3`).

*Citation.* Alexander Bors, Daniel Panario, and Qiang Wang (2023). *Functional graphs of generalized cyclotomic mappings of finite fields*. DOI: [10.4171/MEMS/23](https://doi.org/10.4171/MEMS/23). URL: <https://arxiv.org/abs/2304.00181v1>.

*Commentary.*

Definition 1.5(1), pages 10-11: "There is a unique partition of Z/mZ, which we denote by P(x ≡ b_j (mod a_j) : j = 1, 2, . . . , K), such that each block of this partition is the solution set modulo m of a system of m-CCs of the form" ν_1(x ≡ b_1 (mod a_1)), …, ν_K(x ≡ b_K (mod a_K)). Section 6.3, page 188, calls T_m "the trivial partition T_m of Z/mZ, all of whose blocks are singletons". Thus the partition is T_m precisely when equality of all test truth values forces equality of the two representatives. Fin K indexes exactly K tests.

**Definition 1.4 (Minimum number of separating congruences).**

$$\forall m \in \operatorname{Nat},\; \operatorname{acTrivial}\left(m\right) = \operatorname{sInf}\left(\{K:\operatorname{Nat} \mid (\exists c \in \operatorname{Fin}\left(K\right) \to \operatorname{MCongruence}\left(m\right),\; \operatorname{SpansTrivial}\left(c\right))\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.acTrivial` (`✓ std3`).

*Citation.* Alexander Bors, Daniel Panario, and Qiang Wang (2023). *Functional graphs of generalized cyclotomic mappings of finite fields*. DOI: [10.4171/MEMS/23](https://doi.org/10.4171/MEMS/23). URL: <https://arxiv.org/abs/2304.00181v1>.

*Commentary.*

Definition 1.5(3), page 11: "When P is an arithmetic partition of Z/mZ, then the smallest value of K ∈ N_0 such that P is spanned by K suitably chosen m-congruences is called the (arithmetic) complexity of P, written AC(P)." The natural-number infimum is taken over exactly the separating families. This set is nonempty for positive m, since the congruences x ≡ j (mod m) separate all standard representatives.

**Definition 1.5 (Affirmative answer to Question 6.3.1).**

$$(claim) \Leftrightarrow (0 < \operatorname{Filter}.\operatorname{liminf}\left((\operatorname{fun} m:\operatorname{Nat} \mapsto ((\frac{(\operatorname{acTrivial}\left(m\right):\operatorname{Real})}{\frac{\operatorname{Real}.\operatorname{log}\left((m:\operatorname{Real})\right)^{2}}{\operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left((m:\operatorname{Real})\right)\right)}}:\operatorname{Real}):\operatorname{EReal})), \operatorname{Filter}.\operatorname{atTop}\right))$$

*Formalization.* `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.claim` (`✓ std3`).

*Citation.* Alexander Bors, Daniel Panario, and Qiang Wang (2023). *Functional graphs of generalized cyclotomic mappings of finite fields*. DOI: [10.4171/MEMS/23](https://doi.org/10.4171/MEMS/23). URL: <https://arxiv.org/abs/2304.00181v1>.

*Commentary.*

Question 6.3.1, page 189: "Is it true that lim inf_{m→∞} AC(T_m)/(log² m/log log m) > 0?" The displayed proposition is the affirmative answer, with acTrivial m for AC(T_m), real division and coercion of the normalized ratio into EReal before Filter.liminf.

**Theorem 1.6 (Positive normalized lower limit).**

$$0 < \operatorname{Filter}.\operatorname{liminf}\left((\operatorname{fun} m:\operatorname{Nat} \mapsto ((\frac{(\operatorname{acTrivial}\left(m\right):\operatorname{Real})}{\frac{\operatorname{Real}.\operatorname{log}\left((m:\operatorname{Real})\right)^{2}}{\operatorname{Real}.\operatorname{log}\left(\operatorname{Real}.\operatorname{log}\left((m:\operatorname{Real})\right)\right)}}:\operatorname{Real}):\operatorname{EReal})), \operatorname{Filter}.\operatorname{atTop}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Bors, Daniel Panario, and Qiang Wang (2023). *Functional graphs of generalized cyclotomic mappings of finite fields*. DOI: [10.4171/MEMS/23](https://doi.org/10.4171/MEMS/23). URL: <https://arxiv.org/abs/2304.00181v1>.

*Commentary.*

The prime-power separation estimate and Chebyshev's bound yield the eventual real lower bound 1/64. Its positive image in EReal is a lower bound for the lower limit, proving the full displayed proposition.

## References

- Truth anchor: `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.Holds`
- Truth anchor: `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.MCongruence`
- Truth anchor: `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.SpansTrivial`
- Truth anchor: `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.acTrivial`
- Truth anchor: `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.claim`
- Truth anchor: `D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity.result`
