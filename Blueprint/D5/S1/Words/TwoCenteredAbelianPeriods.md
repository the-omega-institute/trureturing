# Two centered abelian periods

## Abstract

Two centered abelian period lengths force ordinary periodicity.

**Definition 1.1 (Centered abelian powers).**

$$\forall r \in Nat,\; \forall w \in Int \to Fin\left(r\right),\; \forall k \in Nat,\; \forall l \in Nat,\; \forall i \in Int,\; (CentralAbelianPower\left(w, k, l, i\right)) \Leftrightarrow ((0 < l) \land (\forall j \in Nat,\; (j < 2 \cdot k) \Rightarrow (\forall a \in Fin\left(r\right),\; \operatorname{AbelianBorderQuestionDefs.letterCount}\left(\operatorname{List.ofFn}\left(\operatorname{fun} (t: Fin\left(l\right)) \mapsto w\left(i - (l: Int) \cdot (k: Int) + 1 + (j: Int) \cdot (l: Int) + (val\left(t\right): Int)\right)\right), a\right) = \operatorname{AbelianBorderQuestionDefs.letterCount}\left(\operatorname{List.ofFn}\left(\operatorname{fun} (t: Fin\left(l\right)) \mapsto w\left(i - (l: Int) \cdot (k: Int) + 1 + (val\left(t\right): Int)\right)\right), a\right))))$$

*Formalization.* `D5/S1/Words/TwoCenteredAbelianPeriods.CentralAbelianPower` (`✓ std3`).

*Citation.* S. Avgustinovich, J. Karhumäki and S. Puzynina (2012). *On abelian versions of critical factorization theorem*. DOI: [10.1051/ita/2011121](https://doi.org/10.1051/ita/2011121). URL: <https://www.numdam.org/item/ITA_2012__46_1_3_0/>.

*Commentary.*

Section 2.2, p. 6: “Two words u and v in Σ∗ are abelian equivalent if and only if |u|ₐ = |v|ₐ for all a ∈ Σ.” “An abelian k-power is a non-empty word of the form u = v₁v₂…v_k where the words vᵢ are pairwise abelian equivalent. In this case we refer to |v₁| as the length of an abelian period of u (or briefly period).” “Let w be a biinfinite word over an alphabet Σ. For integer i, by a position i in a word w we mean a position between wᵢ and wᵢ₊₁.” “for every i there exists l′ ≤ l such that w_{i−l′k+1} … w_{i+l′k} is an abelian 2k-power.” The fixed-length predicate displays this centered factor at a specified period length l. The integer-indexed word takes values in Fin r. The factor from i−lk+1 through i+lk consists of 2k nonempty blocks of length l. Each block has the same letterCount as the first block. All arithmetic in the starting position is integer arithmetic.

**Definition 1.2 (Ordinary periodicity).**

$$\forall r \in Nat,\; \forall w \in Int \to Fin\left(r\right),\; (Periodic\left(w\right)) \Leftrightarrow (\exists p \in Nat,\; (0 < p) \land (\forall n \in Int,\; w\left(n + (p: Int)\right) = w\left(n\right)))$$

*Formalization.* `D5/S1/Words/TwoCenteredAbelianPeriods.Periodic` (`✓ std3`).

*Citation.* S. Avgustinovich, J. Karhumäki and S. Puzynina (2012). *On abelian versions of critical factorization theorem*. DOI: [10.1051/ita/2011121](https://doi.org/10.1051/ita/2011121). URL: <https://www.numdam.org/item/ITA_2012__46_1_3_0/>.

*Commentary.*

Section 2.1, p. 4: “We say that a biinfinite word w is periodic, if there exists a finite word v such that w = v^ℤ.” The positive-period encoding uses a natural period p: w(n+p)=w(n) for every integer n.

**Definition 1.3 (The negative answer to Open problem 6.2).**

$$(claim) \Leftrightarrow (\forall k \in Nat,\; (1 \le k) \Rightarrow (\forall r \in Nat,\; \forall w \in Int \to Fin\left(r\right),\; \forall l1 \in Nat,\; \forall l2 \in Nat,\; (\forall i \in Int,\; (CentralAbelianPower\left(w, k, l1, i\right)) \lor (CentralAbelianPower\left(w, k, l2, i\right))) \Rightarrow (Periodic\left(w\right))))$$

*Formalization.* `D5/S1/Words/TwoCenteredAbelianPeriods.claim` (`✓ std3`).

*Citation.* S. Avgustinovich, J. Karhumäki and S. Puzynina (2012). *On abelian versions of critical factorization theorem*. DOI: [10.1051/ita/2011121](https://doi.org/10.1051/ita/2011121). URL: <https://www.numdam.org/item/ITA_2012__46_1_3_0/>.

*Commentary.*

Open problem 6.2, p. 14: “Let k be an integer. Does there exist a non-periodic word w and integers l₁, l₂, such that w contains a central abelian 2k-power of length l₁ or l₂ at every position?” “Notice that the construction from Theorem 3.2 gives an example of such a word using three periods. One period trivially implies periodicity. So two periods is an open question.” The proposition answers no for every positive k and every finite alphabet Fin r, with integer-indexed words and positive block lengths.

**Theorem 1.4 (Two lengths force periodicity).**

$$\forall k \in Nat,\; (1 \le k) \Rightarrow (\forall r \in Nat,\; \forall w \in Int \to Fin\left(r\right),\; \forall l1 \in Nat,\; \forall l2 \in Nat,\; (\forall i \in Int,\; (CentralAbelianPower\left(w, k, l1, i\right)) \lor (CentralAbelianPower\left(w, k, l2, i\right))) \Rightarrow (Periodic\left(w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoCenteredAbelianPeriods.result` (`✓ std3`). ∎

*Resolves.* `Problems/akp-2012-two-centered-abelian-periods` (proved) by `D5/S1/Words/TwoCenteredAbelianPeriods.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"akp-2012-two-centered-abelian-periods","declaration_gid":"D5/S1/Words/TwoCenteredAbelianPeriods.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Avgustinovich, J. Karhumäki and S. Puzynina (2012). *On abelian versions of critical factorization theorem*. DOI: [10.1051/ita/2011121](https://doi.org/10.1051/ita/2011121). URL: <https://www.numdam.org/item/ITA_2012__46_1_3_0/>.

*Commentary.*

Every word satisfying the two-length alternative is periodic. The middle two blocks reduce each centered power to an abelian square. For each letter, the mixed forward difference of its cumulative count vanishes: an exact square identity makes a bounded integer flux antitone, and a bounded coboundary on both tails forces the flux to be zero. When both lengths are positive, the proof gives their least common multiple as a period. A zero length is excluded by the nonempty-block condition. No earlier answer was identified in the bounded literature screen; completeness of that screen remains unverified.

## References

- Truth anchor: `D5/S1/Words/TwoCenteredAbelianPeriods.CentralAbelianPower`
- Truth anchor: `D5/S1/Words/TwoCenteredAbelianPeriods.Periodic`
- Truth anchor: `D5/S1/Words/TwoCenteredAbelianPeriods.claim`
- Truth anchor: `D5/S1/Words/TwoCenteredAbelianPeriods.result`
- Dependency: [D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs](AbelianBorders/AbelianBorderQuestionDefs.md)
