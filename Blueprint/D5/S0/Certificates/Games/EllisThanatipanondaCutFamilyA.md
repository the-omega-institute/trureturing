# Ellis–Thanatipanonda Conjecture 1: Family A

## Abstract

Every Family A cut-set has nim-sequence (0, 1)^c (+2).

**Definition 1.1 (The nim-sequence of cut).**

$$\forall C \in \operatorname{Set}\left(Nat\right),\; \forall n \in Nat,\; \operatorname{G}\left(C, n\right) = \operatorname{mex}\left(\{g | \exists d \in Nat,\; (d \in C) \land (\exists o \in \operatorname{Fin}\left(d + 1\right) \to Nat,\; (\forall i \in \operatorname{Fin}\left(d + 1\right),\; 1 \le o\left(i\right)) \land ((\sum_{i} o\left(i\right) = n) \land (g = \operatorname{List}.\operatorname{foldr}\left(\operatorname{Nat}.\operatorname{xor}, 0, \operatorname{List}.\operatorname{ofFn}\left((fun (i: \operatorname{Fin}\left(d + 1\right)) \mapsto (if (o\left(i\right) < n) then \operatorname{G}\left(C, o\left(i\right)\right) else 0))\right)\right))))\}\right)$$

*Formalization.* `D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.G` (`✓ std3`).

*Citation.* Paul Ellis; Thotsaporn Aek Thanatipanonda (2022). *The Arithmetic-Periodicity of cut for C = {1, 2c}*. DOI: [10.1016/j.dam.2022.08.027](https://doi.org/10.1016/j.dam.2022.08.027). URL: <https://arxiv.org/abs/2203.02457v1>.

*Commentary.*

Page 2: “Fixing a cut-set C, we write G(n) to denote the nim-value of the position of cut with a single pile of size n. Then G(n) is called the nim-sequence of the game with cut-set C.” Definition 1, page 2: “Given a pile of size n, an option O_n is a sequence of piles obtainable via a single legal move on that pile. In other words, O_n is a particular partition of n with d + 1 parts for some d ∈ C. Formally, O_n = (h_0, h_1, ..., h_d) where 1 ≤ h_i and h_0 + h_1 + · · · + h_d = n.” Here o : Fin (d + 1) → Nat lists the positive parts. List.ofFn lists their recursively computed values and List.foldr Nat.xor 0 forms their nim-sum. The existing mex is sInf of the complement. For d ≥ 1 each part is smaller than n, so the recursion guard is inactive on legal Family A options. The guarded formula also defines G at zero and for arbitrary cut-sets.

**Definition 1.2 (The Family A conjecture).**

$$claim = (\forall X \in \operatorname{Set}\left(Nat\right),\; \forall Y \in \operatorname{Set}\left(Nat\right),\; (\operatorname{Set}.\operatorname{Nonempty}\left(X\right)) \Rightarrow ((\forall x \in Nat,\; (x \in X) \Rightarrow ((\operatorname{Even}\left(x\right)) \land (4 \le x))) \Rightarrow (((Y = \emptyset) \lor ((\operatorname{Set}.\operatorname{Nonempty}\left(Y\right)) \land (\forall y \in Nat,\; (y \in Y) \Rightarrow ((\operatorname{Odd}\left(y\right)) \land (5 \le y))))) \Rightarrow (\forall c \in Nat,\; (2 \cdot c = \operatorname{sInf}\left(X\right)) \Rightarrow (\forall n \in Nat,\; (1 \le n) \Rightarrow (\operatorname{G}\left((\left\{1, 3\right\} \cup X) \cup Y, n\right) = 2 \cdot \operatorname{Nat}.\operatorname{div}\left(n - 1, 2 \cdot c\right) + \operatorname{Nat}.\operatorname{mod}\left(n - 1, 2\right)))))))$$

*Formalization.* `D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.claim` (`✓ std3`).

*Citation.* Paul Ellis; Thotsaporn Aek Thanatipanonda (2022). *The Arithmetic-Periodicity of cut for C = {1, 2c}*. DOI: [10.1016/j.dam.2022.08.027](https://doi.org/10.1016/j.dam.2022.08.027). URL: <https://arxiv.org/abs/2203.02457v1>.

*Commentary.*

Section 7, page 18: “Let X to be a non-empty set of even numbers, each of which is at least 4. Let Y to be a non-empty set of odd numbers, each of which is at least 5. Let x = 2c and y be the smallest elements of X and Y, respectively.” “Family A: C = {1, 3} ∪ X, or C = {1, 3} ∪ X ∪ Y.” Conjecture 1, page 18: “The nim-sequence for all games of cut in this family are all precisely (0, 1)^c (+2).” The first alternative uses Y = ∅; the second uses nonempty Y. The least element of X is sInf X = 2c. Page 3: “The notation (0, 1)^3 (+2), for example, denotes the sequence 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 4, 5, 4, 5, 4, 5, . . ..” Thus n starts at 1, subtraction is truncated natural subtraction, Nat.div is integer division and Nat.mod is remainder. Arbitrary sets X and Y are allowed; only cuts smaller than n produce options.

**Theorem 1.3 (The conjectured sequence for every Family A cut-set).**

$$\forall X \in \operatorname{Set}\left(Nat\right),\; \forall Y \in \operatorname{Set}\left(Nat\right),\; (\operatorname{Set}.\operatorname{Nonempty}\left(X\right)) \Rightarrow ((\forall x \in Nat,\; (x \in X) \Rightarrow ((\operatorname{Even}\left(x\right)) \land (4 \le x))) \Rightarrow (((Y = \emptyset) \lor ((\operatorname{Set}.\operatorname{Nonempty}\left(Y\right)) \land (\forall y \in Nat,\; (y \in Y) \Rightarrow ((\operatorname{Odd}\left(y\right)) \land (5 \le y))))) \Rightarrow (\forall c \in Nat,\; (2 \cdot c = \operatorname{sInf}\left(X\right)) \Rightarrow (\forall n \in Nat,\; (1 \le n) \Rightarrow (\operatorname{G}\left((\left\{1, 3\right\} \cup X) \cup Y, n\right) = 2 \cdot \operatorname{Nat}.\operatorname{div}\left(n - 1, 2 \cdot c\right) + \operatorname{Nat}.\operatorname{mod}\left(n - 1, 2\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.result` (`✓ std3`). ∎

*Resolves.* `Problems/ellis-thanatipanonda-2022-cut-family-a-conjecture-1` (proved) by `D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ellis-thanatipanonda-2022-cut-family-a-conjecture-1","declaration_gid":"D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul Ellis; Thotsaporn Aek Thanatipanonda (2022). *The Arithmetic-Periodicity of cut for C = {1, 2c}*. DOI: [10.1016/j.dam.2022.08.027](https://doi.org/10.1016/j.dam.2022.08.027). URL: <https://arxiv.org/abs/2203.02457v1>.

*Commentary.*

Strong induction on the pile size replaces the values of all option parts by the stated formula. An odd cut gives an even number of parts: the low bit of their nim-sum is opposite to the low bit of G(n). An even cut is at least 2c; the sum of the parts' quotient terms is strictly below the quotient term of n. The xor of natural numbers is at most their sum, so this also excludes the proposed value. Every smaller value is attained using only cuts 1, 3 and 2c: two parts, four parts with an equal pair, or a leading part followed by 2c equal parts. The minimum excluded value is therefore the proposed one. Proposition 8 of Dailly–Duchêne–Larsson–Paris already gives C = {1, 3, 2c}; this proof allows every extra cut in Family A.

## References

- Truth anchor: `D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.G`
- Truth anchor: `D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.claim`
- Truth anchor: `D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.result`
- Dependency: [D5/S0/Certificates/Games/AbukuEnforceNimberDomination](AbukuEnforceNimberDomination.md)
