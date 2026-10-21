# A cardinal-ranking counterexample for modular integer complexity

## Abstract

Three unit bases modulo seventeen have greater inefficiency than base two.

Expressions are arbitrary binary trees with one kind of leaf and two operations, addition and multiplication. A recursion over all splits of a leaf budget enumerates exactly their possible values. At modulus 17, six leaves suffice for every residue in base 2, while bases 1, 3 and 16 each miss a residue at that budget. These three distinct unit bases contradict the bound of two in the displayed proposition. The comparison counts individual bases; bases 3 and 16 tie, so the conclusion does not address dense ranking by distinct inefficiency values. Exact inefficiencies and minimality are not separate theorems of this module.

**Definition 1.1 (Addition and multiplication expressions).**

$$\operatorname{Expr}:\operatorname{Type}; \operatorname{Expr}.\operatorname{x}:\operatorname{Expr}; \operatorname{Expr}.\operatorname{add}:\operatorname{Expr} \to \left(\operatorname{Expr} \to \operatorname{Expr}\right); \operatorname{Expr}.\operatorname{mul}:\operatorname{Expr} \to \left(\operatorname{Expr} \to \operatorname{Expr}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr` (`✓ std3`).

*Citation.* Aarya Kumar, Siyu Peng, and Vincent Tran (2022). *Integer Complexity Generalizations in Various Rings*. DOI: [10.48550/arXiv.2211.04379](https://doi.org/10.48550/arXiv.2211.04379). URL: <https://arxiv.org/abs/2211.04379v1>.

*Commentary.*

Page 1: “An expression refers to a sequence of x’s, which are joined together by +, ·, and () in the usual sense.” Expr has one leaf constructor x and the two binary constructors add and mul; parentheses specify the tree.

**Definition 1.2 (Number of occurrences of x).**

$$\forall e \in \operatorname{Expr},\; \forall f \in \operatorname{Expr},\; (\operatorname{Expr}.\operatorname{leaves}\left(\operatorname{Expr}.\operatorname{x}\right) = 1) \land ((\operatorname{Expr}.\operatorname{leaves}\left(\operatorname{Expr}.\operatorname{add}\left(e, f\right)\right) = \operatorname{Expr}.\operatorname{leaves}\left(e\right)+\operatorname{Expr}.\operatorname{leaves}\left(f\right)) \land (\operatorname{Expr}.\operatorname{leaves}\left(\operatorname{Expr}.\operatorname{mul}\left(e, f\right)\right) = \operatorname{Expr}.\operatorname{leaves}\left(e\right)+\operatorname{Expr}.\operatorname{leaves}\left(f\right)))$$

*Formalization.* `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.leaves` (`✓ std3`).

*Citation.* Aarya Kumar, Siyu Peng, and Vincent Tran (2022). *Integer Complexity Generalizations in Various Rings*. DOI: [10.48550/arXiv.2211.04379](https://doi.org/10.48550/arXiv.2211.04379). URL: <https://arxiv.org/abs/2211.04379v1>.

*Commentary.*

Page 1 defines complexity as “the smallest number of 1’s needed to write n as an equation using addition and multiplication.” Page 28 states “In this section, we shall denote the base as s.” Expr.leaves counts one occurrence at x and adds the counts at either binary operation.

**Definition 1.3 (Evaluation at a residue-ring base).**

$$\forall m \in \operatorname{Nat},\; \forall s \in \operatorname{ZMod}\left(m\right),\; \forall e \in \operatorname{Expr},\; \forall f \in \operatorname{Expr},\; (\operatorname{Expr}.\operatorname{eval}\left(s, \operatorname{Expr}.\operatorname{x}\right) = s) \land ((\operatorname{Expr}.\operatorname{eval}\left(s, \operatorname{Expr}.\operatorname{add}\left(e, f\right)\right) = \operatorname{Expr}.\operatorname{eval}\left(s, e\right)+\operatorname{Expr}.\operatorname{eval}\left(s, f\right)) \land (\operatorname{Expr}.\operatorname{eval}\left(s, \operatorname{Expr}.\operatorname{mul}\left(e, f\right)\right) = \operatorname{Expr}.\operatorname{eval}\left(s, e\right)\cdot\operatorname{Expr}.\operatorname{eval}\left(s, f\right)))$$

*Formalization.* `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.eval` (`✓ std3`).

*Citation.* Aarya Kumar, Siyu Peng, and Vincent Tran (2022). *Integer Complexity Generalizations in Various Rings*. DOI: [10.48550/arXiv.2211.04379](https://doi.org/10.48550/arXiv.2211.04379). URL: <https://arxiv.org/abs/2211.04379v1>.

*Commentary.*

Page 28: “In this section, we shall denote the base as s.” The leaf x evaluates to s in ZMod m; the two binary operations evaluate by ring addition and multiplication, with no subtraction or extra constants.

**Definition 1.4 (Least expression size).**

$$\forall m \in \operatorname{Nat},\; \forall s \in \operatorname{ZMod}\left(m\right),\; \forall r \in \operatorname{ZMod}\left(m\right),\; \operatorname{complexity}\left(s, r\right) = \operatorname{sInf}\left(\{n:\operatorname{Nat} \mid (\exists e \in \operatorname{Expr},\; (\operatorname{Expr}.\operatorname{leaves}\left(e\right) = n) \land (\operatorname{Expr}.\operatorname{eval}\left(s, e\right) = r))\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity` (`✓ std3`).

*Citation.* Aarya Kumar, Siyu Peng, and Vincent Tran (2022). *Integer Complexity Generalizations in Various Rings*. DOI: [10.48550/arXiv.2211.04379](https://doi.org/10.48550/arXiv.2211.04379). URL: <https://arxiv.org/abs/2211.04379v1>.

*Commentary.*

Page 1: “The complexity of a number n, denoted as ||n|| is equal to the smallest number of 1’s needed to write n as an equation using addition and multiplication.” Page 28 replaces the base by s. The set contains precisely the natural leaf counts of expressions evaluating to r. Its natural sInf is the minimum when r is reachable; the proof uses reachability explicitly when relating this infimum to a leaf budget.

**Definition 1.5 (Maximum residue complexity).**

$$\forall m \in \operatorname{Nat},\; [\operatorname{NeZero}\left(m\right)] \forall s \in \operatorname{ZMod}\left(m\right),\; \operatorname{inefficiency}\left(m, s\right) = \operatorname{Finset}.\operatorname{sup}\left((\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(\operatorname{ZMod}\left(m\right)\right)), (\operatorname{fun} r:\operatorname{ZMod}\left(m\right) \mapsto \operatorname{complexity}\left(s, r\right))\right)$$

*Formalization.* `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.inefficiency` (`✓ std3`).

*Citation.* Aarya Kumar, Siyu Peng, and Vincent Tran (2022). *Integer Complexity Generalizations in Various Rings*. DOI: [10.48550/arXiv.2211.04379](https://doi.org/10.48550/arXiv.2211.04379). URL: <https://arxiv.org/abs/2211.04379v1>.

*Commentary.*

Page 28: “The inefficiency E of an element, which will be used as a base, s ∈ ℤ/mℤ is defined as E(m, s) = max(‖0‖, ‖1‖, ‖2‖, …, ‖m − 1‖). In other words, the maximum complexity of an element of ℤ/mℤ with x = s.” Finset.univ ranges over all residues and Finset.sup takes their maximum.

**Definition 1.6 (Conjecture 4.4 with cardinal ranking).**

$$(\operatorname{claim}) \Leftrightarrow (\forall m \in \operatorname{Nat},\; [\operatorname{NeZero}\left(m\right)] (3 \le m) \Rightarrow ((\operatorname{Odd}\left(m\right)) \Rightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} s:\operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right) \mapsto \operatorname{inefficiency}\left(m, (2:\operatorname{ZMod}\left(m\right))\right) < \operatorname{inefficiency}\left(m, (s:\operatorname{ZMod}\left(m\right))\right)), (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(\operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right)\right))\right)\right) \le 2)))$$

*Formalization.* `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.claim` (`✓ std3`).

*Citation.* Aarya Kumar, Siyu Peng, and Vincent Tran (2022). *Integer Complexity Generalizations in Various Rings*. DOI: [10.48550/arXiv.2211.04379](https://doi.org/10.48550/arXiv.2211.04379). URL: <https://arxiv.org/abs/2211.04379v1>.

*Commentary.*

Conjecture 4.4, page 29: “E(m, 2) is the third most inefficient for odd m.” The proposition quantifies over odd natural m ≥ 3 with NeZero m, and counts units s for which inefficiency m 2 < inefficiency m s. It requires that count to be at most two. This is the individual-base cardinal interpretation of third place. The paper does not specify a tie rule; dense ranking by distinct values is outside this proposition. Page 28 restricts bases that span the ring by the observation “The representations with base s span every element of ℤ/mℤ if and only if s ∈ Uₘ.”

**Theorem 1.7 (Refutation by three strictly larger inefficiencies).**

$$\neg (\forall m \in \operatorname{Nat},\; [\operatorname{NeZero}\left(m\right)] (3 \le m) \Rightarrow ((\operatorname{Odd}\left(m\right)) \Rightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} s:\operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right) \mapsto \operatorname{inefficiency}\left(m, (2:\operatorname{ZMod}\left(m\right))\right) < \operatorname{inefficiency}\left(m, (s:\operatorname{ZMod}\left(m\right))\right)), (\operatorname{Finset}.\operatorname{univ}:\operatorname{Finset}\left(\operatorname{Units}\left(\operatorname{ZMod}\left(m\right)\right)\right))\right)\right) \le 2)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result` (`✓ std3`). ∎

*Resolves.* `Problems/kumar-peng-tran-2022-modular-integer-complexity-conjecture-4-4` (refuted) by `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kumar-peng-tran-2022-modular-integer-complexity-conjecture-4-4","declaration_gid":"D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aarya Kumar, Siyu Peng, and Vincent Tran (2022). *Integer Complexity Generalizations in Various Rings*. DOI: [10.48550/arXiv.2211.04379](https://doi.org/10.48550/arXiv.2211.04379). URL: <https://arxiv.org/abs/2211.04379v1>.

*Commentary.*

At m = 17, inefficiency 17 2 ≤ 6, whereas inefficiency 17 1, inefficiency 17 3 and inefficiency 17 16 are greater than 6. The units represented by 1, 3 and 16 form a three-element subset of the filtered set. Monotonicity of finite cardinality contradicts its proposed bound.

## References

- Truth anchor: `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.Expr`
- Truth anchor: `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.claim`
- Truth anchor: `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.complexity`
- Truth anchor: `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.eval`
- Truth anchor: `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.inefficiency`
- Truth anchor: `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.leaves`
- Truth anchor: `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result`
