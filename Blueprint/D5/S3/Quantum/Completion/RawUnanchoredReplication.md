# Raw unanchored replication

## Abstract

Literal synchronous arrays and countable unit normal forms preserve ordered comparisons while removing unit drift.

M is an arbitrary genuine unital magma, U is any self-map, and c is finite, real, nonnegative and zero on the diagonal. RawCost requires the full four-variable identity c(au,bv)+c(aUu,bUv)+c(aU(Uu),bU(Uv))=3c(a,b)+3c(u,v). It requires no associativity, commutativity, symmetry, triangle inequality, positivity of a bilinear form, surjectivity of U, or equation U(1)=1.

**Theorem 1.1 (Actual finite-depth supplier).**

$$(\forall M: Type, [\operatorname{MulOneClass}\left(M\right)] (\forall U: M \to M, (\forall c: M \to M \to \mathbb{R}, (\operatorname{RawCost}\left(U, c\right) \Rightarrow (\forall N: \mathbb{N}, (0 < N \Rightarrow (\operatorname{RawCost}\left(\operatorname{arrayMarker}\left(U\right), \operatorname{arrayCost}\left(c, N\right)\right) \land (\operatorname{omega}\left(\operatorname{arrayMarker}\left(U\right), \operatorname{arrayCost}\left(c, N\right)\right) = \frac{\operatorname{omega}\left(U, c\right)}{N} \land ((\forall a: M, (\forall b: M, \operatorname{arrayCost}\left(c, N, \operatorname{gamma}\left(U, N, a\right), \operatorname{gamma}\left(U, N, b\right)\right) = \operatorname{c}\left(a, b\right))) \land ((\forall a: M, (\operatorname{arrayCost}\left(c, N, \operatorname{gamma}\left(U, N, a\right), 1\right) \le ((3 \cdot \operatorname{c}\left(a, 1\right))+\frac{(3 \cdot \operatorname{omega}\left(U, c\right))}{N}) \land \operatorname{arrayCost}\left(c, N, 1, \operatorname{gamma}\left(U, N, a\right)\right) \le ((3 \cdot \operatorname{c}\left(1, a\right))+\frac{(3 \cdot \operatorname{omega}\left(U, c\right))}{N}))) \land (\forall x: M, (\forall n: \mathbb{N}, (\operatorname{c}\left(\operatorname{iterate}\left(U, n, x\right), 1\right)+\operatorname{c}\left(1, \operatorname{iterate}\left(U, n, x\right)\right)) \le ((9 \cdot (\operatorname{c}\left(x, 1\right)+\operatorname{c}\left(1, x\right)))+(24 \cdot \operatorname{omega}\left(U, c\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_replication` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sigma(N) is literally Fin N -> Fin 3. The cost divides the sum over all coordinate arrays by N*3^N. Product and marker act coordinatewise, and the actual unit is the constant old-unit array. The right comb applies a*U^k(inner) at each node. Every source at a coordinate uses the same phase e=(3-s mod 3) mod 3, where s is the sum of that coordinate's phase choices. Thus 3 divides s+e. The corrected old-unit source is U^(s+e)(1), which need not be the actual array unit. The theorem retains every ordered comparison, both actual-unit budgets, the complete raw law and exact unit-budget scaling.

The raw recurrence at the two true units is nonnegative, so ThreeWayBalance.nonneg_recurrence_constant supplies synchronous marker isometry. Subtracting consecutive balance laws gives period three for simultaneous right multiplication by unit-orbit markers. Two further balance instances give the unit-orbit budget. These facts provide unit control after phase completion. The synchronous right-comb sum is proved by induction over the literal coordinate arrays, preserving multiplicity, bracketing and order.

**Theorem 1.2 (Uniform budgets on actual unit normal forms).**

$$(\forall M: Type, [\operatorname{MulOneClass}\left(M\right)] (\forall U: M \to M, (\forall c: M \to M \to \mathbb{R}, (\forall A: Type, (\forall f: A \to M, (\operatorname{RawCost}\left(U, c\right) \Rightarrow (\operatorname{budget}\left(f, U, c, 1\right) = 0 \land ((\forall a: A, \operatorname{budget}\left(f, U, c, \operatorname{source}\left(a\right)\right) = ((3 \cdot (\operatorname{c}\left(\operatorname{f}\left(a\right), 1\right)+\operatorname{c}\left(1, \operatorname{f}\left(a\right)\right)))+(6 \cdot \operatorname{omega}\left(U, c\right)))) \land ((\forall s: \operatorname{Term}\left(A\right), \operatorname{budget}\left(f, U, c, \operatorname{termMarker}\left(s\right)\right) = ((9 \cdot \operatorname{budget}\left(f, U, c, s\right))+(24 \cdot \operatorname{omega}\left(U, c\right)))) \land ((\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), \operatorname{budget}\left(f, U, c, (s \cdot t)\right) \le (3 \cdot (\operatorname{budget}\left(f, U, c, s\right)+\operatorname{budget}\left(f, U, c, t\right))))) \land (\forall N: \mathbb{N}, (0 < N \Rightarrow (\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), ((\operatorname{modelCost}\left(f, U, c, N, s, 1\right)+\operatorname{modelCost}\left(f, U, c, N, 1, s\right)) \le \operatorname{budget}\left(f, U, c, s\right) \land \operatorname{modelCost}\left(f, U, c, N, s, t\right) \le (3 \cdot (\operatorname{budget}\left(f, U, c, s\right)+\operatorname{budget}\left(f, U, c, t\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawUnanchoredReplication.normal_form_budgets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same budget controls all actual evaluation depths. Smart multiplication first removes a unit factor; nonnegativity then gives B(st)<=3(B(s)+B(t)) even in those reduced cases. At a nonunit product the equality follows from the ordered constructor. These bounds supply the compact intervals used by the common all-pair extraction.

**Theorem 1.3 (A common limit on the free unital U terms).**

$$(\forall M: Type, [\operatorname{MulOneClass}\left(M\right)] (\forall U: M \to M, (\forall c: M \to M \to \mathbb{R}, (\forall A: Type, [\operatorname{Finite}\left(A\right)] (\forall f: A \to M, (\operatorname{RawCost}\left(U, c\right) \Rightarrow (\exists d: \operatorname{Term}\left(A\right) \to \operatorname{Term}\left(A\right) \to \mathbb{R}, (\exists rho: \mathbb{N} \to \mathbb{N}, (\operatorname{StrictMono}\left(rho\right) \land ((\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), \operatorname{Tendsto}\left(\lambda l: \mathbb{N} \mapsto \operatorname{modelCost}\left(f, U, c, (\operatorname{rho}\left(l\right)+1), s, t\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{d}\left(s, t\right)\right)\right))) \land (\operatorname{RawCost}\left(\operatorname{termMarker}\left(\right), d\right) \land (\operatorname{omega}\left(\operatorname{termMarker}\left(\right), d\right) = 0 \land ((\forall a: A, (\forall b: A, \operatorname{d}\left(\operatorname{source}\left(a\right), \operatorname{source}\left(b\right)\right) = \operatorname{c}\left(\operatorname{f}\left(a\right), \operatorname{f}\left(b\right)\right))) \land ((\forall a: A, \operatorname{source}\left(a\right) \neq 1) \land (\operatorname{termMarker}\left(1\right) \neq 1 \land (\forall P: \operatorname{Term}\left(A\right) \to Prop, ((\operatorname{P}\left(1\right) \land ((\forall a: A, \operatorname{P}\left(\operatorname{source}\left(a\right)\right)) \land ((\forall s: \operatorname{Term}\left(A\right), (\operatorname{P}\left(s\right) \Rightarrow \operatorname{P}\left(\operatorname{termMarker}\left(s\right)\right))) \land (\forall s: \operatorname{Term}\left(A\right), (\forall t: \operatorname{Term}\left(A\right), ((\operatorname{P}\left(s\right) \land \operatorname{P}\left(t\right)) \Rightarrow \operatorname{P}\left((s \cdot t)\right))))))) \Rightarrow (\forall s: \operatorname{Term}\left(A\right), \operatorname{P}\left(s\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_zero_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is any finite type of labels, and f maps those labels to the original magma; repetitions and the old unit are allowed. Expr has separate constructors for unit, source, unary marker and ordered binary product. Term is the subset of unit normal forms: a product has two nonunit normal children. Multiplication removes a unit factor and otherwise keeps the binary product constructor. U(unit) is retained. Evaluation into every actual array model respects these operations. Consequently only the two-sided unit laws are imposed; no original operation-preserving or unit-preserving embedding is asserted.

For a source a the budget is 3(c(f(a),1)+c(1,f(a)))+6 omega. Unit has budget zero, a marker node has budget 9B+24 omega, and a nonunit product has budget 3(B(s)+B(t)). For every N>=1 the two unit comparisons of an evaluated term sum to at most its budget, and each ordered pair costs at most 3(B(s)+B(t)). All term pairs form one countable index type. The compact product of their finite closed intervals yields a single strictly increasing subsequence, rather than separate choices for separate pairs. All finite scalar balance identities pass to that same limit. Exact omega/N scaling gives zero unit drift, and the source matrix remains exact. The final induction principle states that the actual unit, source symbols, marker and binary product generate every element of Term. Each source symbol differs from the new unit, even if its original label equals the old unit.

Finite sums, the nonnegative recurrence and countable compact extraction are reused mathematical tools. The construction concerns the stated algebraic comparison model; it supplies no additional physical preparation or measurement assumptions and makes no literature priority claim.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawUnanchoredReplication.normal_form_budgets`
- Truth anchor: `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_replication`
- Truth anchor: `D5/S3/Quantum/Completion/RawUnanchoredReplication.raw_zero_drift`
- Dependency: [D5/S3/QuadraticForms/ThreeWayBalance](../../QuadraticForms/ThreeWayBalance.md)
