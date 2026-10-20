# The null tuple and Boolean constraint expressibility

## Abstract

Deleting the null tuple changes whether ternary disjunction is pp definable.

**Definition 1.1 (The five-mode relation).**

$$\forall a \in \operatorname{Fin}\left(3\right) \to \mathrm{Bool},\; (\operatorname{A}\left(a\right)) \Leftrightarrow ((\operatorname{and}\left(\operatorname{a}\left(0\right), \operatorname{a}\left(2\right)\right) = 0) \land (\operatorname{and}\left(\operatorname{a}\left(1\right), \operatorname{a}\left(2\right)\right) = 0))$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.A` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

Bits are ordered as (x,y,z), with z the middle site. A consists exactly of 000, 100, 001, 010 and 110. Bool false and true are written 0 and 1.

**Definition 1.2 (The null-free relation).**

$$\forall a \in \operatorname{Fin}\left(3\right) \to \mathrm{Bool},\; (\operatorname{N}\left(a\right)) \Leftrightarrow ((\operatorname{A}\left(a\right)) \land (\neg ((\operatorname{a}\left(0\right) = 0) \land ((\operatorname{a}\left(1\right) = 0) \land (\operatorname{a}\left(2\right) = 0)))))$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.N` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

N removes exactly 000 from A. Equivalently its third bit is NOR of its first two bits: z = not(x or y). This equivalence is checked in the proof of the construction below.

**Definition 1.3 (Equality).**

$$\forall a \in \operatorname{Fin}\left(2\right) \to \mathrm{Bool},\; (\operatorname{EQ}\left(a\right)) \Leftrightarrow (\operatorname{a}\left(0\right) = \operatorname{a}\left(1\right))$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.EQ` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

The binary equality relation.

**Definition 1.4 (Disequality).**

$$\forall a \in \operatorname{Fin}\left(2\right) \to \mathrm{Bool},\; (\operatorname{NEQ}\left(a\right)) \Leftrightarrow (\operatorname{a}\left(0\right) \ne \operatorname{a}\left(1\right))$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.NEQ` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

The binary disequality relation.

**Definition 1.5 (The zero singleton).**

$$\forall a \in \operatorname{Fin}\left(1\right) \to \mathrm{Bool},\; (\operatorname{C0}\left(a\right)) \Leftrightarrow (\operatorname{a}\left(0\right) = 0)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.C0` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

The unary relation containing only false.

**Definition 1.6 (The one singleton).**

$$\forall a \in \operatorname{Fin}\left(1\right) \to \mathrm{Bool},\; (\operatorname{C1}\left(a\right)) \Leftrightarrow (\operatorname{a}\left(0\right) = 1)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.C1` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

The unary relation containing only true.

**Definition 1.7 (Ternary disjunction).**

$$\forall a \in \operatorname{Fin}\left(3\right) \to \mathrm{Bool},\; (\operatorname{OR3}\left(a\right)) \Leftrightarrow (\operatorname{or}\left(\operatorname{or}\left(\operatorname{a}\left(0\right), \operatorname{a}\left(1\right)\right), \operatorname{a}\left(2\right)\right) = 1)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.OR3` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

OR3 contains every three-bit tuple except 000.

**Definition 1.8 (The ternary majority operation).**

$$\forall a \in \operatorname{Fin}\left(3\right) \to \mathrm{Bool},\; \operatorname{majority}\left(a\right) = \operatorname{or}\left(\operatorname{or}\left(\operatorname{and}\left(\operatorname{a}\left(0\right), \operatorname{a}\left(1\right)\right), \operatorname{and}\left(\operatorname{a}\left(0\right), \operatorname{a}\left(2\right)\right)\right), \operatorname{and}\left(\operatorname{a}\left(1\right), \operatorname{a}\left(2\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.majority` (`✓ std3`).

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

Majority preserves A, equality, disequality and both singleton constants. It sends the three unit vectors 100, 010, 001 to 000, so it does not preserve OR3. The general pp preservation theorem transfers this obstruction to every finite conjunction with any number of hidden variables.

**Theorem 1.9 (Correspondence with native windows).**

$$\forall x \in \mathrm{Bool},\; \forall y \in \mathrm{Bool},\; \forall z \in \mathrm{Bool},\; (\operatorname{A}\left(\operatorname{tuple}\left(x, y, z\right)\right)) \Leftrightarrow (\exists w \in \mathrm{Window},\; \operatorname{bits}\left(w\right) = \operatorname{word}\left(x, z, y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.a_window_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Window and bits are the existing LiteralWindowEnd definitions. Native bits are ordered low, middle, high, so the word is [x,z,y]. The native modes zero, low, middle, high, ends correspond respectively to the event tuples 000, 100, 001, 010, 110. The equivalence includes existence of a native window for each allowed tuple and excludes all three forbidden tuples.

**Definition 1.10 (A five-atom NOR definition).**

$$\operatorname{norAtoms}\left(\right) = \operatorname{atoms}\left(\operatorname{N}\left(0, 1, 3\right), \operatorname{N}\left(3, 3, 4\right), \operatorname{N}\left(4, 2, 5\right), \operatorname{N}\left(5, 5, 6\right), \operatorname{N}\left(7, 6, 7\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.norAtoms` (`✓ std3`).

*Citation.* Henry Maurice Sheffer (1913). *A set of five independent postulates for Boolean algebras, with application to logical constants*. DOI: [10.1090/S0002-9947-1913-1500960-1](https://doi.org/10.1090/S0002-9947-1913-1500960-1). URL: <https://doi.org/10.1090/S0002-9947-1913-1500960-1>.

*Commentary.*

Indices 0,1,2 denote free variables x,y,z; 3,4,5,6,7 denote hidden variables t,u,v,w,r. Thus the conjunction is N(x,y,t), N(t,t,u), N(u,z,v), N(v,v,w), N(r,w,r). The language has the single symbol N of arity three, represented by Unit with nArity constantly three and nRelations constantly N. There are no equality or constant atoms. If x or y or z holds, a hidden assignment is t = not(x or y), u = x or y, v = not(x or y or z), w = x or y or z, r = 0. Conversely the first four atoms compute w as the disjunction; the last atom forces w = 1.

**Theorem 1.11 (The two pp closures are separated).**

$$(\forall m \in \mathrm{Nat},\; \forall L \in \operatorname{List}\left(\operatorname{Atom}\left(\mathrm{baseArity}, 3 + m\right)\right),\; \neg (\forall a \in \operatorname{Fin}\left(3\right) \to \mathrm{Bool},\; (\operatorname{Defines}\left(\mathrm{baseRelations}, L, a\right)) \Leftrightarrow (\operatorname{OR3}\left(a\right)))) \land (\exists m \in \mathrm{Nat},\; \exists L \in \operatorname{List}\left(\operatorname{Atom}\left(\mathrm{nArity}, 3 + m\right)\right),\; \forall a \in \operatorname{Fin}\left(3\right) \to \mathrm{Bool},\; (\operatorname{Defines}\left(\mathrm{nRelations}, L, a\right)) \Leftrightarrow (\operatorname{OR3}\left(a\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.result` (`✓ std3`). ∎

*Citation.* Thomas J. Schaefer (1978). *The complexity of satisfiability problems*. DOI: [10.1145/800133.804350](https://doi.org/10.1145/800133.804350). URL: <https://doi.org/10.1145/800133.804350>.

*Commentary.*

The first conjunct quantifies over every natural m and every atom list in the language with the five symbols A, EQ, NEQ, C0 and C1 and their respective arities 3,2,2,1,1. It rules out pointwise equivalence with OR3. The second conjunct supplies m = 5 and the displayed N-only list, and proves equivalence for every free tuple. An atom can use any variable index in Fin(3+m), with repetition allowed. Defines has exactly the finite existential-conjunction semantics above. The negative result uses the general polymorphism preservation theorem on its proof path. These conclusions concern relation expressibility. They make no assertion about arbitrary probability laws, proof certificates or P versus NP. Majority closure and NOR completeness are classical Boolean constraint theory; the explicit small construction identifies the effect of the null tuple.

## References

- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.A`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.C0`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.C1`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.EQ`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.N`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.NEQ`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.OR3`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.a_window_iff`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.majority`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.norAtoms`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd](../../Arith/FibonacciAtomic/LiteralWindowEnd.md)
- Dependency: [D5/S3/Combinatorics/ConstraintRelations/PrimitivePositive](PrimitivePositive.md)
