# OrbitIndexedSums

## Abstract

Exact tree evaluation and finite Fourier identities support the exclusion of uniform mixing on the cycle with twenty-one vertices.

**Definition 1.1 (Exp).**

$$\operatorname{Exp} : \operatorname{Type}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Exp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor fields are a : Int b : Int c : Int d : Int e : Int f : Int deriving DecidableEq.

**Definition 1.2 (plus).**

$$\forall (\operatorname{v} : \operatorname{Exp}) (\operatorname{w} : \operatorname{Exp}) , \operatorname{plus} \operatorname{v} \operatorname{w} = \langle \operatorname{v.a} + \operatorname{w.a} , \operatorname{v.b} + \operatorname{w.b} , \operatorname{v.c} + \operatorname{w.c} , \operatorname{v.d} + \operatorname{w.d} , \operatorname{v.e} + \operatorname{w.e} , \operatorname{v.f} + \operatorname{w.f} \rangle$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.plus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.3 (neg).**

$$\forall (\operatorname{v} : \operatorname{Exp}) , \operatorname{neg} \operatorname{v} = \langle - \operatorname{v.a} , - \operatorname{v.b} , - \operatorname{v.c} , - \operatorname{v.d} , - \operatorname{v.e} , - \operatorname{v.f} \rangle$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.neg` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.4 (act0).**

$$(\forall (\operatorname{v} : \operatorname{Exp}) , \operatorname{act0} 0 \operatorname{v} = \langle (1) \cdot \operatorname{v.a} , (1) \cdot \operatorname{v.b} , (1) \cdot \operatorname{v.c} , (1) \cdot \operatorname{v.d} , (1) \cdot \operatorname{v.e} , (1) \cdot \operatorname{v.f} \rangle) \land (\forall (\operatorname{v} : \operatorname{Exp}) , \operatorname{act0} 1 \operatorname{v} = \langle (1) \cdot \operatorname{v.a} + (- 1) \cdot \operatorname{v.d} + (1) \cdot \operatorname{v.e} , (- 1) \cdot \operatorname{v.e} , (1) \cdot \operatorname{v.b} + (1) \cdot \operatorname{v.d} + (- 1) \cdot \operatorname{v.e} , (- 1) \cdot \operatorname{v.d} + (1) \cdot \operatorname{v.e} + (- 1) \cdot \operatorname{v.f} , (1) \cdot \operatorname{v.c} + (- 1) \cdot \operatorname{v.f} , (1) \cdot \operatorname{v.d} + (- 1) \cdot \operatorname{v.e} \rangle) \land (\forall (\operatorname{v} : \operatorname{Exp}) , \operatorname{act0} 2 \operatorname{v} = \langle (1) \cdot \operatorname{v.a} + (1) \cdot \operatorname{v.c} , (- 1) \cdot \operatorname{v.c} + (1) \cdot \operatorname{v.f} , (- 1) \cdot \operatorname{v.c} + (- 1) \cdot \operatorname{v.d} , (1) \cdot \operatorname{v.c} , (1) \cdot \operatorname{v.b} , (- 1) \cdot \operatorname{v.c} + (- 1) \cdot \operatorname{v.d} + (1) \cdot \operatorname{v.e} \rangle) \land (\forall (\operatorname{v} : \operatorname{Exp}) , \operatorname{act0} 3 \operatorname{v} = \langle (1) \cdot \operatorname{v.a} + (1) \cdot \operatorname{v.b} , (- 1) \cdot \operatorname{v.b} , (- 1) \cdot \operatorname{v.b} + (1) \cdot \operatorname{v.f} , (1) \cdot \operatorname{v.b} + (1) \cdot \operatorname{v.d} + (- 1) \cdot \operatorname{v.e} , (- 1) \cdot \operatorname{v.e} , (- 1) \cdot \operatorname{v.b} + (1) \cdot \operatorname{v.c} \rangle) \land (\forall (\operatorname{v} : \operatorname{Exp}) , \operatorname{act0} 4 \operatorname{v} = \langle (1) \cdot \operatorname{v.a} + (- 1) \cdot \operatorname{v.d} , (1) \cdot \operatorname{v.e} , (1) \cdot \operatorname{v.d} , (- 1) \cdot \operatorname{v.c} + (- 1) \cdot \operatorname{v.d} , (- 1) \cdot \operatorname{v.c} + (1) \cdot \operatorname{v.f} , (1) \cdot \operatorname{v.b} + (1) \cdot \operatorname{v.d} \rangle) \land (\forall (\operatorname{v} : \operatorname{Exp}) , \operatorname{act0} 5 \operatorname{v} = \langle (1) \cdot \operatorname{v.a} + (1) \cdot \operatorname{v.f} , (1) \cdot \operatorname{v.c} + (- 1) \cdot \operatorname{v.f} , (- 1) \cdot \operatorname{v.d} + (1) \cdot \operatorname{v.e} + (- 1) \cdot \operatorname{v.f} , (- 1) \cdot \operatorname{v.b} + (1) \cdot \operatorname{v.f} , (- 1) \cdot \operatorname{v.b} , (- 1) \cdot \operatorname{v.d} + (- 1) \cdot \operatorname{v.f} \rangle) \land (\forall (\operatorname{i} : \operatorname{Nat}) (\operatorname{v} : \operatorname{Exp}) , 6 \leq \operatorname{i} \to \operatorname{act0} \operatorname{i} \operatorname{v} = \operatorname{v})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.act0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These six coordinate formulas and the default clause define the action.

**Definition 1.5 (act).**

$$\forall (\operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2)) (\operatorname{v} : \operatorname{Exp}) , \operatorname{act} \operatorname{g} \operatorname{v} = \operatorname{if} \operatorname{Fin.val} (\operatorname{show} \operatorname{Fin} 2 \operatorname{from} \operatorname{g.2}) = 0 \operatorname{then} \operatorname{act0} (\operatorname{Fin.val} (\operatorname{show} \operatorname{Fin} 6 \operatorname{from} \operatorname{g.1})) \operatorname{v} \operatorname{else} \operatorname{neg} (\operatorname{act0} (\operatorname{Fin.val} (\operatorname{show} \operatorname{Fin} 6 \operatorname{from} \operatorname{g.1})) \operatorname{v})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.act` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.6 (norm).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{AddCommMonoid} \operatorname{K}] (\operatorname{F} : \operatorname{Exp} \to \operatorname{K}) (\operatorname{v} : \operatorname{Exp}) , \operatorname{norm} \operatorname{F} \operatorname{v} = \sum \operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2) , \operatorname{F} (\operatorname{act} \operatorname{g} \operatorname{v})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.norm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Theorem 1.7 (norm_act).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{AddCommMonoid} \operatorname{K}] (\operatorname{F} : \operatorname{Exp} \to \operatorname{K}) (\operatorname{v} : \operatorname{Exp}) (\operatorname{h} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2)) , \operatorname{norm} \operatorname{F} (\operatorname{act} \operatorname{h} \operatorname{v}) = \operatorname{norm} \operatorname{F} \operatorname{v}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.norm_act` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.8 (Poly).**

$$\operatorname{Poly} : \operatorname{Type}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Poly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor fields are | tip : (Exp × Int) → Poly | node : Nat → Poly → Poly → Poly.

**Definition 1.9 (size).**

$$(\forall (\operatorname{field0} : \operatorname{Exp} \times \operatorname{Int}) , \operatorname{size} (\operatorname{Poly.tip} \operatorname{field0}) = 1) \land (\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{field1} : \operatorname{Poly}) (\operatorname{r} : \operatorname{Poly}) , \operatorname{size} (\operatorname{Poly.node} \operatorname{n} \operatorname{field1} \operatorname{r}) = \operatorname{n} + \operatorname{size} \operatorname{r})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.size` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.10 (valid).**

$$(\forall (\operatorname{field0} : \operatorname{Exp} \times \operatorname{Int}) , \operatorname{valid} (\operatorname{Poly.tip} \operatorname{field0}) = \operatorname{true}) \land (\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Poly}) (\operatorname{r} : \operatorname{Poly}) , \operatorname{valid} (\operatorname{Poly.node} \operatorname{n} \operatorname{l} \operatorname{r}) = \operatorname{Bool.and} (\operatorname{Bool.and} (\operatorname{decide} (\operatorname{n} = \operatorname{size} \operatorname{l})) (\operatorname{valid} \operatorname{l})) (\operatorname{valid} \operatorname{r}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.valid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.11 (lookup).**

$$(\forall (\operatorname{t} : \operatorname{Exp} \times \operatorname{Int}) (\operatorname{i} : \operatorname{Nat}) , \operatorname{lookup} (\operatorname{Poly.tip} \operatorname{t}) \operatorname{i} = \operatorname{t}) \land (\forall (\operatorname{n} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Poly}) (\operatorname{r} : \operatorname{Poly}) (\operatorname{i} : \operatorname{Nat}) , \operatorname{lookup} (\operatorname{Poly.node} \operatorname{n} \operatorname{l} \operatorname{r}) \operatorname{i} = \operatorname{if} \operatorname{i} < \operatorname{n} \operatorname{then} \operatorname{lookup} \operatorname{l} \operatorname{i} \operatorname{else} \operatorname{lookup} \operatorname{r} (\operatorname{i} - \operatorname{n}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.lookup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.12 (sumValues).**

$$(\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{AddCommMonoid} \operatorname{K}] , \forall (\operatorname{F} : (\operatorname{Exp} \times \operatorname{Int}) \to \operatorname{K}) (\operatorname{t} : \operatorname{Exp} \times \operatorname{Int}) , \operatorname{sumValues} \operatorname{F} (\operatorname{Poly.tip} \operatorname{t}) = \operatorname{F} \operatorname{t}) \land (\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{AddCommMonoid} \operatorname{K}] , \forall (\operatorname{F} : (\operatorname{Exp} \times \operatorname{Int}) \to \operatorname{K}) (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Poly}) (\operatorname{r} : \operatorname{Poly}) , \operatorname{sumValues} \operatorname{F} (\operatorname{Poly.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{sumValues} \operatorname{F} \operatorname{l} + \operatorname{sumValues} \operatorname{F} \operatorname{r})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.sumValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Theorem 1.13 (indexed_sum).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{AddCommMonoid} \operatorname{K}] (\operatorname{F} : (\operatorname{Exp} \times \operatorname{Int}) \to \operatorname{K}) (\operatorname{p} : \operatorname{Poly}) , (\operatorname{valid} \operatorname{p} = \operatorname{true}) \to ((\sum \operatorname{i} \in \operatorname{Finset.range} (\operatorname{size} \operatorname{p}) , \operatorname{F} (\operatorname{lookup} \operatorname{p} \operatorname{i})) = \operatorname{sumValues} \operatorname{F} \operatorname{p})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.indexed_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a valid polynomial tree, indexed lookup visits every leaf exactly once, so its indexed sum equals recursive evaluation. The proof follows the tree decomposition.

**Definition 1.14 (mulTerm).**

$$\forall (\operatorname{t} : (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{u} : (\operatorname{Exp} \times \operatorname{Int})) , \operatorname{mulTerm} \operatorname{t} \operatorname{u} = (\operatorname{plus} \operatorname{t.1} \operatorname{u.1} , \operatorname{t.2} \cdot \operatorname{u.2})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.mulTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.15 (evalPoly).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{F} : \operatorname{Exp} \to \operatorname{K}) (\operatorname{p} : \operatorname{Poly}) , \operatorname{evalPoly} \operatorname{F} \operatorname{p} = \operatorname{sumValues} (\operatorname{fun} \operatorname{t} \mapsto (\operatorname{t.2} : \operatorname{K}) \cdot \operatorname{F} \operatorname{t.1}) \operatorname{p}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.evalPoly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.16 (Tree).**

$$\operatorname{Tree} : \operatorname{Type} \to \operatorname{Type}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor fields are | tip : Nat → α → Tree α | node : Nat → Tree α → Tree α → Tree α.

**Definition 1.17 (low).**

$$(\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{i} : \operatorname{Nat}) (\operatorname{field1} : \alpha) , \operatorname{low} (\operatorname{Tree.tip} \operatorname{i} \operatorname{field1}) = \operatorname{i}) \land (\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{lo} : \operatorname{Nat}) (\operatorname{field1} : \operatorname{Tree} \alpha) (\operatorname{field2} : \operatorname{Tree} \alpha) , \operatorname{low} (\operatorname{Tree.node} \operatorname{lo} \operatorname{field1} \operatorname{field2}) = \operatorname{lo})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.low` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.18 (indexValid).**

$$(\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{field0} : \operatorname{Nat}) (\operatorname{field1} : \alpha) , \operatorname{indexValid} (\operatorname{Tree.tip} \operatorname{field0} \operatorname{field1}) = \operatorname{true}) \land (\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{lo} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Tree} \alpha) (\operatorname{r} : \operatorname{Tree} \alpha) , \operatorname{indexValid} (\operatorname{Tree.node} \operatorname{lo} \operatorname{l} \operatorname{r}) = \operatorname{Bool.and} (\operatorname{Bool.and} (\operatorname{decide} (\operatorname{lo} \leq \operatorname{low} \operatorname{l} \land \operatorname{lo} \leq \operatorname{low} \operatorname{r})) (\operatorname{indexValid} \operatorname{l})) (\operatorname{indexValid} \operatorname{r}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.indexValid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.19 (mask).**

$$(\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{field0} : \operatorname{Nat}) (\operatorname{field1} : \alpha) , \operatorname{mask} (\operatorname{Tree.tip} \operatorname{field0} \operatorname{field1}) = 1) \land (\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{lo} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Tree} \alpha) (\operatorname{r} : \operatorname{Tree} \alpha) , \operatorname{mask} (\operatorname{Tree.node} \operatorname{lo} \operatorname{l} \operatorname{r}) = \operatorname{Nat.lor} ((\operatorname{Nat.shiftLeft} (\operatorname{mask} \operatorname{l}) ((\operatorname{low} \operatorname{l} - \operatorname{lo})))) ((\operatorname{Nat.shiftLeft} (\operatorname{mask} \operatorname{r}) ((\operatorname{low} \operatorname{r} - \operatorname{lo})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.mask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.20 (leaves).**

$$(\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{i} : \operatorname{Nat}) (\operatorname{field1} : \alpha) , \operatorname{leaves} (\operatorname{Tree.tip} \operatorname{i} \operatorname{field1}) = [\operatorname{i}]) \land (\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Tree} \alpha) (\operatorname{r} : \operatorname{Tree} \alpha) , \operatorname{leaves} (\operatorname{Tree.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{List.append} (\operatorname{leaves} \operatorname{l}) (\operatorname{leaves} \operatorname{r}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.leaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.21 (count).**

$$(\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{field0} : \operatorname{Nat}) (\operatorname{field1} : \alpha) , \operatorname{count} (\operatorname{Tree.tip} \operatorname{field0} \operatorname{field1}) = 1) \land (\forall (\alpha : \operatorname{Type}) , \forall (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Tree} \alpha) (\operatorname{r} : \operatorname{Tree} \alpha) , \operatorname{count} (\operatorname{Tree.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{count} \operatorname{l} + \operatorname{count} \operatorname{r})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.22 (groupOfNat).**

$$\forall (\operatorname{n} : \operatorname{Nat}) , \operatorname{groupOfNat} \operatorname{n} = ((\operatorname{Nat.cast} (\operatorname{Nat.mod} \operatorname{n} 6) : \operatorname{ZMod} 6) , (\operatorname{Nat.cast} (\operatorname{Nat.div} (\operatorname{n}) 6) : \operatorname{ZMod} 2))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.groupOfNat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Division n/6 is the natural-number quotient, and n%6 is the natural-number remainder. The remainder is cast to ZMod 6, and the quotient is cast to ZMod 2; these are the two finite group coordinates.

**Definition 1.23 (zeroExp).**

$$\operatorname{zeroExp} = \langle 0 , 0 , 0 , 0 , 0 , 0 \rangle$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.zeroExp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.24 (checkInc).**

$$(\forall (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{rep} : \operatorname{Exp}) (\operatorname{i} : \operatorname{Nat}) (\operatorname{g} : \operatorname{Nat}) , \operatorname{checkInc} \operatorname{src} \operatorname{rep} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree.tip} \operatorname{i} \operatorname{g}) = \operatorname{decide} (\operatorname{act} (\operatorname{groupOfNat} \operatorname{g}) (\operatorname{src} \operatorname{i}) . 1 = \operatorname{rep})) \land (\forall (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{rep} : \operatorname{Exp}) (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat})) (\operatorname{r} : (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat})) , \operatorname{checkInc} \operatorname{src} \operatorname{rep} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{Bool.and} (\operatorname{checkInc} \operatorname{src} \operatorname{rep} \operatorname{l}) (\operatorname{checkInc} \operatorname{src} \operatorname{rep} \operatorname{r}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.checkInc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.25 (coefficientSum).**

$$(\forall (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{i} : \operatorname{Nat}) (\operatorname{field1} : \operatorname{Nat}) , \operatorname{coefficientSum} \operatorname{src} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree.tip} \operatorname{i} \operatorname{field1}) = (\operatorname{src} \operatorname{i}) . 2) \land (\forall (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat})) (\operatorname{r} : (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat})) , \operatorname{coefficientSum} \operatorname{src} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{coefficientSum} \operatorname{src} \operatorname{l} + \operatorname{coefficientSum} \operatorname{src} \operatorname{r})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.coefficientSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.26 (evalInc).**

$$(\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] , \forall (\operatorname{F} : \operatorname{Exp} \to \operatorname{K}) (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{i} : \operatorname{Nat}) (\operatorname{field1} : \operatorname{Nat}) , \operatorname{evalInc} \operatorname{F} \operatorname{src} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree.tip} \operatorname{i} \operatorname{field1}) = ((\operatorname{src} \operatorname{i}) . 2 : \operatorname{K}) \cdot \operatorname{norm} \operatorname{F} (\operatorname{src} \operatorname{i}) . 1) \land (\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] , \forall (\operatorname{F} : \operatorname{Exp} \to \operatorname{K}) (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat})) (\operatorname{r} : (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat})) , \operatorname{evalInc} \operatorname{F} \operatorname{src} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{evalInc} \operatorname{F} \operatorname{src} \operatorname{l} + \operatorname{evalInc} \operatorname{F} \operatorname{src} \operatorname{r})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.evalInc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.27 (Rows).**

$$\operatorname{Rows} : \operatorname{Type}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor fields are | row : Exp → Int → (D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree Nat) → Rows | node : Nat → Rows → Rows → Rows.

**Definition 1.28 (ids).**

$$(\forall (\operatorname{field0} : \operatorname{Exp}) (\operatorname{field1} : \operatorname{Int}) (\operatorname{t} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat}) , \operatorname{ids} (\operatorname{Rows.row} \operatorname{field0} \operatorname{field1} \operatorname{t}) = \operatorname{t}) \land (\forall (\operatorname{lo} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Rows}) (\operatorname{r} : \operatorname{Rows}) , \operatorname{ids} (\operatorname{Rows.node} \operatorname{lo} \operatorname{l} \operatorname{r}) = \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree.node} \operatorname{lo} (\operatorname{ids} \operatorname{l}) (\operatorname{ids} \operatorname{r}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.ids` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.29 (rowCheck).**

$$(\forall (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{rep} : \operatorname{Exp}) (\operatorname{expected} : \operatorname{Int}) (\operatorname{t} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat}) , \operatorname{rowCheck} \operatorname{src} (\operatorname{Rows.row} \operatorname{rep} \operatorname{expected} \operatorname{t}) = \operatorname{Bool.and} (\operatorname{checkInc} \operatorname{src} \operatorname{rep} \operatorname{t}) (\operatorname{decide} (\operatorname{coefficientSum} \operatorname{src} \operatorname{t} = \operatorname{expected}))) \land (\forall (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Rows}) (\operatorname{r} : \operatorname{Rows}) , \operatorname{rowCheck} \operatorname{src} (\operatorname{Rows.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{Bool.and} (\operatorname{rowCheck} \operatorname{src} \operatorname{l}) (\operatorname{rowCheck} \operatorname{src} \operatorname{r}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.rowCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Theorem 1.30 (combine_checked).**

$$\forall (\operatorname{src} : \operatorname{Nat} \to (\operatorname{Exp} \times \operatorname{Int})) (\operatorname{lo} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Rows}) (\operatorname{r} : \operatorname{Rows}) , (\operatorname{rowCheck} \operatorname{src} \operatorname{l} = \operatorname{true}) \to ((\operatorname{rowCheck} \operatorname{src} \operatorname{r} = \operatorname{true}) \to (\operatorname{rowCheck} \operatorname{src} (\operatorname{Rows.node} \operatorname{lo} \operatorname{l} \operatorname{r}) = \operatorname{true}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.combine_checked` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.31 (targetCheck).**

$$(\forall (\operatorname{rep} : \operatorname{Exp}) (\operatorname{expected} : \operatorname{Int}) (\operatorname{field2} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat}) , \operatorname{targetCheck} (\operatorname{Rows.row} \operatorname{rep} \operatorname{expected} \operatorname{field2}) = \operatorname{decide} (\operatorname{expected} = 0 \lor \operatorname{rep} = \operatorname{zeroExp})) \land (\forall (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Rows}) (\operatorname{r} : \operatorname{Rows}) , \operatorname{targetCheck} (\operatorname{Rows.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{Bool.and} (\operatorname{targetCheck} \operatorname{l}) (\operatorname{targetCheck} \operatorname{r}))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.32 (targetSum).**

$$(\forall (\operatorname{field0} : \operatorname{Exp}) (\operatorname{expected} : \operatorname{Int}) (\operatorname{field2} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat}) , \operatorname{targetSum} (\operatorname{Rows.row} \operatorname{field0} \operatorname{expected} \operatorname{field2}) = \operatorname{expected}) \land (\forall (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Rows}) (\operatorname{r} : \operatorname{Rows}) , \operatorname{targetSum} (\operatorname{Rows.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{targetSum} \operatorname{l} + \operatorname{targetSum} \operatorname{r})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.33 (targetValue).**

$$(\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] , \forall (\operatorname{F} : \operatorname{Exp} \to \operatorname{K}) (\operatorname{rep} : \operatorname{Exp}) (\operatorname{expected} : \operatorname{Int}) (\operatorname{field2} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \operatorname{Nat}) , \operatorname{targetValue} \operatorname{F} (\operatorname{Rows.row} \operatorname{rep} \operatorname{expected} \operatorname{field2}) = (\operatorname{expected} : \operatorname{K}) \cdot \operatorname{norm} \operatorname{F} \operatorname{rep}) \land (\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] , \forall (\operatorname{F} : \operatorname{Exp} \to \operatorname{K}) (\operatorname{field0} : \operatorname{Nat}) (\operatorname{l} : \operatorname{Rows}) (\operatorname{r} : \operatorname{Rows}) , \operatorname{targetValue} \operatorname{F} (\operatorname{Rows.node} \operatorname{field0} \operatorname{l} \operatorname{r}) = \operatorname{targetValue} \operatorname{F} \operatorname{l} + \operatorname{targetValue} \operatorname{F} \operatorname{r})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is determined by these constructor equations. Type denotes an arbitrary universe. Division of natural numbers is integer quotient; Nat.mod is the remainder. Bool.and, Nat.lor, Nat.shiftLeft and Nat.shiftRight retain their Lean meanings.

**Definition 1.34 (h0).**

$$\operatorname{h0} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.35 (p0).**

$$\operatorname{p0} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are specified by the Lean definition.

**Theorem 1.36 (hv0).**

$$\operatorname{valid} \operatorname{h0} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.37 (pv0).**

$$\operatorname{valid} \operatorname{p0} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.38 (h1).**

$$\operatorname{h1} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.39 (p1).**

$$\operatorname{p1} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are specified by the Lean definition.

**Theorem 1.40 (hv1).**

$$\operatorname{valid} \operatorname{h1} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.41 (pv1).**

$$\operatorname{valid} \operatorname{p1} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.42 (h2).**

$$\operatorname{h2} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.43 (p2).**

$$\operatorname{p2} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are specified by the Lean definition.

**Theorem 1.44 (hv2).**

$$\operatorname{valid} \operatorname{h2} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.45 (pv2).**

$$\operatorname{valid} \operatorname{p2} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.46 (h3).**

$$\operatorname{h3} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.47 (p3).**

$$\operatorname{p3} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.48 (hv3).**

$$\operatorname{valid} \operatorname{h3} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.49 (pv3).**

$$\operatorname{valid} \operatorname{p3} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.50 (h4).**

$$\operatorname{h4} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.51 (p4).**

$$\operatorname{p4} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are specified by the Lean definition.

**Theorem 1.52 (hv4).**

$$\operatorname{valid} \operatorname{h4} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.53 (pv4).**

$$\operatorname{valid} \operatorname{p4} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.54 (h5).**

$$\operatorname{h5} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.55 (p5).**

$$\operatorname{p5} : \operatorname{Poly}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.56 (hv5).**

$$\operatorname{valid} \operatorname{h5} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.57 (pv5).**

$$\operatorname{valid} \operatorname{p5} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.58 (source).**

$$\forall (\operatorname{i} : \operatorname{Nat}) , \operatorname{source} \operatorname{i} = \operatorname{if} \operatorname{i} < 29421 \operatorname{then} \operatorname{mulTerm} (\operatorname{lookup} \operatorname{h0} (\operatorname{Nat.div} (\operatorname{i} - 0) 21)) (\operatorname{lookup} \operatorname{p0} (\operatorname{Nat.mod} ((\operatorname{i} - 0)) (21))) \operatorname{else} \operatorname{if} \operatorname{i} < 49308 \operatorname{then} \operatorname{mulTerm} (\operatorname{lookup} \operatorname{h1} (\operatorname{Nat.div} (\operatorname{i} - 29421) 21)) (\operatorname{lookup} \operatorname{p1} (\operatorname{Nat.mod} ((\operatorname{i} - 29421)) (21))) \operatorname{else} \operatorname{if} \operatorname{i} < 59388 \operatorname{then} \operatorname{mulTerm} (\operatorname{lookup} \operatorname{h2} (\operatorname{Nat.div} (\operatorname{i} - 49308) 21)) (\operatorname{lookup} \operatorname{p2} (\operatorname{Nat.mod} ((\operatorname{i} - 49308)) (21))) \operatorname{else} \operatorname{if} \operatorname{i} < 118080 \operatorname{then} \operatorname{mulTerm} (\operatorname{lookup} \operatorname{h3} (\operatorname{Nat.div} (\operatorname{i} - 59388) 67)) (\operatorname{lookup} \operatorname{p3} (\operatorname{Nat.mod} ((\operatorname{i} - 59388)) (67))) \operatorname{else} \operatorname{if} \operatorname{i} < 142740 \operatorname{then} \operatorname{mulTerm} (\operatorname{lookup} \operatorname{h4} (\operatorname{Nat.div} (\operatorname{i} - 118080) 36)) (\operatorname{lookup} \operatorname{p4} (\operatorname{Nat.mod} ((\operatorname{i} - 118080)) (36))) \operatorname{else} \operatorname{if} \operatorname{i} < 149736 \operatorname{then} \operatorname{mulTerm} (\operatorname{lookup} \operatorname{h5} (\operatorname{Nat.div} (\operatorname{i} - 142740) 66)) (\operatorname{lookup} \operatorname{p5} (\operatorname{Nat.mod} ((\operatorname{i} - 142740)) (66))) \operatorname{else} (\langle 0 , 0 , 0 , 0 , 0 , 0 \rangle , 0)$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.source` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation. Nat.div is the natural-number integer quotient; Nat.mod is the remainder.

**Definition 1.59 (rows0).**

$$\operatorname{rows0} : \operatorname{Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.rows0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.60 (expectedMask0).**

$$\operatorname{expectedMask0} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.expectedMask0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.61 (rowChecked0).**

$$\operatorname{rowCheck} \operatorname{source} \operatorname{rows0} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.rowChecked0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.62 (targetChecked0).**

$$\operatorname{targetCheck} \operatorname{rows0} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetChecked0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.63 (idsValid0).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.indexValid} (\operatorname{ids} \operatorname{rows0}) = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.idsValid0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.64 (maskChecked0).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{ids} \operatorname{rows0}) = \operatorname{expectedMask0}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.maskChecked0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.65 (countChecked0).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.count} (\operatorname{ids} \operatorname{rows0}) = 49940$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.countChecked0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.66 (targetSum0).**

$$\operatorname{targetSum} \operatorname{rows0} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetSum0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.67 (amplitude).**

$$\forall (\operatorname{N} : \mathbb{N}) [\operatorname{NeZero} \operatorname{N}] (\operatorname{z} : \operatorname{ZMod} \operatorname{N} \to \mathbb{C}) (\operatorname{a} : \operatorname{ZMod} \operatorname{N}) (\operatorname{b} : \operatorname{ZMod} \operatorname{N}) , \operatorname{amplitude} \operatorname{z} \operatorname{a} \operatorname{b} = (\operatorname{N} : \mathbb{C})^{-1} \cdot \operatorname{ZMod.dft} \operatorname{z} (\operatorname{b} - \operatorname{a})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.amplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Theorem 1.68 (uniform_amplitude_iff_ratio).**

$$\forall (\operatorname{N} : \mathbb{N}) [\operatorname{NeZero} \operatorname{N}] (\operatorname{z} : \operatorname{ZMod} \operatorname{N} \to \mathbb{C}) , (\forall (\operatorname{j} : \operatorname{ZMod} \operatorname{N}) , \operatorname{Complex.normSq} (\operatorname{z} \operatorname{j}) = 1) \to ((\forall (\operatorname{a} \operatorname{b} : \operatorname{ZMod} \operatorname{N}) , \operatorname{Complex.normSq} (\operatorname{amplitude} \operatorname{z} \operatorname{a} \operatorname{b}) = 1 / (\operatorname{N} : \mathbb{R})) \iff (\forall (\operatorname{l} : \operatorname{ZMod} \operatorname{N}) , \operatorname{l} \neq 0 \to \sum \operatorname{j} : \operatorname{ZMod} \operatorname{N} , \operatorname{z} (\operatorname{j} + \operatorname{l}) / \operatorname{z} \operatorname{j} = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.uniform_amplitude_iff_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.69 (cycleA).**

$$\forall (\operatorname{N} : \mathbb{N}) [\operatorname{NeZero} \operatorname{N}] , \operatorname{cycleA} = (\operatorname{D5.S3.Combinatorics.NarayanaStrip.CiglerCycleWalkFolding.cycleAdj} \operatorname{N}) . \operatorname{map} (\operatorname{Int.castRingHom} \mathbb{C})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.cycleA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.70 (eigenvalue).**

$$\forall (\operatorname{N} : \mathbb{N}) [\operatorname{NeZero} \operatorname{N}] (\operatorname{j} : \operatorname{ZMod} \operatorname{N}) , \operatorname{eigenvalue} \operatorname{j} = \operatorname{ZMod.stdAddChar} \operatorname{j} + \operatorname{ZMod.stdAddChar} (- \operatorname{j})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.eigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Theorem 1.71 (exp_cycle_entry).**

$$\forall (\operatorname{N} : \mathbb{N}) [\operatorname{NeZero} \operatorname{N}] (\operatorname{c} : \mathbb{C}) (\operatorname{a} : \operatorname{ZMod} \operatorname{N}) (\operatorname{b} : \operatorname{ZMod} \operatorname{N}) , \operatorname{NormedSpace.exp} (\operatorname{SMul.smul} (\operatorname{c}) (\operatorname{cycleA})) \operatorname{a} \operatorname{b} = (\operatorname{N} : \mathbb{C})^{-1} \cdot \operatorname{ZMod.dft} (\operatorname{fun} \operatorname{j} \mapsto \operatorname{Complex.exp} (\operatorname{c} \cdot \operatorname{eigenvalue} \operatorname{j})) (\operatorname{b} - \operatorname{a})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.exp_cycle_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.72 (instDecidableEqExp).**

$$\operatorname{instDecidableEqExp} : \operatorname{DecidableEq} \operatorname{Exp}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.instDecidableEqExp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Exp`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Poly`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Rows`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.Tree`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.act`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.act0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.amplitude`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.checkInc`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.coefficientSum`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.combine_checked`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.count`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.countChecked0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.cycleA`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.eigenvalue`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.evalInc`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.evalPoly`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.exp_cycle_entry`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.expectedMask0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.groupOfNat`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.h5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.hv5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.ids`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.idsValid0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.indexValid`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.indexed_sum`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.instDecidableEqExp`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.leaves`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.lookup`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.low`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.mask`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.maskChecked0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.mulTerm`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.neg`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.norm`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.norm_act`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.p5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.plus`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.pv5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.rowCheck`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.rowChecked0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.rows0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.size`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.source`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.sumValues`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetCheck`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetChecked0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetSum`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetSum0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.targetValue`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.uniform_amplitude_iff_ratio`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.valid`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums.zeroExp`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding](../../../Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity](../../QuantumChannels/TomiyamaDiagonalKPositivity.md)
