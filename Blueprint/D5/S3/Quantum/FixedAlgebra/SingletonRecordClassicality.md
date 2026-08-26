# Singleton Record Classicality

## Abstract

Singleton environment-record classes leave exactly a diagonal classical algebra.

**Theorem 1.1 (Singleton record classes give a classical fixed algebra).**

$$\forall d, e: Nat, E: \operatorname{Fin}(d)\to\operatorname{Fin}(e)\to\mathbb{C} \Rightarrow(\forall i: \operatorname{Fin}(d), \sum_{a} \in \operatorname{Fin}(e) \Vert E(i, a) \Vert^{2} = 1 \land \forall i, j: \operatorname{Fin}(d), i \neq j \Rightarrow \operatorname{recordGram}(E, i, j) \neq 1 \Rightarrow\\{}(\forall i, j: \operatorname{Fin}(d), \operatorname{recordGram}(E, i, j) = 1 \Leftrightarrow i = j) \land (\forall rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), \operatorname{recordChannel}(E, rho) = rho \Leftrightarrow rho \in \operatorname{range}(\operatorname{diagonalAlgHom}(\mathbb{C}))) \land (\forall p: \operatorname{Fin}(d)\to\mathbb{C}, \operatorname{recordChannel}(E, \operatorname{diagonal}(p)) =\operatorname{diagonal}(p) \land \operatorname{diagonalRangeEquiv}(d)(\operatorname{diagonal}(p)) = p) \land (\forall x, y: \operatorname{range}(\operatorname{diagonalAlgHom}(\mathbb{C})), xy = yx) \land (\forall rho: \operatorname{Matrix}(\operatorname{Fin}(d), \operatorname{Fin}(d), \mathbb{C}), \operatorname{PosSemidef}(rho) \Rightarrow \operatorname{trace}(rho) = 1 \Rightarrow \operatorname{recordChannel}(E, rho) = rho \Rightarrow \exists q: \operatorname{Fin}(d)\to\mathbb{R}, rho = \operatorname{diagonal}(q) \land \forall i: \operatorname{Fin}(d), 0 \le q(i) \land \sum_{i} \in \operatorname{Fin}(d) q(i) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality.singleton_record_classicality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite system and environment address sets, construct the record Gram overlap from normalized environment amplitudes and let the reduced channel multiply each matrix entry by that overlap. Assume unit overlap occurs only on the same address, so every record equivalence class is a singleton.

The fixed matrices are exactly the diagonal matrices. The canonical diagonal algebra map has a range isomorphic to the coordinate algebra of complex functions on the system addresses, and its coordinates are recovered by diagonal entries; this range is commutative and is the stable accessible algebra.

Finally, a positive trace-one fixed matrix has real nonnegative diagonal coordinates whose sum is one. Thus the observer state is exactly a probability vector.

## References

- Truth anchor: `D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality.singleton_record_classicality`
