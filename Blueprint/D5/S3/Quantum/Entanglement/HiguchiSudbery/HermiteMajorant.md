# HermiteMajorant

## Abstract

Two double contacts and a nonnegative fourth derivative force nonnegativity on the positive half-line.

**Theorem 1.1 (Fourth derivative comparison).**

$$\forall (f : \operatorname{Real} \to \operatorname{Real}), (\forall (f_{1} : \operatorname{Real} \to \operatorname{Real}), (\forall (f_{2} : \operatorname{Real} \to \operatorname{Real}), (\forall (f_{3} : \operatorname{Real} \to \operatorname{Real}), (\forall (f_{4} : \operatorname{Real} \to \operatorname{Real}), ((\forall (x : \operatorname{Real}), ((0 < x) \Rightarrow (\operatorname{HasDerivAt}\left(f, \left(f_{1}\right)\left(x\right), x\right)))) \Rightarrow ((\forall (x : \operatorname{Real}), ((0 < x) \Rightarrow (\operatorname{HasDerivAt}\left(f_{1}, \left(f_{2}\right)\left(x\right), x\right)))) \Rightarrow ((\forall (x : \operatorname{Real}), ((0 < x) \Rightarrow (\operatorname{HasDerivAt}\left(f_{2}, \left(f_{3}\right)\left(x\right), x\right)))) \Rightarrow ((\forall (x : \operatorname{Real}), ((0 < x) \Rightarrow (\operatorname{HasDerivAt}\left(f_{3}, \left(f_{4}\right)\left(x\right), x\right)))) \Rightarrow ((\forall (x : \operatorname{Real}), ((0 < x) \Rightarrow (0 \le \left(f_{4}\right)\left(x\right)))) \Rightarrow (\forall (a : \operatorname{Real}), (\forall (b : \operatorname{Real}), (((((0 < a) \land (a < b)) \land ((f\left(a\right) = 0) \land (f\left(b\right) = 0))) \land ((\left(f_{1}\right)\left(a\right) = 0) \land (\left(f_{1}\right)\left(b\right) = 0))) \Rightarrow (\forall (x : \operatorname{Real}), ((0 < x) \Rightarrow (0 \le f\left(x\right))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteMajorant.double_contact_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The functions f, f₁, f₂, f₃ and f₄ form a derivative chain at every positive point. Both f and f₁ vanish at the ordered positive nodes a and b. The displayed conclusion covers every positive x, including the contact nodes.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/HiguchiSudbery/HermiteMajorant.double_contact_nonnegative`
