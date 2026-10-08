# Clifford Bond Parents

## Abstract

Average the positive Fourier vacuum over Clifford monomials, label each outcome by its bond conjugation signs, and push it to Boolean assignments.

Formulas retain Lean application and binder notation. Omega denotes the outcome-index type Ω, whereas ω denotes an outcome. Square brackets denote anonymous typeclass assumptions. Scalar coercions display their target types; angle brackets suppress the proof field of a Fin value. The identity is written as 1. Products of matrices and scalar actions use a centered dot; the operand types distinguish them. Infix Matrix.kronecker denotes the Lean kronecker notation.

**Definition 1.1 (cycleCoeff).**

$$\begin{aligned}\forall (L : \mathbb{N}),\\\forall (v : \operatorname{Fin} (2 \cdot L)),\\(\operatorname{cycleCoeff} (L : = L) (v : = v) : \mathbb{C}) = (\operatorname{if} v . \operatorname{val} + 1 < 2 \cdot L \operatorname{then} \operatorname{Complex} . I \operatorname{else} - \operatorname{Complex} . I)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.cycleCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines cycleCoeff.

**Definition 1.2 (cycleMajoranaBond).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\\forall (L : \mathbb{N}),\\\forall (g : \operatorname{Fin} (2 \cdot L) \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\\forall (v : \operatorname{Fin} (2 \cdot L)),\\(\operatorname{cycleMajoranaBond} (\iota : = \iota) (L : = L) (g : = g) (v : = v) : \operatorname{Matrix} \iota \iota \mathbb{C}) = (\operatorname{cycleCoeff} L v \cdot (g v \cdot g (\operatorname{finRotate} (2 \cdot L) v)))\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.cycleMajoranaBond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression defines cycleMajoranaBond.

**Lemma 1.3 (cycle majorana parent).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (n : \mathbb{N}),\\(1 \leq n) \to\\\forall (g : \operatorname{Fin} (2 \cdot (n + 1)) \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\(\forall j , g j \cdot g j = 1) \to\\(\forall j , \operatorname{star} (g j) = g j) \to\\(\forall j k , j \neq k \to g j \cdot g k = - (g k \cdot g j)) \to\\\exists E : (\operatorname{Fin} (2 \cdot (n + 1)) \to \operatorname{Bool}) \to \operatorname{Matrix} \iota \iota \mathbb{C} , (\forall a , (E a) . \operatorname{PosSemidef}) \land (\sum a , E a = 1) \land (\forall v , \sum a , \operatorname{outcomeSign} (a v) \cdot E a = (\operatorname{visibility} n : \mathbb{C}) \cdot \operatorname{cycleMajoranaBond} g v)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.cycle_majorana_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Average the positive Fourier vacuum over Clifford monomials, label each outcome by its bond conjugation signs, and push it to Boolean assignments. The average normalizes the parent and the Fourier covariance fixes every antiperiodic bond marginal at the threshold.

**Lemma 1.4 (consecutive majorana parent).**

$$\begin{aligned}\forall (\iota : \operatorname{Type}),\\{}[\operatorname{Fintype} \iota] ,\\{}[\operatorname{DecidableEq} \iota] ,\\\forall (n : \mathbb{N}),\\\forall (q : \mathbb{N}),\\(1 \leq n) \to\\\forall (g : \operatorname{Fin} (2 \cdot (n + 1)) \to \operatorname{Matrix} \iota \iota \mathbb{C}),\\(\forall j , g j \cdot g j = 1) \to\\(\forall j , \operatorname{star} (g j) = g j) \to\\(\forall j k , j \neq k \to g j \cdot g k = - (g k \cdot g j)) \to\\\forall (j : \operatorname{Fin} q \to \operatorname{Fin} (2 \cdot (n + 1))),\\\forall (k : \operatorname{Fin} q \to \operatorname{Fin} (2 \cdot (n + 1))),\\(\forall v , (k v) . \operatorname{val} = (j v) . \operatorname{val} + 1) \to\\\exists E : (\operatorname{Fin} q \to \operatorname{Bool}) \to \operatorname{Matrix} \iota \iota \mathbb{C} , (\forall a , (E a) . \operatorname{PosSemidef}) \land (\sum a , E a = 1) \land (\forall v , \sum a , \operatorname{outcomeSign} (a v) \cdot E a = (\operatorname{visibility} n : \mathbb{C}) \cdot (\operatorname{Complex} . I \cdot (g (j v) \cdot g (k v))))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.consecutive_majorana_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This consecutive majorana parent identity is used in the CliffordBondParents construction.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.consecutive_majorana_parent`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.cycleCoeff`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.cycleMajoranaBond`
- Truth anchor: `D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents.cycle_majorana_parent`
- Dependency: [D5/S3/Quantum/Measurements/CliffordJointMeasurability/FourierCliffordVacuum](FourierCliffordVacuum.md)
