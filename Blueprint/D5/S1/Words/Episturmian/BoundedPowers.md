# BoundedPowers

## Abstract

Episturmian words: BoundedPowers.

**Definition 1.1 (ConstantBlock).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall i \in (Nat),\; \forall a \in (Nat),\; ConstantBlock\left(Delta\right)\left(i\right)\left(a\right) = (\forall j \in (Nat),\; (j < a) \Rightarrow (Delta\left(((i)+(j))\right) = Delta\left(i\right)))$$

*Formalization.* `D5/S1/Words/Episturmian/BoundedPowers.ConstantBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed equations define the object.

**Definition 1.2 (RunStart).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall i \in (Nat),\; RunStart\left(Delta\right)\left(i\right) = ((i = 0) \lor (Delta\left(((i)-(1))\right) \ne Delta\left(i\right)))$$

*Formalization.* `D5/S1/Words/Episturmian/BoundedPowers.RunStart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.3 (unboundedPQ iff long blocks).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; (\neg (BoundedPQ\left(Delta\right))) \Leftrightarrow (\forall a \in (Nat),\; \exists i \in (Nat),\; ConstantBlock\left(Delta\right)\left(i\right)\left(a\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.unboundedPQ_iff_long_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.4 (constant block at run start).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall i \in (Nat),\; \forall a \in (Nat),\; (ConstantBlock\left(Delta\right)\left(i\right)\left(a\right)) \Rightarrow (\exists n \in (Nat),\; (n \le i) \land ((RunStart\left(Delta\right)\left(n\right)) \land (\forall j \in (Nat),\; (j < ((i)+(a))-(n)) \Rightarrow (Delta\left(((n)+(j))\right) = Delta\left(n\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.constant_block_at_run_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.5 (cDelta constant run cover).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall a \in (Nat),\; (0 < a) \Rightarrow (((n = 0) \lor (Delta\left(((n)-(1))\right) \ne Delta\left(n\right))) \Rightarrow ((\forall j \in (Nat),\; (j < a) \Rightarrow (Delta\left(((n)+(j))\right) = Delta\left(n\right))) \Rightarrow (Nonempty\left((PeriodicRunCover\left((cDelta\left(Delta\right))\right)\left(((mu\left(Delta\right)\left(n\right)\left((Delta\left(n\right))\right))).length\right)\left(a\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.cDelta_constant_run_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.6 (not boundedPQ dio top).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (Lang\left(t\right) = Lang\left((cDelta\left(Delta\right))\right)) \Rightarrow ((\neg (BoundedPQ\left(Delta\right))) \Rightarrow (dio\left(t\right) = \infty))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.not_boundedPQ_dio_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.7 (dio finite implies boundedPQ).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (Lang\left(t\right) = Lang\left((cDelta\left(Delta\right))\right)) \Rightarrow ((dio\left(t\right) < \infty) \Rightarrow (BoundedPQ\left(Delta\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.dio_finite_implies_boundedPQ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.8 (morphicImage block get).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left(f\right)) \Rightarrow (\forall k \in (Nat),\; \forall j \in (Nat),\; (j < ((f\left((s\left(k\right))\right))).length) \Rightarrow (t\left(((((imagePrefix\left(s\right)\left(f\right)\left(k\right))).length)+(j))\right) = ((f\left((s\left(k\right))\right)))[j]))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_block_get` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.9 (morphicImage block position).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left(f\right)) \Rightarrow ((\forall z \in (Fin\left(d\right)),\; 0 < ((f\left(z\right))).length) \Rightarrow (\forall n \in (Nat),\; \exists k \in (Nat),\; \exists j \in (Nat),\; (j < ((f\left((s\left(k\right))\right))).length) \land ((n = (((imagePrefix\left(s\right)\left(f\right)\left(k\right))).length)+(j)) \land (t\left(n\right) = ((f\left((s\left(k\right))\right)))[j]))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_block_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.10 (Hword prefix decode).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(s, Hword\left(x\right)\left(w\right)\right)) \Rightarrow ((\exists p \in (List\left((Fin\left(d\right))\right)),\; s = (p)++([x])) \Rightarrow (\exists v \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(v, w\right)) \land (s = Hword\left(x\right)\left(v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.Hword_prefix_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.11 (Hword prefix reflect).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall u \in (List\left((Fin\left(d\right))\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(Hword\left(x\right)\left(u\right), Hword\left(x\right)\left(w\right)\right)) \Rightarrow (List.IsPrefix\left(u, w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.Hword_prefix_reflect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.12 (Hword period desubstitute).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall p \in (Nat),\; (0 < p) \Rightarrow ((p < ((Hword\left(x\right)\left(w\right))).length) \Rightarrow ((List.HasPeriod\left((Hword\left(x\right)\left(w\right))\right)\left(p\right)) \Rightarrow (\exists v \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(v, w\right)) \land ((0 < v.length) \land ((((Lword\left(x\right)\left(v\right))).length = p) \land (List.HasPeriod\left(w\right)\left(v.length\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.Hword_period_desubstitute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.13 (extendedMu).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; extendedMu\left(Delta\right)\left(n\right)\left(w\right) = ((muWord\left(Delta\right)\left(n\right)\left(w\right))++(central\left(Delta\right)\left(n\right)))$$

*Formalization.* `D5/S1/Words/Episturmian/BoundedPowers.extendedMu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.14 (muWord shift).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; muWord\left(Delta\right)\left(((n)+(1))\right)\left(w\right) = Lword\left((Delta\left(0\right))\right)\left((muWord\left((fun (j:Nat) \mapsto (Delta\left(((j)+(1))\right)))\right)\left(n\right)\left(w\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.muWord_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.15 (extendedMu shift).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; extendedMu\left(Delta\right)\left(((n)+(1))\right)\left(w\right) = Hword\left((Delta\left(0\right))\right)\left((extendedMu\left((fun (j:Nat) \mapsto (Delta\left(((j)+(1))\right)))\right)\left(n\right)\left(w\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.extendedMu_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.16 (Hword prefix).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall u \in (List\left((Fin\left(d\right))\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(u, w\right)) \Rightarrow (List.IsPrefix\left(Hword\left(x\right)\left(u\right), Hword\left(x\right)\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.Hword_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.17 (central prefix extendedMu).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; List.IsPrefix\left(central\left(Delta\right)\left(n\right), extendedMu\left(Delta\right)\left(n\right)\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.central_prefix_extendedMu` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.18 (muWord prefix).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall u \in (List\left((Fin\left(d\right))\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(u, w\right)) \Rightarrow (List.IsPrefix\left(muWord\left(Delta\right)\left(n\right)\left(u\right), muWord\left(Delta\right)\left(n\right)\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.muWord_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.19 (extendedMu period lift).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall p \in (Nat),\; (0 < p) \Rightarrow (((p)+(((central\left(Delta\right)\left(n\right))).length) < ((extendedMu\left(Delta\right)\left(n\right)\left(w\right))).length) \Rightarrow ((List.HasPeriod\left((extendedMu\left(Delta\right)\left(n\right)\left(w\right))\right)\left(p\right)) \Rightarrow (\exists v \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(v, w\right)) \land ((0 < v.length) \land ((((muWord\left(Delta\right)\left(n\right)\left(v\right))).length = p) \land (List.HasPeriod\left(w\right)\left(v.length\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.extendedMu_period_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.20 (morphicImage shift).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left(f\right)) \Rightarrow (\forall k \in (Nat),\; MorphicImage\left((fun (j:Nat) \mapsto (s\left(((k)+(j))\right)))\right)\left((fun (j:Nat) \mapsto (t\left(((((imagePrefix\left(s\right)\left(f\right)\left(k\right))).length)+(j))\right)))\right)\left(f\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.21 (central prefix imagePrefix).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; (((central\left(Delta\right)\left(n\right))).length \le k) \Rightarrow (List.IsPrefix\left(central\left(Delta\right)\left(n\right), imagePrefix\left(s\right)\left((mu\left(Delta\right)\left(n\right))\right)\left(k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.central_prefix_imagePrefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.22 (morphicImage central prefix).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left((mu\left(Delta\right)\left(n\right))\right)) \Rightarrow ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(t\right)\left(((central\left(Delta\right)\left(n\right))).length\right) = central\left(Delta\right)\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_central_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.23 (morphicImage extended prefix).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left((mu\left(Delta\right)\left(n\right))\right)) \Rightarrow (\forall k \in (Nat),\; (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(t\right)\left(((extendedMu\left(Delta\right)\left(n\right)\left(((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(s\right)\left(k\right))\right))).length\right) = extendedMu\left(Delta\right)\left(n\right)\left(((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(s\right)\left(k\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_extended_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.24 (imagePrefix length strictMono).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; (\forall z \in (Fin\left(d\right)),\; 0 < ((f\left(z\right))).length) \Rightarrow (StrictMono\left((fun (k:Nat) \mapsto (((imagePrefix\left(s\right)\left(f\right)\left(k\right))).length))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.imagePrefix_length_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.25 (extendedMu segment occurrence).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left((mu\left(Delta\right)\left(n\right))\right)) \Rightarrow (\forall k \in (Nat),\; \forall l \in (Nat),\; (k \le l) \Rightarrow ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (t\left(((((imagePrefix\left(s\right)\left((mu\left(Delta\right)\left(n\right))\right)\left(k\right))).length)+(j))\right)))\right)\left((((((imagePrefix\left(s\right)\left((mu\left(Delta\right)\left(n\right))\right)\left(l\right))).length)-(((imagePrefix\left(s\right)\left((mu\left(Delta\right)\left(n\right))\right)\left(k\right))).length))+(((central\left(Delta\right)\left(n\right))).length))\right) = extendedMu\left(Delta\right)\left(n\right)\left(((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (s\left(((k)+(j))\right)))\right)\left(((l)-(k))\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.extendedMu_segment_occurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.26 (mu length mono).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall z \in (Fin\left(d\right)),\; \forall n \in (Nat),\; \forall m \in (Nat),\; (n \le m) \Rightarrow (((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le ((mu\left(Delta\right)\left(m\right)\left(z\right))).length)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.mu_length_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.27 (mu length uniform ratio).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall B \in (Nat),\; (\forall i \in (Nat),\; \exists j \in (Nat),\; (j < B) \land (Delta\left(((i)+(j))\right) \ne Delta\left(i\right))) \Rightarrow (\forall n \in (Nat),\; \forall u \in (Fin\left(d\right)),\; \forall v \in (Fin\left(d\right)),\; ((mu\left(Delta\right)\left(n\right)\left(u\right))).length \le (((B)+(2)))\cdot (((mu\left(Delta\right)\left(n\right)\left(v\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.mu_length_uniform_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.28 (central succ morphic).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; central\left(Delta\right)\left(((n)+(1))\right) = (mu\left(Delta\right)\left(n\right)\left((Delta\left(n\right))\right))++(central\left(Delta\right)\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.central_succ_morphic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.29 (image sum step).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; (\sum_{z:Fin\left(d\right)} (((mu\left(Delta\right)\left(((n)+(1))\right)\left(z\right))).length)) = ((\sum_{z:Fin\left(d\right)} (((mu\left(Delta\right)\left(n\right)\left(z\right))).length)))+((((d)-(1)))\cdot (((mu\left(Delta\right)\left(n\right)\left((Delta\left(n\right))\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.image_sum_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.30 (central length le image sum).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; (2 \le d) \Rightarrow (\forall n \in (Nat),\; ((central\left(Delta\right)\left(n\right))).length \le \sum_{z:Fin\left(d\right)} (((mu\left(Delta\right)\left(n\right)\left(z\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.central_length_le_image_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.31 (mu length increases over B).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall B \in (Nat),\; (\forall i \in (Nat),\; \exists j \in (Nat),\; (j < B) \land (Delta\left(((i)+(j))\right) \ne Delta\left(i\right))) \Rightarrow (\forall n \in (Nat),\; \forall z \in (Fin\left(d\right)),\; (((mu\left(Delta\right)\left(n\right)\left(z\right))).length)+(1) \le ((mu\left(Delta\right)\left(((n)+(B))\right)\left(z\right))).length)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.mu_length_increases_over_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.32 (mu length blocks ge).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall B \in (Nat),\; (\forall i \in (Nat),\; \exists j \in (Nat),\; (j < B) \land (Delta\left(((i)+(j))\right) \ne Delta\left(i\right))) \Rightarrow (\forall k \in (Nat),\; \forall z \in (Fin\left(d\right)),\; (k)+(1) \le ((mu\left(Delta\right)\left(((k)\cdot (B))\right)\left(z\right))).length)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.mu_length_blocks_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.33 (boundedPQ image scale).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall B \in (Nat),\; \forall p \in (Nat),\; (2 \le d) \Rightarrow ((0 < p) \Rightarrow ((\forall i \in (Nat),\; \exists j \in (Nat),\; (j < B) \land (Delta\left(((i)+(j))\right) \ne Delta\left(i\right))) \Rightarrow (\exists n \in (Nat),\; ((\forall z \in (Fin\left(d\right)),\; p < ((mu\left(Delta\right)\left(n\right)\left(z\right))).length)) \land (((\forall z \in (Fin\left(d\right)),\; ((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le ((2)\cdot (((B)+(2))))\cdot (p))) \land (((central\left(Delta\right)\left(n\right))).length \le (d)\cdot ((((2)\cdot (((B)+(2))))\cdot (p))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.boundedPQ_image_scale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.34 (wordPrefix subinterval).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall L \in (Nat),\; \forall a \in (Nat),\; \forall ell \in (Nat),\; ((a)+(ell) \le L) \Rightarrow (List.IsInfix\left((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (x\left(((a)+(j))\right)))\right)\left(ell\right), (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(L\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.wordPrefix_subinterval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.35 (morphic periodic factor bound).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left((mu\left(Delta\right)\left(n\right))\right)) \Rightarrow (\forall p \in (Nat),\; \forall Q \in (Nat),\; \forall b \in (Nat),\; \forall ell \in (Nat),\; (0 < p) \Rightarrow ((\forall z \in (Fin\left(d\right)),\; p < ((mu\left(Delta\right)\left(n\right)\left(z\right))).length) \Rightarrow ((\forall z \in (Fin\left(d\right)),\; ((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le Q) \Rightarrow ((List.HasPeriod\left(((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (t\left(((b)+(j))\right)))\right)\left(ell\right))\right)\left(p\right)) \Rightarrow (ell \le ((p)+(((central\left(Delta\right)\left(n\right))).length))+((2)\cdot (Q)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.morphic_periodic_factor_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.36 (cDelta periodic factor bound).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall B \in (Nat),\; (\forall i \in (Nat),\; \exists j \in (Nat),\; (j < B) \land (Delta\left(((i)+(j))\right) \ne Delta\left(i\right))) \Rightarrow ((2 \le d) \Rightarrow (\forall p \in (Nat),\; \forall b \in (Nat),\; \forall ell \in (Nat),\; (0 < p) \Rightarrow ((List.HasPeriod\left(((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (cDelta\left(Delta\right)\left(((b)+(j))\right)))\right)\left(ell\right))\right)\left(p\right)) \Rightarrow (ell \le (((1)+(((2)\cdot (((d)+(2))))\cdot (((B)+(2))))))\cdot (p)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.cDelta_periodic_factor_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.37 (BoundedPowers).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; BoundedPowers\left(x\right) = (\exists C \in (NNReal),\; \forall n \in (Nat),\; \forall V \in (List\left((Fin\left(d\right))\right)),\; \forall hV \in (V \ne []),\; \forall ell \in (Nat),\; (V.length \le ell) \Rightarrow (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (x\left(((n)+(j))\right)))\right)\left(ell\right) = fractionalPower\left(V\right)\left(hV\right)\left(ell\right)) \Rightarrow ((((ell:Real)))/(V.length) \le ((C:Real)))))$$

*Formalization.* `D5/S1/Words/Episturmian/BoundedPowers.BoundedPowers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.38 (dio finite of bounded powers).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; (BoundedPowers\left(x\right)) \Rightarrow (dio\left(x\right) < \infty)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.dio_finite_of_bounded_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.39 (boundedPowers of language eq).**

$$\forall d \in (Nat),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; (Lang\left(t\right) = Lang\left(x\right)) \Rightarrow ((BoundedPowers\left(x\right)) \Rightarrow (BoundedPowers\left(t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.boundedPowers_of_language_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.40 (fractionalPower period).**

$$\forall d \in (Nat),\; \forall V \in (List\left((Fin\left(d\right))\right)),\; \forall hV \in (V \ne []),\; \forall ell \in (Nat),\; List.HasPeriod\left((fractionalPower\left(V\right)\left(hV\right)\left(ell\right))\right)\left(V.length\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.fractionalPower_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.41 (boundedPQ boundedPowers).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; (BoundedPQ\left(Delta\right)) \Rightarrow (BoundedPowers\left((cDelta\left(Delta\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/BoundedPowers.boundedPQ_boundedPowers` (`✓ std3`). ∎

*Citation.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

Justin–Pirillo, Section 4.1: bounded directive runs give bounded fractional powers.

## References

- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.BoundedPowers`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.ConstantBlock`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.Hword_period_desubstitute`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.Hword_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.Hword_prefix_decode`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.Hword_prefix_reflect`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.RunStart`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.boundedPQ_boundedPowers`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.boundedPQ_image_scale`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.boundedPowers_of_language_eq`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.cDelta_constant_run_cover`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.cDelta_periodic_factor_bound`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.central_length_le_image_sum`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.central_prefix_extendedMu`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.central_prefix_imagePrefix`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.central_succ_morphic`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.constant_block_at_run_start`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.dio_finite_implies_boundedPQ`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.dio_finite_of_bounded_powers`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.extendedMu`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.extendedMu_period_lift`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.extendedMu_segment_occurrence`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.extendedMu_shift`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.fractionalPower_period`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.imagePrefix_length_strictMono`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.image_sum_step`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_block_get`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_block_position`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_central_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_extended_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.morphicImage_shift`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.morphic_periodic_factor_bound`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.muWord_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.muWord_shift`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.mu_length_blocks_ge`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.mu_length_increases_over_B`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.mu_length_mono`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.mu_length_uniform_ratio`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.not_boundedPQ_dio_top`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.unboundedPQ_iff_long_blocks`
- Truth anchor: `D5/S1/Words/Episturmian/BoundedPowers.wordPrefix_subinterval`
- Dependency: [D5/S1/Words/Episturmian/DensePowerWindow](DensePowerWindow.md)
