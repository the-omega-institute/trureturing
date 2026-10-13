# MorphicDecomposition

## Abstract

Episturmian words: MorphicDecomposition.

**Theorem 1.1 (central prefix succ).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; List.IsPrefix\left(central\left(Delta\right)\left(k\right), central\left(Delta\right)\left(((k)+(1))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.2 (central prefix of le).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; \forall m \in (Nat),\; (k \le m) \Rightarrow (List.IsPrefix\left(central\left(Delta\right)\left(k\right), central\left(Delta\right)\left(m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.3 (central get eq cDelta).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; \forall i \in (Nat),\; (i < ((central\left(Delta\right)\left(k\right))).length) \Rightarrow (((central\left(Delta\right)\left(k\right)))[i] = cDelta\left(Delta\right)\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_get_eq_cDelta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.4 (central is cDelta prefix).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((cDelta\left(Delta\right))\right)\left(((central\left(Delta\right)\left(k\right))).length\right) = central\left(Delta\right)\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_is_cDelta_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.5 (letterImage).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; letterImage\left(x\right)\left(z\right) = (if (z = x) then ([x]) else ([x,z]))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Definition 1.6 (mu).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; (\forall z \in (Fin\left(d\right)),\; mu\left(Delta\right)\left((0)\right)\left((z)\right) = [z]) \land (\forall z \in (Fin\left(d\right)),\; \forall n \in (Nat),\; mu\left(Delta\right)\left(((n)+(1))\right)\left((z)\right) = ((letterImage\left((Delta\left(n\right))\right)\left(z\right))).flatMap\left((mu\left(Delta\right)\left(n\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.mu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.7 (mu length step).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall z \in (Fin\left(d\right)),\; ((mu\left(Delta\right)\left(((n)+(1))\right)\left(z\right))).length = if (z = Delta\left(n\right)) then (((mu\left(Delta\right)\left(n\right)\left(z\right))).length) else ((((mu\left(Delta\right)\left(n\right)\left((Delta\left(n\right))\right))).length)+(((mu\left(Delta\right)\left(n\right)\left(z\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.8 (mu length pos).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall z \in (Fin\left(d\right)),\; 0 < ((mu\left(Delta\right)\left(n\right)\left(z\right))).length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.9 (mu length triangle).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall u \in (Fin\left(d\right)),\; \forall v \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; (u \ne v) \Rightarrow (((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le (((mu\left(Delta\right)\left(n\right)\left(u\right))).length)+(((mu\left(Delta\right)\left(n\right)\left(v\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.10 (mu length at run start).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; ((n = 0) \lor (Delta\left(((n)-(1))\right) \ne Delta\left(n\right))) \Rightarrow (\forall z \in (Fin\left(d\right)),\; ((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le (2)\cdot (((mu\left(Delta\right)\left(n\right)\left((Delta\left(n\right))\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_at_run_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.11 (mu constant run).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall a \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; (\forall i \in (Nat),\; (i < a) \Rightarrow (Delta\left(((n)+(i))\right) = x)) \Rightarrow (mu\left(Delta\right)\left(((n)+(a))\right)\left(z\right) = if (z = x) then (mu\left(Delta\right)\left(n\right)\left(x\right)) else (((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left((mu\left(Delta\right)\left(n\right)\left(x\right))\right)\left(a\right))++(mu\left(Delta\right)\left(n\right)\left(z\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_constant_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.12 (Lword).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; Lword\left(x\right)\left(w\right) = (w.flatMap\left((letterImage\left(x\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.Lword` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Definition 1.13 (Hword).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; Hword\left(x\right)\left(w\right) = ((Lword\left(x\right)\left(w\right))++([x]))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.Hword` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.14 (letterImage conjugacy).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; ([x])++(((letterImage\left(x\right)\left(z\right))).reverse) = (letterImage\left(x\right)\left(z\right))++([x])$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.15 (Hword reverse).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; ((Hword\left(x\right)\left(w\right))).reverse = Hword\left(x\right)\left(w.reverse\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

List.prod_hom_rel propagates the letter-image conjugacy through the word. Reversal therefore commutes with Hword; Hword_palindrome_iff uses this identity to characterize palindromes.

**Theorem 1.16 (Hword starts).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \exists r \in (List\left((Fin\left(d\right))\right)),\; Hword\left(x\right)\left(w\right) = (x)::(r)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.17 (Hword cons).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; Hword\left(x\right)\left(((z)::(w))\right) = if (z = x) then ((x)::(Hword\left(x\right)\left(w\right))) else ((x)::((z)::(Hword\left(x\right)\left(w\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.18 (Hword injective).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; Function.Injective\left((Hword\left(x\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.19 (Hword palindrome iff).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.Palindrome\left((Hword\left(x\right)\left(w\right))\right)) \Leftrightarrow (List.Palindrome\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palindrome_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.20 (Lword append).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall u \in (List\left((Fin\left(d\right))\right)),\; \forall v \in (List\left((Fin\left(d\right))\right)),\; Lword\left(x\right)\left(((u)++(v))\right) = (Lword\left(x\right)\left(u\right))++(Lword\left(x\right)\left(v\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.21 (Lword prefix).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall u \in (List\left((Fin\left(d\right))\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(u, w\right)) \Rightarrow (List.IsPrefix\left(Lword\left(x\right)\left(u\right), Lword\left(x\right)\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.22 (Hword suffix decode).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, Hword\left(x\right)\left(w\right)\right)) \Rightarrow ((\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (x)::(r)) \Rightarrow (\exists v \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(v, w\right)) \land (s = Hword\left(x\right)\left(v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_suffix_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.23 (palindrome suffix Hword starts).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, Hword\left(x\right)\left(w\right)\right)) \Rightarrow ((List.Palindrome\left(s\right)) \Rightarrow ((s \ne []) \Rightarrow (\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (x)::(r))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_Hword_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.24 (Hword palCut).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palCut\left((Hword\left(x\right)\left(w\right))\right) = ((Lword\left(x\right)\left((w.take\left((palCut\left(w\right))\right))\right))).length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.25 (Hword palClosure).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palClosure\left((Hword\left(x\right)\left(w\right))\right) = Hword\left(x\right)\left((palClosure\left(w\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palClosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.26 (Lword suffix nonx).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (z \ne x) \Rightarrow ((List.IsSuffix\left(s, Lword\left(x\right)\left(w\right)\right)) \Rightarrow ((\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (z)::(r)) \Rightarrow (List.IsSuffix\left(([x])++((s)++([x])), Hword\left(x\right)\left(w\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_suffix_nonx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.27 (palindrome suffix last starts).**

$$\forall d \in (Nat),\; \forall z \in (Fin\left(d\right)),\; \forall p \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, (p)++([z])\right)) \Rightarrow ((List.Palindrome\left(s\right)) \Rightarrow ((s \ne []) \Rightarrow (\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (z)::(r))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_last_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.28 (palCut le of suffix).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, w\right)) \Rightarrow ((List.Palindrome\left(s\right)) \Rightarrow (palCut\left(w\right) \le (w.length)-(s.length)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_le_of_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.29 (Lword palClosure).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall p \in (List\left((Fin\left(d\right))\right)),\; (z \ne x) \Rightarrow (palClosure\left((Lword\left(x\right)\left(((p)++([z]))\right))\right) = Hword\left(x\right)\left((palClosure\left(((p)++([z]))\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_palClosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.30 (palClosure of palindrome).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.Palindrome\left(w\right)) \Rightarrow (palClosure\left(w\right) = w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_of_palindrome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.31 (Hword append letter closure).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palClosure\left(((Hword\left(x\right)\left(w\right))++([z]))\right) = Hword\left(x\right)\left((palClosure\left(((w)++([z]))\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_append_letter_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.32 (central Justin).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; central\left((cons\left(x\right)\left(Delta\right))\right)\left(((k)+(1))\right) = Hword\left(x\right)\left((central\left(Delta\right)\left(k\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin` (`✓ std3`). ∎

*Citation.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

Justin–Pirillo, equation (3): the palindromic-prefix morphism identity. Here cons is Mathlib Stream'.cons, which prepends one letter to a directive stream.

**Theorem 1.33 (central Justin shift).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; central\left(Delta\right)\left(((k)+(1))\right) = Hword\left((Delta\left(0\right))\right)\left((central\left((fun (n:Nat) \mapsto (Delta\left(((n)+(1))\right)))\right)\left(k\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin_shift` (`✓ std3`). ∎

*Citation.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

Justin–Pirillo, equation (3): the palindromic-prefix morphism identity.

**Definition 1.34 (muWord).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; muWord\left(Delta\right)\left(n\right)\left(w\right) = (w.flatMap\left((mu\left(Delta\right)\left(n\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.muWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.35 (mu shift).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall z \in (Fin\left(d\right)),\; mu\left(Delta\right)\left(((n)+(1))\right)\left(z\right) = Lword\left((Delta\left(0\right))\right)\left((mu\left((fun (j:Nat) \mapsto (Delta\left(((j)+(1))\right)))\right)\left(n\right)\left(z\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.36 (central morphic finite).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall k \in (Nat),\; central\left(Delta\right)\left(((n)+(k))\right) = (muWord\left(Delta\right)\left(n\right)\left((central\left((fun (j:Nat) \mapsto (Delta\left(((n)+(j))\right)))\right)\left(k\right))\right))++(central\left(Delta\right)\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_morphic_finite` (`✓ std3`). ∎

*Citation.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

Justin–Pirillo, equation (3): the palindromic-prefix morphism identity.

**Definition 1.37 (MorphicImage).**

$$\forall d \in (Nat),\; \forall source \in (((Nat) \to (Fin\left(d\right)))),\; \forall target \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; MorphicImage\left(source\right)\left(target\right)\left(f\right) = (\forall k \in (Nat),\; let W := (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(source\right)\left(k\right))).flatMap\left(f\right); (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(target\right)\left(W.length\right) = W)$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.MorphicImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.38 (wordPrefix isPrefix).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; \forall m \in (Nat),\; (k \le m) \Rightarrow (List.IsPrefix\left((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(k\right), (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_isPrefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.39 (cDelta morphicImage).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; MorphicImage\left((cDelta\left((fun (j:Nat) \mapsto (Delta\left(((n)+(j))\right)))\right))\right)\left((cDelta\left(Delta\right))\right)\left((mu\left(Delta\right)\left(n\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.cDelta_morphicImage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

## References

- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_append_letter_closure`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_cons`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_injective`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palClosure`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palCut`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palindrome_iff`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_reverse`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_starts`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_suffix_decode`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_append`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_palClosure`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_suffix_nonx`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.MorphicImage`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.cDelta_morphicImage`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin_shift`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_get_eq_cDelta`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_is_cDelta_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_morphic_finite`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_of_le`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_succ`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage_conjugacy`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.muWord`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_constant_run`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_at_run_start`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_pos`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_step`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_triangle`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_shift`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_of_palindrome`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_le_of_suffix`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_Hword_starts`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_last_starts`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_isPrefix`
- Dependency: [D5/S1/Words/Episturmian/PalindromicClosure](PalindromicClosure.md)
- Dependency: [D5/S1/Words/MBonacciSentinelDesubstitution](../MBonacciSentinelDesubstitution.md)
