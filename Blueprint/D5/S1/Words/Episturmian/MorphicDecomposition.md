# MorphicDecomposition

## Abstract

Episturmian words: MorphicDecomposition.

**Definition 1.1 (palClosure).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall h \in (\exists n \in (Nat),\; \exists p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \land ((List.Palindrome\left(p\right)) \land (p.length = n))),\; \forall hp \in (\exists p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \land ((List.Palindrome\left(p\right)) \land (p.length = Nat.find\left(h\right)))),\; palClosure\left(w\right) = Classical.choose\left(hp\right)$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure` (`✓ std3`).

*Citation.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

Droubay–Justin–Pirillo, Section 2: the palindromic closure construction. The evidence for the least length and its palindrome is quantified explicitly; proof irrelevance makes Classical.choose independent of these proof terms.

**Theorem 1.2 (palClosure spec).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, palClosure\left(w\right)\right)) \land ((List.Palindrome\left((palClosure\left(w\right))\right)) \land (\forall p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \Rightarrow ((List.Palindrome\left(p\right)) \Rightarrow (((palClosure\left(w\right))).length \le p.length))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.3 (palCut).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall h \in (\exists k \in (Nat),\; (k \le w.length) \land (List.Palindrome\left((w.drop\left(k\right))\right))),\; palCut\left(w\right) = Nat.find\left(h\right)$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.palCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The least cut leaves a palindromic suffix. Existence proof arguments are displayed as quantified evidence; proof irrelevance makes Nat.find independent of the evidence.

**Theorem 1.4 (palCut spec).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (palCut\left(w\right) \le w.length) \land (List.Palindrome\left((w.drop\left((palCut\left(w\right))\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.5 (palCut min).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall k \in (Nat),\; (k \le w.length) \Rightarrow ((List.Palindrome\left((w.drop\left(k\right))\right)) \Rightarrow (palCut\left(w\right) \le k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.6 (palindrome extension middle).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall r \in (List\left((Fin\left(d\right))\right)),\; (List.Palindrome\left(((w)++(r))\right)) \Rightarrow ((r.length \le w.length) \Rightarrow (List.Palindrome\left((w.drop\left(r.length\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_extension_middle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.7 (palindrome extension length).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \Rightarrow ((List.Palindrome\left(p\right)) \Rightarrow ((w.length)+(palCut\left(w\right)) \le p.length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_extension_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.8 (closure candidate palindrome).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; List.Palindrome\left(((w)++(((w.take\left((palCut\left(w\right))\right))).reverse))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.closure_candidate_palindrome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.9 (palClosure formula cut).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palClosure\left(w\right) = (w)++(((w.take\left((palCut\left(w\right))\right))).reverse)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_formula_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.10 (central).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; (central\left(Delta\right)\left((0)\right) = []) \land (\forall k \in (Nat),\; central\left(Delta\right)\left(((k)+(1))\right) = palClosure\left(((central\left(Delta\right)\left(k\right))++([Delta\left(k\right)]))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.central` (`✓ std3`).

*Citation.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

Droubay–Justin–Pirillo, Section 2: the palindromic closure construction.

**Theorem 1.11 (central length ge).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; k \le ((central\left(Delta\right)\left(k\right))).length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_length_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.12 (cDelta).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; cDelta\left(Delta\right)\left(n\right) = ((central\left(Delta\right)\left(((n)+(1))\right))).get\left(\langle n\rangle \right)$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.cDelta` (`✓ std3`).

*Citation.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

Droubay–Justin–Pirillo, Section 2: the palindromic closure construction. The Fin index shows its value; its inequality proof is implicit.

**Definition 1.13 (Lang).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; Lang\left(x\right) = (\{ w:List\left((Fin\left(d\right))\right) \mid \exists i \in (Nat),\; \forall j \in (Fin\left(w.length\right)),\; w.get\left(j\right) = x\left(((i)+(\operatorname{val}\left(j\right)))\right) \})$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.Lang` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Section 2: episturmian words, directive words and partial quotients.

**Definition 1.14 (BoundedPQ).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; BoundedPQ\left(Delta\right) = (\exists B \in (Nat),\; \forall i \in (Nat),\; \exists j \in (Nat),\; (j < B) \land (Delta\left(((i)+(j))\right) \ne Delta\left(i\right)))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.BoundedPQ` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Section 2: episturmian words, directive words and partial quotients.

**Definition 1.15 (fractionalPower).**

$$\forall d \in (Nat),\; \forall V \in (List\left((Fin\left(d\right))\right)),\; \forall hV \in (V \ne []),\; \forall ell \in (Nat),\; fractionalPower\left(V\right)\left(hV\right)\left(ell\right) = ((List.range\left(ell\right))).map\left((fun (i:Nat) \mapsto (V.get\left(\langle Nat.mod\left(i, V.length\right)\rangle \right)))\right)$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.fractionalPower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed equations define the object. The Fin index shows its value; its inequality proof is implicit. Nat.mod(i, q) denotes the natural-number remainder i % q.

**Definition 1.16 (DioAdmissible).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall rho \in (NNReal),\; DioAdmissible\left(x\right)\left(rho\right) = (\forall L \in (Nat),\; \exists U \in (List\left((Fin\left(d\right))\right)),\; \exists V \in (List\left((Fin\left(d\right))\right)),\; \exists ell \in (Nat),\; \exists hV \in (V \ne []),\; (V.length \le ell) \land (((U.length)+(ell) \ge L) \land (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(((U.length)+(ell))\right) = (U)++(fractionalPower\left(V\right)\left(hV\right)\left(ell\right))) \land (((((U.length)+(ell):Real)))/(((U.length)+(V.length))) \ge ((rho:Real))))))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.DioAdmissible` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Definition 1.1.

**Definition 1.17 (dio).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; dio\left(x\right) = (iSup\left(fun (rho:NNReal) \mapsto (iSup\left(fun (\cdot :DioAdmissible\left(x\right)\left(rho\right)) \mapsto (((rho:ENNReal)))\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.dio` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Definition 1.1.

**Definition 1.18 (claim).**

$$claim = (\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (Lang\left(t\right) = Lang\left((cDelta\left(Delta\right))\right)) \Rightarrow ((\neg (\exists N \in (Nat),\; \exists p \in (Nat),\; (0 < p) \land (\forall n \in (Nat),\; (N \le n) \Rightarrow (t\left((n+p)\right) = t\left(n\right))))) \Rightarrow (((dio\left(t\right) < \infty) \Leftrightarrow (BoundedPQ\left(Delta\right))))))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.claim` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Let $\mathbf{t}$ be an aperiodic episturmian word. Then $dio\left(\mathbf{t}\right) < \infty$ if and only if $\mathbf{t}$ has bounded partial quotients.

Peltomäki, Conjecture 8.4, Section 8.

Peltomäki, Conjecture 8.4, Section 8.

**Theorem 1.19 (central prefix succ).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; List.IsPrefix\left(central\left(Delta\right)\left(k\right), central\left(Delta\right)\left(((k)+(1))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.20 (central prefix of le).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; \forall m \in (Nat),\; (k \le m) \Rightarrow (List.IsPrefix\left(central\left(Delta\right)\left(k\right), central\left(Delta\right)\left(m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.21 (central get eq cDelta).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; \forall i \in (Nat),\; (i < ((central\left(Delta\right)\left(k\right))).length) \Rightarrow (((central\left(Delta\right)\left(k\right)))[i] = cDelta\left(Delta\right)\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_get_eq_cDelta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.22 (central is cDelta prefix).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((cDelta\left(Delta\right))\right)\left(((central\left(Delta\right)\left(k\right))).length\right) = central\left(Delta\right)\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_is_cDelta_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.23 (letterImage).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; letterImage\left(x\right)\left(z\right) = (if (z = x) then ([x]) else ([x,z]))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Definition 1.24 (mu).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; (\forall z \in (Fin\left(d\right)),\; mu\left(Delta\right)\left((0)\right)\left((z)\right) = [z]) \land (\forall z \in (Fin\left(d\right)),\; \forall n \in (Nat),\; mu\left(Delta\right)\left(((n)+(1))\right)\left((z)\right) = ((letterImage\left((Delta\left(n\right))\right)\left(z\right))).flatMap\left((mu\left(Delta\right)\left(n\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.mu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.25 (mu length step).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall z \in (Fin\left(d\right)),\; ((mu\left(Delta\right)\left(((n)+(1))\right)\left(z\right))).length = if (z = Delta\left(n\right)) then (((mu\left(Delta\right)\left(n\right)\left(z\right))).length) else ((((mu\left(Delta\right)\left(n\right)\left((Delta\left(n\right))\right))).length)+(((mu\left(Delta\right)\left(n\right)\left(z\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.26 (mu length mono).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall z \in (Fin\left(d\right)),\; \forall n \in (Nat),\; \forall m \in (Nat),\; (n \le m) \Rightarrow (((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le ((mu\left(Delta\right)\left(m\right)\left(z\right))).length)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.27 (mu length pos).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall z \in (Fin\left(d\right)),\; 0 < ((mu\left(Delta\right)\left(n\right)\left(z\right))).length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.28 (mu length triangle).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall u \in (Fin\left(d\right)),\; \forall v \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; (u \ne v) \Rightarrow (((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le (((mu\left(Delta\right)\left(n\right)\left(u\right))).length)+(((mu\left(Delta\right)\left(n\right)\left(v\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.29 (mu length at run start).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; ((n = 0) \lor (Delta\left(((n)-(1))\right) \ne Delta\left(n\right))) \Rightarrow (\forall z \in (Fin\left(d\right)),\; ((mu\left(Delta\right)\left(n\right)\left(z\right))).length \le (2)\cdot (((mu\left(Delta\right)\left(n\right)\left((Delta\left(n\right))\right))).length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_at_run_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.30 (mu constant run).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall a \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; (\forall i \in (Nat),\; (i < a) \Rightarrow (Delta\left(((n)+(i))\right) = x)) \Rightarrow (mu\left(Delta\right)\left(((n)+(a))\right)\left(z\right) = if (z = x) then (mu\left(Delta\right)\left(n\right)\left(x\right)) else (((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left((mu\left(Delta\right)\left(n\right)\left(x\right))\right)\left(a\right))++(mu\left(Delta\right)\left(n\right)\left(z\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_constant_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.31 (Lword).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; Lword\left(x\right)\left(w\right) = (w.flatMap\left((letterImage\left(x\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.Lword` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Definition 1.32 (Hword).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; Hword\left(x\right)\left(w\right) = ((Lword\left(x\right)\left(w\right))++([x]))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.Hword` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.33 (letterImage conjugacy).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; ([x])++(((letterImage\left(x\right)\left(z\right))).reverse) = (letterImage\left(x\right)\left(z\right))++([x])$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.34 (Hword reverse).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; ((Hword\left(x\right)\left(w\right))).reverse = Hword\left(x\right)\left(w.reverse\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_reverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

List.prod_hom_rel propagates the letter-image conjugacy through the word. Reversal therefore commutes with Hword; Hword_palindrome_iff uses this identity to characterize palindromes.

**Theorem 1.35 (Hword starts).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \exists r \in (List\left((Fin\left(d\right))\right)),\; Hword\left(x\right)\left(w\right) = (x)::(r)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.36 (Hword cons).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; Hword\left(x\right)\left(((z)::(w))\right) = if (z = x) then ((x)::(Hword\left(x\right)\left(w\right))) else ((x)::((z)::(Hword\left(x\right)\left(w\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.37 (Hword injective).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; Function.Injective\left((Hword\left(x\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.38 (Hword palindrome iff).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.Palindrome\left((Hword\left(x\right)\left(w\right))\right)) \Leftrightarrow (List.Palindrome\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palindrome_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.39 (Lword append).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall u \in (List\left((Fin\left(d\right))\right)),\; \forall v \in (List\left((Fin\left(d\right))\right)),\; Lword\left(x\right)\left(((u)++(v))\right) = (Lword\left(x\right)\left(u\right))++(Lword\left(x\right)\left(v\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.40 (Lword prefix).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall u \in (List\left((Fin\left(d\right))\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(u, w\right)) \Rightarrow (List.IsPrefix\left(Lword\left(x\right)\left(u\right), Lword\left(x\right)\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.41 (Hword suffix decode).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, Hword\left(x\right)\left(w\right)\right)) \Rightarrow ((\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (x)::(r)) \Rightarrow (\exists v \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(v, w\right)) \land (s = Hword\left(x\right)\left(v\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_suffix_decode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.42 (palindrome suffix last starts).**

$$\forall d \in (Nat),\; \forall z \in (Fin\left(d\right)),\; \forall p \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, (p)++([z])\right)) \Rightarrow ((List.Palindrome\left(s\right)) \Rightarrow ((s \ne []) \Rightarrow (\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (z)::(r))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_last_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.43 (palindrome suffix Hword starts).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, Hword\left(x\right)\left(w\right)\right)) \Rightarrow ((List.Palindrome\left(s\right)) \Rightarrow ((s \ne []) \Rightarrow (\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (x)::(r))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_Hword_starts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.44 (Hword palCut).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palCut\left((Hword\left(x\right)\left(w\right))\right) = ((Lword\left(x\right)\left((w.take\left((palCut\left(w\right))\right))\right))).length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.45 (Hword palClosure).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palClosure\left((Hword\left(x\right)\left(w\right))\right) = Hword\left(x\right)\left((palClosure\left(w\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_palClosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.46 (Lword suffix nonx).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (z \ne x) \Rightarrow ((List.IsSuffix\left(s, Lword\left(x\right)\left(w\right)\right)) \Rightarrow ((\exists r \in (List\left((Fin\left(d\right))\right)),\; s = (z)::(r)) \Rightarrow (List.IsSuffix\left(([x])++((s)++([x])), Hword\left(x\right)\left(w\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_suffix_nonx` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.47 (palCut le of suffix).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall s \in (List\left((Fin\left(d\right))\right)),\; (List.IsSuffix\left(s, w\right)) \Rightarrow ((List.Palindrome\left(s\right)) \Rightarrow (palCut\left(w\right) \le (w.length)-(s.length)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_le_of_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.48 (Lword palClosure).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall p \in (List\left((Fin\left(d\right))\right)),\; (z \ne x) \Rightarrow (palClosure\left((Lword\left(x\right)\left(((p)++([z]))\right))\right) = Hword\left(x\right)\left((palClosure\left(((p)++([z]))\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_palClosure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.49 (palClosure of palindrome).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.Palindrome\left(w\right)) \Rightarrow (palClosure\left(w\right) = w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_of_palindrome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.50 (Hword append letter closure).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall z \in (Fin\left(d\right)),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palClosure\left(((Hword\left(x\right)\left(w\right))++([z]))\right) = Hword\left(x\right)\left((palClosure\left(((w)++([z]))\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.Hword_append_letter_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.51 (central Justin).**

$$\forall d \in (Nat),\; \forall x \in (Fin\left(d\right)),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; central\left((cons\left(x\right)\left(Delta\right))\right)\left(((k)+(1))\right) = Hword\left(x\right)\left((central\left(Delta\right)\left(k\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin` (`✓ std3`). ∎

*Citation.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

Justin–Pirillo, equation (3): the palindromic-prefix morphism identity. Here cons is Mathlib Stream'.cons, which prepends one letter to a directive stream.

**Theorem 1.52 (central Justin shift).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; central\left(Delta\right)\left(((k)+(1))\right) = Hword\left((Delta\left(0\right))\right)\left((central\left((fun (n:Nat) \mapsto (Delta\left(((n)+(1))\right)))\right)\left(k\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin_shift` (`✓ std3`). ∎

*Citation.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

Justin–Pirillo, equation (3): the palindromic-prefix morphism identity.

**Definition 1.53 (muWord).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; muWord\left(Delta\right)\left(n\right)\left(w\right) = (w.flatMap\left((mu\left(Delta\right)\left(n\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.muWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.54 (mu shift).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall z \in (Fin\left(d\right)),\; mu\left(Delta\right)\left(((n)+(1))\right)\left(z\right) = Lword\left((Delta\left(0\right))\right)\left((mu\left((fun (j:Nat) \mapsto (Delta\left(((j)+(1))\right)))\right)\left(n\right)\left(z\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.mu_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.55 (central morphic finite).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; \forall k \in (Nat),\; central\left(Delta\right)\left(((n)+(k))\right) = (muWord\left(Delta\right)\left(n\right)\left((central\left((fun (j:Nat) \mapsto (Delta\left(((n)+(j))\right)))\right)\left(k\right))\right))++(central\left(Delta\right)\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.central_morphic_finite` (`✓ std3`). ∎

*Citation.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

Justin–Pirillo, equation (3): the palindromic-prefix morphism identity.

**Definition 1.56 (MorphicImage).**

$$\forall d \in (Nat),\; \forall source \in (((Nat) \to (Fin\left(d\right)))),\; \forall target \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; MorphicImage\left(source\right)\left(target\right)\left(f\right) = (\forall k \in (Nat),\; let W := (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(source\right)\left(k\right))).flatMap\left(f\right); (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(target\right)\left(W.length\right) = W)$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.MorphicImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.57 (wordPrefix isPrefix).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; \forall m \in (Nat),\; (k \le m) \Rightarrow (List.IsPrefix\left((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(k\right), (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(m\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_isPrefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.58 (cDelta morphicImage).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; MorphicImage\left((cDelta\left((fun (j:Nat) \mapsto (Delta\left(((n)+(j))\right)))\right))\right)\left((cDelta\left(Delta\right))\right)\left((mu\left(Delta\right)\left(n\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.cDelta_morphicImage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jacques Justin and Giuseppe Pirillo (2002). *Episturmian words and episturmian morphisms*. DOI: [10.1016/S0304-3975(01)00207-9](https://doi.org/10.1016/S0304-3975(01)00207-9). URL: <https://doi.org/10.1016/S0304-3975(01)00207-9>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.59 (HasPeriodOn).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall b \in (Nat),\; \forall e \in (Nat),\; HasPeriodOn\left(x\right)\left(q\right)\left(b\right)\left(e\right) = (\forall i \in (Nat),\; (b \le i) \Rightarrow (((i)+(q) < e) \Rightarrow (x\left(((i)+(q))\right) = x\left(i\right))))$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.HasPeriodOn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.60 (periodic interval mod).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall b \in (Nat),\; \forall e \in (Nat),\; (0 < q) \Rightarrow ((HasPeriodOn\left(x\right)\left(q\right)\left(b\right)\left(e\right)) \Rightarrow (\forall i \in (Nat),\; ((b)+(i) < e) \Rightarrow (x\left(((b)+(i))\right) = x\left(((b)+(Nat.mod\left(i, q\right)))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.periodic_interval_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion. Nat.mod(i, q) denotes the natural-number remainder i % q.

**Theorem 1.61 (periodic interval prefix).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall b \in (Nat),\; \forall ell \in (Nat),\; \forall e \in (Nat),\; (0 < q) \Rightarrow ((q \le ell) \Rightarrow (((b)+(ell) \le e) \Rightarrow ((HasPeriodOn\left(x\right)\left(q\right)\left(b\right)\left(e\right)) \Rightarrow (\exists V \in (List\left((Fin\left(d\right))\right)),\; \exists hV \in (V \ne []),\; (V.length = q) \land ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (i:Nat) \mapsto (x\left(((b)+(i))\right)))\right)\left(ell\right) = fractionalPower\left(V\right)\left(hV\right)\left(ell\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.periodic_interval_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.62 (wordPrefix append).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall u \in (Nat),\; \forall ell \in (Nat),\; (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(((u)+(ell))\right) = ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(u\right))++((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (x\left(((u)+(j))\right)))\right)\left(ell\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.63 (PeriodicRunCover).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall a \in (Nat),\; PeriodicRunCover x q a := \{ beginRun:((Nat) \to (Nat)); endRun:((Nat) \to (Nat)); (beginRun\left(0\right) = 0); (\forall k \in (Nat),\; (beginRun\left(k\right))+((a)\cdot (q)) \le endRun\left(k\right)); (\forall k \in (Nat),\; endRun\left(k\right) \le beginRun\left(((k)+(1))\right)); (\forall k \in (Nat),\; (beginRun\left(((k)+(1))\right))-(endRun\left(k\right)) \le (2)\cdot (q)); (\forall k \in (Nat),\; HasPeriodOn\left(x\right)\left(q\right)\left((beginRun\left(k\right))\right)\left((endRun\left(k\right))\right)); (\forall n \in (Nat),\; \exists k \in (Nat),\; n < endRun\left(k\right)) \}$$

*Formalization.* `D5/S1/Words/Episturmian/MorphicDecomposition.PeriodicRunCover` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The data fields and all proof-field types are listed in declaration order.

**Theorem 1.64 (run cover near period).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall a \in (Nat),\; \forall M \in (Nat),\; \forall n \in (Nat),\; \forall (\cdot :PeriodicRunCover\left(x\right)\left(q\right)\left(a\right)), ((HasPeriodOn\left(x\right)\left(q\right)\left(n\right)\left(((n)+((M)\cdot (q)))\right))) \lor (\exists u \in (Nat),\; (u \le (((M)+(2)))\cdot (q)) \land (HasPeriodOn\left(x\right)\left(q\right)\left(((n)+(u))\right)\left((((n)+(u))+((a)\cdot (q)))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.run_cover_near_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.65 (uniform finite window).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall a \in (Nat),\; \forall M \in (Nat),\; \forall n \in (Nat),\; (0 < q) \Rightarrow ((2 \le M) \Rightarrow (((M)\cdot (((M)+(3))) \le a) \Rightarrow (\forall (\cdot :PeriodicRunCover\left(x\right)\left(q\right)\left(a\right)), \exists U \in (List\left((Fin\left(d\right))\right)),\; \exists V \in (List\left((Fin\left(d\right))\right)),\; \exists ell \in (Nat),\; \exists hV \in (V \ne []),\; (V.length = q) \land ((V.length \le ell) \land ((U.length \le (((M)+(2)))\cdot (q)) \land (((M)\cdot (q) \le (U.length)+(ell)) \land (((U.length)+(ell) \le ((((a)+(M))+(2)))\cdot (q)) \land (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (x\left(((n)+(j))\right)))\right)\left(((U.length)+(ell))\right) = (U)++(fractionalPower\left(V\right)\left(hV\right)\left(ell\right))) \land (((M:Real)) \le ((((U.length)+(ell):Real)))/(((U.length)+(V.length))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.uniform_finite_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Every position has a finite window containing a fractional power with the stated length and ratio bounds.

**Theorem 1.66 (wordPower add).**

$$\forall d \in (Nat),\; \forall A \in (List\left((Fin\left(d\right))\right)),\; \forall r \in (Nat),\; \forall s \in (Nat),\; (\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(((r)+(s))\right) = ((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(r\right))++((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.wordPower_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.67 (wordPower period).**

$$\forall d \in (Nat),\; \forall A \in (List\left((Fin\left(d\right))\right)),\; \forall r \in (Nat),\; List.HasPeriod\left(((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(r\right))\right)\left(A.length\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.wordPower_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.68 (wordPrefix constant).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall x \in (Fin\left(d\right)),\; \forall a \in (Nat),\; (\forall j \in (Nat),\; (j < a) \Rightarrow (s\left(j\right) = x)) \Rightarrow ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(s\right)\left(a\right) = List.replicate\left(a\right)\left(x\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

## References

- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.BoundedPQ`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.DioAdmissible`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.HasPeriodOn`
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
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lang`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_append`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_palClosure`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.Lword_suffix_nonx`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.MorphicImage`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.PeriodicRunCover`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.cDelta`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.cDelta_morphicImage`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_Justin_shift`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_get_eq_cDelta`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_is_cDelta_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_length_ge`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_morphic_finite`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_of_le`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.central_prefix_succ`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.claim`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.closure_candidate_palindrome`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.dio`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.fractionalPower`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.letterImage_conjugacy`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.muWord`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_constant_run`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_at_run_start`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_mono`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_pos`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_step`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_length_triangle`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.mu_shift`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_formula_cut`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_of_palindrome`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palClosure_spec`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palCut`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_le_of_suffix`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_min`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palCut_spec`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_extension_length`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_extension_middle`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_Hword_starts`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.palindrome_suffix_last_starts`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.periodic_interval_mod`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.periodic_interval_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.run_cover_near_period`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.uniform_finite_window`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.wordPower_add`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.wordPower_period`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_append`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_constant`
- Truth anchor: `D5/S1/Words/Episturmian/MorphicDecomposition.wordPrefix_isPrefix`
- Dependency: [D5/S1/Words/MBonacciSentinelDesubstitution](../MBonacciSentinelDesubstitution.md)
