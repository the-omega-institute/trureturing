# PalindromicClosure

## Abstract

Episturmian words: PalindromicClosure.

**Definition 1.1 (palClosure).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall h \in (\exists n \in (Nat),\; \exists p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \land ((List.Palindrome\left(p\right)) \land (p.length = n))),\; \forall hp \in (\exists p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \land ((List.Palindrome\left(p\right)) \land (p.length = Nat.find\left(h\right)))),\; palClosure\left(w\right) = Classical.choose\left(hp\right)$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.palClosure` (`✓ std3`).

*Citation.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

Droubay–Justin–Pirillo, Section 2: the palindromic closure construction. The evidence for the least length and its palindrome is quantified explicitly; proof irrelevance makes Classical.choose independent of these proof terms.

**Theorem 1.2 (palClosure spec).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, palClosure\left(w\right)\right)) \land ((List.Palindrome\left((palClosure\left(w\right))\right)) \land (\forall p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \Rightarrow ((List.Palindrome\left(p\right)) \Rightarrow (((palClosure\left(w\right))).length \le p.length))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.palClosure_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.3 (palCut).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall h \in (\exists k \in (Nat),\; (k \le w.length) \land (List.Palindrome\left((w.drop\left(k\right))\right))),\; palCut\left(w\right) = Nat.find\left(h\right)$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.palCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The least cut leaves a palindromic suffix. Existence proof arguments are displayed as quantified evidence; proof irrelevance makes Nat.find independent of the evidence.

**Theorem 1.4 (palCut spec).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; (palCut\left(w\right) \le w.length) \land (List.Palindrome\left((w.drop\left((palCut\left(w\right))\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.palCut_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.5 (palCut min).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall k \in (Nat),\; (k \le w.length) \Rightarrow ((List.Palindrome\left((w.drop\left(k\right))\right)) \Rightarrow (palCut\left(w\right) \le k))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.palCut_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.6 (palindrome extension middle).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall r \in (List\left((Fin\left(d\right))\right)),\; (List.Palindrome\left(((w)++(r))\right)) \Rightarrow ((r.length \le w.length) \Rightarrow (List.Palindrome\left((w.drop\left(r.length\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.palindrome_extension_middle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.7 (palindrome extension length).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; \forall p \in (List\left((Fin\left(d\right))\right)),\; (List.IsPrefix\left(w, p\right)) \Rightarrow ((List.Palindrome\left(p\right)) \Rightarrow ((w.length)+(palCut\left(w\right)) \le p.length))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.palindrome_extension_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.8 (closure candidate palindrome).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; List.Palindrome\left(((w)++(((w.take\left((palCut\left(w\right))\right))).reverse))\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.closure_candidate_palindrome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.9 (palClosure formula cut).**

$$\forall d \in (Nat),\; \forall w \in (List\left((Fin\left(d\right))\right)),\; palClosure\left(w\right) = (w)++(((w.take\left((palCut\left(w\right))\right))).reverse)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.palClosure_formula_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.10 (central).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; (central\left(Delta\right)\left((0)\right) = []) \land (\forall k \in (Nat),\; central\left(Delta\right)\left(((k)+(1))\right) = palClosure\left(((central\left(Delta\right)\left(k\right))++([Delta\left(k\right)]))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.central` (`✓ std3`).

*Citation.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

Droubay–Justin–Pirillo, Section 2: the palindromic closure construction.

**Theorem 1.11 (central length ge).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall k \in (Nat),\; k \le ((central\left(Delta\right)\left(k\right))).length$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/PalindromicClosure.central_length_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.12 (cDelta).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall n \in (Nat),\; cDelta\left(Delta\right)\left(n\right) = ((central\left(Delta\right)\left(((n)+(1))\right))).get\left(\langle n\rangle \right)$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.cDelta` (`✓ std3`).

*Citation.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

Droubay–Justin–Pirillo, Section 2: the palindromic closure construction. The Fin index shows its value; its inequality proof is implicit.

**Definition 1.13 (Lang).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; Lang\left(x\right) = (\{ w:List\left((Fin\left(d\right))\right) \mid \exists i \in (Nat),\; \forall j \in (Fin\left(w.length\right)),\; w.get\left(j\right) = x\left(((i)+(\operatorname{val}\left(j\right)))\right) \})$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.Lang` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Section 2: episturmian words, directive words and partial quotients.

**Definition 1.14 (BoundedPQ).**

$$\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; BoundedPQ\left(Delta\right) = (\exists B \in (Nat),\; \forall i \in (Nat),\; \exists j \in (Nat),\; (j < B) \land (Delta\left(((i)+(j))\right) \ne Delta\left(i\right)))$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.BoundedPQ` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Section 2: episturmian words, directive words and partial quotients.

**Definition 1.15 (fractionalPower).**

$$\forall d \in (Nat),\; \forall V \in (List\left((Fin\left(d\right))\right)),\; \forall hV \in (V \ne []),\; \forall ell \in (Nat),\; fractionalPower\left(V\right)\left(hV\right)\left(ell\right) = ((List.range\left(ell\right))).map\left((fun (i:Nat) \mapsto (V.get\left(\langle Nat.mod\left(i, V.length\right)\rangle \right)))\right)$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.fractionalPower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xavier Droubay and Jacques Justin and Giuseppe Pirillo (2001). *Episturmian words and some constructions of de Luca and Rauzy*. DOI: [10.1016/S0304-3975(99)00320-5](https://doi.org/10.1016/S0304-3975(99)00320-5). URL: <https://doi.org/10.1016/S0304-3975(99)00320-5>.

*Commentary.*

The displayed equations define the object. The Fin index shows its value; its inequality proof is implicit. Nat.mod(i, q) denotes the natural-number remainder i % q.

**Definition 1.16 (DioAdmissible).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall rho \in (NNReal),\; DioAdmissible\left(x\right)\left(rho\right) = (\forall L \in (Nat),\; \exists U \in (List\left((Fin\left(d\right))\right)),\; \exists V \in (List\left((Fin\left(d\right))\right)),\; \exists ell \in (Nat),\; \exists hV \in (V \ne []),\; (V.length \le ell) \land (((U.length)+(ell) \ge L) \land (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(((U.length)+(ell))\right) = (U)++(fractionalPower\left(V\right)\left(hV\right)\left(ell\right))) \land (((((U.length)+(ell):Real)))/(((U.length)+(V.length))) \ge ((rho:Real))))))$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.DioAdmissible` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Definition 1.1.

**Definition 1.17 (dio).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; dio\left(x\right) = (iSup\left(fun (rho:NNReal) \mapsto (iSup\left(fun (\cdot :DioAdmissible\left(x\right)\left(rho\right)) \mapsto (((rho:ENNReal)))\right))\right))$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.dio` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Peltomäki, Definition 1.1.

**Definition 1.18 (claim).**

$$claim = (\forall d \in (Nat),\; \forall Delta \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; (Lang\left(t\right) = Lang\left((cDelta\left(Delta\right))\right)) \Rightarrow ((\neg (\exists N \in (Nat),\; \exists p \in (Nat),\; (0 < p) \land (\forall n \in (Nat),\; (N \le n) \Rightarrow (t\left((n+p)\right) = t\left(n\right))))) \Rightarrow (((dio\left(t\right) < \infty) \Leftrightarrow (BoundedPQ\left(Delta\right))))))$$

*Formalization.* `D5/S1/Words/Episturmian/PalindromicClosure.claim` (`✓ std3`).

*Citation.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Let $\mathbf{t}$ be an aperiodic episturmian word. Then $dio\left(\mathbf{t}\right) < \infty$ if and only if $\mathbf{t}$ has bounded partial quotients.

Peltomäki, Conjecture 8.4, Section 8.

Peltomäki, Conjecture 8.4, Section 8.

## References

- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.BoundedPQ`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.DioAdmissible`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.Lang`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.cDelta`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.central`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.central_length_ge`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.claim`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.closure_candidate_palindrome`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.dio`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.fractionalPower`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palClosure`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palClosure_formula_cut`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palClosure_spec`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palCut`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palCut_min`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palCut_spec`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palindrome_extension_length`
- Truth anchor: `D5/S1/Words/Episturmian/PalindromicClosure.palindrome_extension_middle`
- Dependency: [D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs](../AbelianBorders/AbelianBorderQuestionDefs.md)
