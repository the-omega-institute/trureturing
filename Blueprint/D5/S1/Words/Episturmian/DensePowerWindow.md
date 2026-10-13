# DensePowerWindow

## Abstract

Episturmian words: DensePowerWindow.

**Definition 1.1 (HasPeriodOn).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall b \in (Nat),\; \forall e \in (Nat),\; HasPeriodOn\left(x\right)\left(q\right)\left(b\right)\left(e\right) = (\forall i \in (Nat),\; (b \le i) \Rightarrow (((i)+(q) < e) \Rightarrow (x\left(((i)+(q))\right) = x\left(i\right))))$$

*Formalization.* `D5/S1/Words/Episturmian/DensePowerWindow.HasPeriodOn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.2 (periodic interval mod).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall b \in (Nat),\; \forall e \in (Nat),\; (0 < q) \Rightarrow ((HasPeriodOn\left(x\right)\left(q\right)\left(b\right)\left(e\right)) \Rightarrow (\forall i \in (Nat),\; ((b)+(i) < e) \Rightarrow (x\left(((b)+(i))\right) = x\left(((b)+(Nat.mod\left(i, q\right)))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.periodic_interval_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion. Nat.mod(i, q) denotes the natural-number remainder i % q.

**Theorem 1.3 (periodic interval prefix).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall b \in (Nat),\; \forall ell \in (Nat),\; \forall e \in (Nat),\; (0 < q) \Rightarrow ((q \le ell) \Rightarrow (((b)+(ell) \le e) \Rightarrow ((HasPeriodOn\left(x\right)\left(q\right)\left(b\right)\left(e\right)) \Rightarrow (\exists V \in (List\left((Fin\left(d\right))\right)),\; \exists hV \in (V \ne []),\; (V.length = q) \land ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (i:Nat) \mapsto (x\left(((b)+(i))\right)))\right)\left(ell\right) = fractionalPower\left(V\right)\left(hV\right)\left(ell\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.periodic_interval_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.4 (wordPrefix append).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall u \in (Nat),\; \forall ell \in (Nat),\; (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(((u)+(ell))\right) = ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(u\right))++((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (x\left(((u)+(j))\right)))\right)\left(ell\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.wordPrefix_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.5 (PeriodicRunCover).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall a \in (Nat),\; PeriodicRunCover x q a := \{ beginRun:((Nat) \to (Nat)); endRun:((Nat) \to (Nat)); (beginRun\left(0\right) = 0); (\forall k \in (Nat),\; (beginRun\left(k\right))+((a)\cdot (q)) \le endRun\left(k\right)); (\forall k \in (Nat),\; endRun\left(k\right) \le beginRun\left(((k)+(1))\right)); (\forall k \in (Nat),\; (beginRun\left(((k)+(1))\right))-(endRun\left(k\right)) \le (2)\cdot (q)); (\forall k \in (Nat),\; HasPeriodOn\left(x\right)\left(q\right)\left((beginRun\left(k\right))\right)\left((endRun\left(k\right))\right)); (\forall n \in (Nat),\; \exists k \in (Nat),\; n < endRun\left(k\right)) \}$$

*Formalization.* `D5/S1/Words/Episturmian/DensePowerWindow.PeriodicRunCover` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The data fields and all proof-field types are listed in declaration order.

**Theorem 1.6 (run cover near period).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall a \in (Nat),\; \forall M \in (Nat),\; \forall n \in (Nat),\; \forall (\cdot :PeriodicRunCover\left(x\right)\left(q\right)\left(a\right)), ((HasPeriodOn\left(x\right)\left(q\right)\left(n\right)\left(((n)+((M)\cdot (q)))\right))) \lor (\exists u \in (Nat),\; (u \le (((M)+(2)))\cdot (q)) \land (HasPeriodOn\left(x\right)\left(q\right)\left(((n)+(u))\right)\left((((n)+(u))+((a)\cdot (q)))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.run_cover_near_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.7 (uniform finite window).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall a \in (Nat),\; \forall M \in (Nat),\; \forall n \in (Nat),\; (0 < q) \Rightarrow ((2 \le M) \Rightarrow (((M)\cdot (((M)+(3))) \le a) \Rightarrow (\forall (\cdot :PeriodicRunCover\left(x\right)\left(q\right)\left(a\right)), \exists U \in (List\left((Fin\left(d\right))\right)),\; \exists V \in (List\left((Fin\left(d\right))\right)),\; \exists ell \in (Nat),\; \exists hV \in (V \ne []),\; (V.length = q) \land ((V.length \le ell) \land ((U.length \le (((M)+(2)))\cdot (q)) \land (((M)\cdot (q) \le (U.length)+(ell)) \land (((U.length)+(ell) \le ((((a)+(M))+(2)))\cdot (q)) \land (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (x\left(((n)+(j))\right)))\right)\left(((U.length)+(ell))\right) = (U)++(fractionalPower\left(V\right)\left(hV\right)\left(ell\right))) \land (((M:Real)) \le ((((U.length)+(ell):Real)))/(((U.length)+(V.length))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.uniform_finite_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Every position has a finite window containing a fractional power with the stated length and ratio bounds.

**Theorem 1.8 (wordPower add).**

$$\forall d \in (Nat),\; \forall A \in (List\left((Fin\left(d\right))\right)),\; \forall r \in (Nat),\; \forall s \in (Nat),\; (\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(((r)+(s))\right) = ((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(r\right))++((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(s\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.wordPower_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.9 (wordPower period).**

$$\forall d \in (Nat),\; \forall A \in (List\left((Fin\left(d\right))\right)),\; \forall r \in (Nat),\; List.HasPeriod\left(((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(r\right))\right)\left(A.length\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.wordPower_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.10 (wordPrefix constant).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall x \in (Fin\left(d\right)),\; \forall a \in (Nat),\; (\forall j \in (Nat),\; (j < a) \Rightarrow (s\left(j\right) = x)) \Rightarrow ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(s\right)\left(a\right) = List.replicate\left(a\right)\left(x\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.wordPrefix_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.11 (imagePrefix).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; \forall k \in (Nat),\; imagePrefix\left(s\right)\left(f\right)\left(k\right) = ((((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(s\right)\left(k\right))).flatMap\left(f\right))$$

*Formalization.* `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed equations define the object.

**Theorem 1.12 (imagePrefix add).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; \forall k \in (Nat),\; \forall j \in (Nat),\; imagePrefix\left(s\right)\left(f\right)\left(((k)+(j))\right) = (imagePrefix\left(s\right)\left(f\right)\left(k\right))++(imagePrefix\left((fun (i:Nat) \mapsto (s\left(((k)+(i))\right)))\right)\left(f\right)\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.13 (imagePrefix succ).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; \forall k \in (Nat),\; imagePrefix\left(s\right)\left(f\right)\left(((k)+(1))\right) = (imagePrefix\left(s\right)\left(f\right)\left(k\right))++(f\left((s\left(k\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.14 (imagePrefix length ge).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; (\forall z \in (Fin\left(d\right)),\; 0 < ((f\left(z\right))).length) \Rightarrow (\forall k \in (Nat),\; k \le ((imagePrefix\left(s\right)\left(f\right)\left(k\right))).length)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix_length_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Definition 1.15 (PowerChunk).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; \forall A \in (List\left((Fin\left(d\right))\right)),\; \forall a \in (Nat),\; \forall p \in (Nat),\; PowerChunk s f A a p := \{ step:Nat; copies:Nat; sep:List\left((Fin\left(d\right))\right); (0 < step); (a \le copies); (sep.length \le (2)\cdot (A.length)); (imagePrefix\left((fun (j:Nat) \mapsto (s\left(((p)+(j))\right)))\right)\left(f\right)\left(step\right) = ((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(copies\right))++(sep)) \}$$

*Formalization.* `D5/S1/Words/Episturmian/DensePowerWindow.PowerChunk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The data fields and all proof-field types are listed in declaration order.

**Theorem 1.16 (powerChunk exists).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; \forall A \in (List\left((Fin\left(d\right))\right)),\; \forall B \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; \forall x \in (Fin\left(d\right)),\; \forall a \in (Nat),\; \forall p \in (Nat),\; (0 < a) \Rightarrow ((f\left(x\right) = A) \Rightarrow ((\forall z \in (Fin\left(d\right)),\; (z \ne x) \Rightarrow (f\left(z\right) = ((\lambda (W:List\left(Fin\left(d\right)\right)), \lambda (a:Nat), wordPower\left(a, W\right))\left(A\right)\left(a\right))++(B\left(z\right)))) \Rightarrow ((\forall z \in (Fin\left(d\right)),\; ((B\left(z\right))).length \le (2)\cdot (A.length)) \Rightarrow (Nonempty\left((PowerChunk\left(s\right)\left(f\right)\left(A\right)\left(a\right)\left(p\right))\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.powerChunk_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.17 (morphicImage segment).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; (MorphicImage\left(s\right)\left(t\right)\left(f\right)) \Rightarrow (\forall p \in (Nat),\; \forall step \in (Nat),\; \forall W \in (List\left((Fin\left(d\right))\right)),\; \forall S \in (List\left((Fin\left(d\right))\right)),\; (imagePrefix\left((fun (j:Nat) \mapsto (s\left(((p)+(j))\right)))\right)\left(f\right)\left(step\right) = (W)++(S)) \Rightarrow (\forall j \in (Nat),\; (j < W.length) \Rightarrow (t\left(((((imagePrefix\left(s\right)\left(f\right)\left(p\right))).length)+(j))\right) = (W)[j])))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.morphicImage_segment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.18 (periodOn of segment).**

$$\forall d \in (Nat),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall W \in (List\left((Fin\left(d\right))\right)),\; \forall b \in (Nat),\; \forall q \in (Nat),\; (\forall j \in (Nat),\; (j < W.length) \Rightarrow (t\left(((b)+(j))\right) = (W)[j])) \Rightarrow ((List.HasPeriod\left(W\right)\left(q\right)) \Rightarrow (HasPeriodOn\left(t\right)\left(q\right)\left(b\right)\left(((b)+(W.length))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.periodOn_of_segment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.19 (powerChunks cover).**

$$\forall d \in (Nat),\; \forall s \in (((Nat) \to (Fin\left(d\right)))),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall f \in (((Fin\left(d\right)) \to (List\left((Fin\left(d\right))\right)))),\; \forall A \in (List\left((Fin\left(d\right))\right)),\; \forall a \in (Nat),\; (MorphicImage\left(s\right)\left(t\right)\left(f\right)) \Rightarrow ((\forall z \in (Fin\left(d\right)),\; 0 < ((f\left(z\right))).length) \Rightarrow (\forall (\cdot :\forall p \in (Nat),\; Nonempty\left((PowerChunk\left(s\right)\left(f\right)\left(A\right)\left(a\right)\left(p\right))\right)), Nonempty\left((PeriodicRunCover\left(t\right)\left(A.length\right)\left(a\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.powerChunks_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.20 (wordPrefix mem Lang).**

$$\forall d \in (Nat),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall H \in (Nat),\; (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(x\right)\left(H\right) \in Lang\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.wordPrefix_mem_Lang` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.21 (language prefix occurrence).**

$$\forall d \in (Nat),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall H \in (Nat),\; (Lang\left(t\right) = Lang\left(x\right)) \Rightarrow (\exists n \in (Nat),\; \forall ell \in (Nat),\; (ell \le H) \Rightarrow ((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(t\right)\left(ell\right) = (\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left((fun (j:Nat) \mapsto (x\left(((n)+(j))\right)))\right)\left(ell\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.language_prefix_occurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

The displayed statement gives the complete hypotheses and conclusion.

**Theorem 1.22 (uniform window transfer).**

$$\forall d \in (Nat),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; \forall q \in (Nat),\; \forall a \in (Nat),\; \forall M \in (Nat),\; (Lang\left(t\right) = Lang\left(x\right)) \Rightarrow ((0 < q) \Rightarrow ((2 \le M) \Rightarrow (((M)\cdot (((M)+(3))) \le a) \Rightarrow (\forall (\cdot :PeriodicRunCover\left(x\right)\left(q\right)\left(a\right)), \exists U \in (List\left((Fin\left(d\right))\right)),\; \exists V \in (List\left((Fin\left(d\right))\right)),\; \exists ell \in (Nat),\; \exists hV \in (V \ne []),\; (V.length = q) \land ((V.length \le ell) \land ((U.length \le (((M)+(2)))\cdot (q)) \land (((M)\cdot (q) \le (U.length)+(ell)) \land (((U.length)+(ell) \le ((((a)+(M))+(2)))\cdot (q)) \land (((\lambda (z:((Nat) \to (Fin\left(d\right)))), \lambda (n:Nat), factor\left(z, 0, n\right))\left(t\right)\left(((U.length)+(ell))\right) = (U)++(fractionalPower\left(V\right)\left(hV\right)\left(ell\right))) \land (((M:Real)) \le ((((U.length)+(ell):Real)))/(((U.length)+(V.length)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.uniform_window_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Equality of factor languages transfers the finite-window bound to the prefix of the other word.

**Theorem 1.23 (arbitrarily dense powers dio top).**

$$\forall d \in (Nat),\; \forall t \in (((Nat) \to (Fin\left(d\right)))),\; \forall x \in (((Nat) \to (Fin\left(d\right)))),\; (Lang\left(t\right) = Lang\left(x\right)) \Rightarrow ((\forall M \in (Nat),\; (2 \le M) \Rightarrow (\exists q \in (Nat),\; \exists a \in (Nat),\; (0 < q) \land (((M)\cdot (((M)+(3))) \le a) \land (Nonempty\left((PeriodicRunCover\left(x\right)\left(q\right)\left(a\right))\right))))) \Rightarrow (dio\left(t\right) = \infty))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Episturmian/DensePowerWindow.arbitrarily_dense_powers_dio_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Peltomäki (2024). *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*. DOI: [10.1016/j.ejc.2024.103942](https://doi.org/10.1016/j.ejc.2024.103942). URL: <https://arxiv.org/abs/2103.08351v3>.

*Commentary.*

Uniformly available fractional powers of arbitrarily high ratio make the Diophantine exponent infinite.

## References

- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.HasPeriodOn`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.PeriodicRunCover`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.PowerChunk`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.arbitrarily_dense_powers_dio_top`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix_add`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix_length_ge`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.imagePrefix_succ`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.language_prefix_occurrence`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.morphicImage_segment`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.periodOn_of_segment`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.periodic_interval_mod`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.periodic_interval_prefix`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.powerChunk_exists`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.powerChunks_cover`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.run_cover_near_period`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.uniform_finite_window`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.uniform_window_transfer`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.wordPower_add`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.wordPower_period`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.wordPrefix_append`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.wordPrefix_constant`
- Truth anchor: `D5/S1/Words/Episturmian/DensePowerWindow.wordPrefix_mem_Lang`
- Dependency: [D5/S1/Words/Episturmian/MorphicDecomposition](MorphicDecomposition.md)
