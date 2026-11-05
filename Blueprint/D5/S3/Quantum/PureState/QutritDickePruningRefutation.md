# A missing amplitude in the pruned qutrit Dicke circuit

## Abstract

The pruned qutrit circuit has zero amplitude at a word required by the Dicke state with occupation (1,3,1).

**Definition 1.1 (Real amplitudes on qutrit words).**

$$\forall (n: \mathbb{N}), (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right) = \left((\operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)) \to (\mathbb{R})\right))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.State` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

An n-qutrit amplitude function assigns a real number to each word Fin n → Fin 3. No normalization condition is imposed on this function space.

**Definition 1.2 (Three occupation counts).**

$$\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation} = \left((\operatorname{Fin}\left(3\right)) \to (\mathbb{N})\right)$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.Occupation` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

An occupation vector assigns a natural count to each of the three letters, as in qdit_v3.tex, lines 177–178. The type alone imposes no condition on the sum of the counts.

**Definition 1.3 (Reading a wire).**

$$\forall (n: \mathbb{N}), (\forall (t: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)), (\forall (r: \mathbb{N}), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.wire}\left(t, r\right): \operatorname{Fin}\left(3\right)) = \operatorname{dite}\left(r < n, \lambda (h: r < n) \mapsto (t\left(\operatorname{Fin.mk}\left(r, h\right)\right)), \operatorname{Function.const}\left((\neg (r < n)), (0: \operatorname{Fin}\left(3\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.wire` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

Wire numbers increase from right to left. A read at r < n returns the letter at the corresponding finite index; a read outside the register returns the letter zero. The bound proof h supplies the finite index.

**Definition 1.4 (Updating a wire).**

$$\forall (n: \mathbb{N}), (\forall (t: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)), (\forall (r: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(3\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.put}\left(t, r, a\right): \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)) = \operatorname{dite}\left(r < n, \lambda (h: r < n) \mapsto (\operatorname{Function.update}\left(t, \operatorname{Fin.mk}\left(r, h\right), a\right)), \operatorname{Function.const}\left((\neg (r < n)), t\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.put` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

An update replaces the letter on wire r when r < n and otherwise leaves the word unchanged. The dependent conditional uses h to form the finite index; its other branch is a constant function on the negated bound.

**Definition 1.5 (Testing all controls).**

$$\forall (n: \mathbb{N}), (\forall (controls: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right)), (\forall (t: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlsHold}\left(controls, t\right): \operatorname{Bool}) = \operatorname{List.all}\left(controls, \lambda (p: \mathbb{N} \times \operatorname{Fin}\left(3\right)) \mapsto (\operatorname{Bool.and}\left(\operatorname{Decidable.decide}\left(\operatorname{Prod.fst}\left(p\right) < n\right), \operatorname{Decidable.decide}\left(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.wire}\left(t, \operatorname{Prod.fst}\left(p\right)\right) = \operatorname{Prod.snd}\left(p\right)\right)\right))\right))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.controlsHold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

A list of controls consists of wire and letter pairs. The Boolean test is true precisely when every listed wire lies in the register and carries its specified letter. An empty list passes the test.

**Definition 1.6 (A controlled exchange).**

$$\forall (n: \mathbb{N}), (\forall (target: \mathbb{N}), (\forall (controls: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right)), (\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledX}\left(target, controls, i, j, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \lambda (t: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)) \mapsto (\operatorname{ite}\left((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlsHold}\left(controls, t\right) = \operatorname{Bool.true}), f\left(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.put}\left(t, target, \operatorname{Equiv.swap}\left(i, j\right)\left(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.wire}\left(t, target\right)\right)\right)\right), f\left(t\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.controlledX` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The controlled exchange from qdit_v3.tex, lines 485–499 and 513–527, uses the swap of letters i and j. At a word satisfying all controls, the amplitude is read from f at that word with its target letter swapped; otherwise it is read from f at the original word. For controls on wires distinct from the target, this is the inverse basis permutation. The displayed extension permits arbitrary control lists and target indices, using wire and put as defined above.

**Definition 1.7 (A controlled real rotation).**

$$\forall (n: \mathbb{N}), (\forall (target: \mathbb{N}), (\forall (controls: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right)), (\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), (\forall (c: \mathbb{R}), (\forall (s: \mathbb{R}), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledR}\left(target, controls, i, j, c, s, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \lambda (t: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)) \mapsto (\operatorname{ite}\left((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlsHold}\left(controls, t\right) = \operatorname{Bool.true}), \operatorname{ite}\left((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.wire}\left(t, target\right) = i), ((c) \cdot (f\left(t\right))) - ((s) \cdot (f\left(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.put}\left(t, target, j\right)\right))), \operatorname{ite}\left((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.wire}\left(t, target\right) = j), ((s) \cdot (f\left(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.put}\left(t, target, i\right)\right))) + ((c) \cdot (f\left(t\right))), f\left(t\right)\right)\right), f\left(t\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.controlledR` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

For distinct i and j, the rotation in qdit_v3.tex, lines 501–509, has rows (c,−s) and (s,c) on the i,j coordinates. It leaves other target letters unchanged and acts only when every control holds. Here c and s are arbitrary real parameters; the later circuits choose their square-root values. There is no assumption i ≠ j in this definition, so the first conditional takes precedence when the two letters coincide.

**Definition 1.8 (The exchange–rotation–exchange circuit).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (l: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.V}\left(n, m, l, i, j, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \operatorname{let} (off: \mathbb{N}) = ((n) - (m)); (\operatorname{let} (x: (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \to (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right))) = (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledX}\left((off) + (l), [(off, j)], i, j\right)); (\operatorname{let} (cs: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right)) = (\operatorname{List.append}\left(\operatorname{List.append}\left([((off) + (l), j)], \operatorname{ite}\left((2 \le l), [((off) + ((l) - (1)), j)], ([]: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right))\right)\right), \operatorname{ite}\left(((0 < \operatorname{Fin.val}\left(i\right)) \land (l \le (m) - (2))), [((off) + ((m) - (1)), i)], ([]: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right))\right)\right)); (x\left(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledR}\left(off, cs, i, j, \operatorname{Real.sqrt}\left(\frac{(\operatorname{Nat.cast}\left(l\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(m\right): \mathbb{R})}\right), -(\operatorname{Real.sqrt}\left(((1: \mathbb{R})) - (\frac{(\operatorname{Nat.cast}\left(l\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(m\right): \mathbb{R})})\right)), x\left(f\right)\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.V` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The V circuit is given in qdit_v3.tex, lines 598–696, with the angle specified in lines 326–332. The offset n − m places its local wire zero at global wire n − m. The exchange x acts first and last. Between them, the rotation acts on the offset wire, with cosine √(l/m) and sine −√(1−l/m). The predecessor control is omitted for l < 2; the control at the last local wire is included exactly when i.val > 0 and l ≤ m − 2. Subtractions of wire indices are natural subtraction; both l and m are cast to real numbers before division.

**Definition 1.9 (The three two-letter circuits).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (l: \mathbb{N}), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.I}\left(n, m, l, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.V}\left(n, m, l, (1: \operatorname{Fin}\left(3\right)), (2: \operatorname{Fin}\left(3\right)), \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.V}\left(n, m, l, (0: \operatorname{Fin}\left(3\right)), (2: \operatorname{Fin}\left(3\right)), \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.V}\left(n, m, l, (0: \operatorname{Fin}\left(3\right)), (1: \operatorname{Fin}\left(3\right)), f\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.I` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The product in qdit_v3.tex, lines 612–619, applies V for the letter pairs (0,1), (0,2), then (1,2). Function application makes the rightmost circuit act first.

**Definition 1.10 (The circuit with two rotations).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (l_{1}: \mathbb{N}), (\forall (l_{2}: \mathbb{N}), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.II}\left(n, m, l_{1}, l_{2}, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \operatorname{let} (off: \mathbb{N}) = ((n) - (m)); (\operatorname{let} (x: (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \to (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right))) = (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledX}\left((off) + (l_{2}), [(off, (2: \operatorname{Fin}\left(3\right)))], (1: \operatorname{Fin}\left(3\right)), (2: \operatorname{Fin}\left(3\right))\right)); (\operatorname{let} (y: (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \to (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right))) = (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledX}\left((off) + (l_{1}), [(off, (1: \operatorname{Fin}\left(3\right)))], (0: \operatorname{Fin}\left(3\right)), (1: \operatorname{Fin}\left(3\right))\right)); (\operatorname{let} (cs: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right)) = (\operatorname{List.append}\left(\operatorname{List.append}\left([((off) + (l_{2}), (2: \operatorname{Fin}\left(3\right)))], \operatorname{ite}\left((2 \le l_{2}), [((off) + ((l_{2}) - (1)), (2: \operatorname{Fin}\left(3\right)))], ([]: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right))\right)\right), \operatorname{ite}\left((l_{2} < (l_{1}) - (1)), [((off) + ((l_{1}) - (1)), (1: \operatorname{Fin}\left(3\right)))], ([]: \operatorname{List}\left((\mathbb{N} \times \operatorname{Fin}\left(3\right))\right))\right)\right)); (\operatorname{let} (r_{1}: (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \to (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right))) = (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledR}\left(off, \operatorname{List.cons}\left(((off) + (l_{1}), (0: \operatorname{Fin}\left(3\right))), cs\right), (1: \operatorname{Fin}\left(3\right)), (2: \operatorname{Fin}\left(3\right)), \operatorname{Real.sqrt}\left(\frac{(\operatorname{Nat.cast}\left(l_{2}\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(m\right): \mathbb{R})}\right), -(\operatorname{Real.sqrt}\left(((1: \mathbb{R})) - (\frac{(\operatorname{Nat.cast}\left(l_{2}\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(m\right): \mathbb{R})})\right))\right)); (\operatorname{let} (r_{2}: (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \to (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right))) = (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.controlledR}\left(off, \operatorname{List.cons}\left(((off) + (l_{1}), (1: \operatorname{Fin}\left(3\right))), cs\right), (0: \operatorname{Fin}\left(3\right)), (1: \operatorname{Fin}\left(3\right)), \operatorname{Real.sqrt}\left(\frac{(\operatorname{Nat.cast}\left(((l_{1}) - (l_{2}): \mathbb{N})\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(((m) - (l_{2}): \mathbb{N})\right): \mathbb{R})}\right), -(\operatorname{Real.sqrt}\left(((1: \mathbb{R})) - (\frac{(\operatorname{Nat.cast}\left(((l_{1}) - (l_{2}): \mathbb{N})\right): \mathbb{R})}{(\operatorname{Nat.cast}\left(((m) - (l_{2}): \mathbb{N})\right): \mathbb{R})})\right))\right)); (y\left(\left(r_{2}\right)\left(y\left(x\left(\left(r_{1}\right)\left(x\left(f\right)\right)\right)\right)\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.II` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The two-rotation circuit and its boundary cases are given in qdit_v3.tex, lines 736–881. Its time order is x, r₁, x, y, r₂, y. Both rotations use the common list cs, with one additional control at off + l₁. The controls at off + (l₂ − 1) and off + (l₁ − 1) are omitted at the indicated boundaries. The two cosine squares are the real ratios l₂/m and (l₁−l₂)/(m−l₂); their sines are the negative square roots of one minus those ratios. In the second ratio, both differences are taken in the natural numbers before being cast to the reals.

**Definition 1.11 (The pruned single-index product).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (k: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation}), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedTilde}\left(n, m, k, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \operatorname{let} (kt: \mathbb{N}) = (\operatorname{ite}\left((k\left((0: \operatorname{Fin}\left(3\right))\right) = 0), k\left((2: \operatorname{Fin}\left(3\right))\right), \operatorname{Max.max}\left(k\left((1: \operatorname{Fin}\left(3\right))\right), k\left((2: \operatorname{Fin}\left(3\right))\right)\right)\right)); (\operatorname{List.foldl}\left(\lambda (g: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \mapsto (\lambda (l: \mathbb{N}) \mapsto (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.I}\left(n, m, l, g\right))), f, \operatorname{List.Ico}\left(\operatorname{Max.max}\left(((kt) + (m)) - (n), 1\right), (\operatorname{Min.min}\left(kt, (m) - (1)\right)) + (1)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedTilde` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The range in qdit_v3.tex, lines 1017–1029, retains I gates from max(kt + m − n,1) through min(kt,m−1), inclusive. The parameter kt equals k 2 when k 0 = 0 and otherwise equals max(k 1,k 2). List.Ico excludes its upper endpoint, so the displayed upper bound has an added one. The left fold applies gates in increasing l.

**Definition 1.12 (The pruned double-index product).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (k: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation}), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedTildeTilde}\left(n, m, k, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \operatorname{let} (l_{1}: \mathbb{N}) = ((k\left((1: \operatorname{Fin}\left(3\right))\right)) + (k\left((2: \operatorname{Fin}\left(3\right))\right))); (\operatorname{let} (l_{2}: \mathbb{N}) = (k\left((2: \operatorname{Fin}\left(3\right))\right)); (\operatorname{List.foldl}\left(\lambda (g: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \mapsto (\lambda (b: \mathbb{N}) \mapsto (\operatorname{List.foldl}\left(\lambda (h: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \mapsto (\lambda (a: \mathbb{N}) \mapsto (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.II}\left(n, m, a, b, h\right))), g, \operatorname{List.Ico}\left(\operatorname{Max.max}\left(((l_{1}) + (m)) - (n), (b) + (1)\right), (\operatorname{Min.min}\left(l_{1}, (m) - (1)\right)) + (1)\right)\right))), f, \operatorname{List.Ico}\left(\operatorname{Max.max}\left(((l_{2}) + (m)) - (n), 1\right), (\operatorname{Min.min}\left(l_{2}, (m) - (2)\right)) + (1)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedTildeTilde` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The range in qdit_v3.tex, lines 1008–1013, uses l₁ = k 1 + k 2 and l₂ = k 2. The outer index b runs from max(l₂ + m − n,1) through min(l₂,m−2). For each b, the inner index a runs from max(l₁ + m − n,b+1) through min(l₁,m−1). Both ranges are inclusive and are applied in increasing order, with a increasing inside each fixed b.

**Definition 1.13 (A pruned register block).**

$$\forall (n: \mathbb{N}), (\forall (m: \mathbb{N}), (\forall (k: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation}), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedW}\left(n, m, k, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedTildeTilde}\left(n, m, k, \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedTilde}\left(n, m, k, f\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedW` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The factorization in qdit_v3.tex, lines 1000–1004, first applies the single-index product and then the double-index product.

**Definition 1.14 (The full pruned circuit).**

$$\forall (n: \mathbb{N}), (\forall (k: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation}), (\forall (f: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedU}\left(n, k, f\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \operatorname{List.foldl}\left(\lambda (g: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) \mapsto (\lambda (m: \mathbb{N}) \mapsto (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedW}\left(n, m, k, g\right))), f, \operatorname{List.reverse}\left(\operatorname{List.Ico}\left(2, (n) + (1)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedU` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The product in qdit_v3.tex, lines 993–997, applies the largest register block first. Reversing the list 2,…,n gives the time order n,n−1,…,2. Each block uses the same occupation vector k.

**Definition 1.15 (The identity-permutation input word).**

$$\forall (n: \mathbb{N}), (\forall (k: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation}), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.initialWord}\left(n, k\right): \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)) = \lambda (w: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{ite}\left((\operatorname{Fin.val}\left(w\right) < k\left((2: \operatorname{Fin}\left(3\right))\right)), (2: \operatorname{Fin}\left(3\right)), \operatorname{ite}\left((\operatorname{Fin.val}\left(w\right) < (k\left((1: \operatorname{Fin}\left(3\right))\right)) + (k\left((2: \operatorname{Fin}\left(3\right))\right))), (1: \operatorname{Fin}\left(3\right)), (0: \operatorname{Fin}\left(3\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.initialWord` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The input from qdit_v3.tex, lines 191–197, has its twos on the rightmost k 2 wires, followed by k 1 ones, then zeros. The finite index w is explicitly mapped to its natural value before either comparison. The definition is total for arbitrary k; it has occupation k when the three counts sum to n.

**Definition 1.16 (The Dicke amplitude function).**

$$\forall (n: \mathbb{N}), (\forall (k: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation}), ((\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.dicke}\left(n, k\right): \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.State}\left(n\right)) = \lambda (t: \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.Word}\left(\operatorname{Fin}\left(3\right), n\right)) \mapsto (\operatorname{ite}\left((\forall (s: \operatorname{Fin}\left(3\right)), (\operatorname{Multiset.count}\left(s, \operatorname{D5.S3.Quantum.Entanglement.OccupancyWordSectors.occupation}\left(t\right)\right) = k\left(s\right))), \frac{(1: \mathbb{R})}{\operatorname{Real.sqrt}\left((\operatorname{Nat.cast}\left((\operatorname{Nat.div}\left(\operatorname{Nat.factorial}\left(n\right), ((\operatorname{Nat.factorial}\left(k\left((0: \operatorname{Fin}\left(3\right))\right)\right)) \cdot (\operatorname{Nat.factorial}\left(k\left((1: \operatorname{Fin}\left(3\right))\right)\right))) \cdot (\operatorname{Nat.factorial}\left(k\left((2: \operatorname{Fin}\left(3\right))\right)\right))\right): \mathbb{N})\right): \mathbb{R})\right)}, (0: \mathbb{R})\right))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.dicke` (`✓ std3`).

*Citation.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

The state in qdit_v3.tex, lines 177–185, has a common amplitude on words with the specified letter counts and zero elsewhere. For counts summing to n, its number of words is n!/(k 0! k 1! k 2!). The displayed definition first performs this factorial division in the natural numbers, then casts the quotient to a real number before taking its square root. The count is the multiplicity in the multiset of letters of t; it remains a natural number.

**Definition 1.17 (Universal preparation by the pruned circuit).**

$$(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((2 \le n) \to (\forall (k_{0}: \mathbb{N}), (\forall (k_{1}: \mathbb{N}), (\forall (k_{2}: \mathbb{N}), ((((k_{0}) + (k_{1})) + (k_{2}) = n) \to (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.prunedU}\left(n, (![k_{0},k_{1},k_{2}]: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation}), \operatorname{D5.S3.Combinatorics.Graph.LegalWords.SignedBoundary.vertexDelta}\left(\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.initialWord}\left(n, (![k_{0},k_{1},k_{2}]: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation})\right)\right)\right) = \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.dicke}\left(n, (![k_{0},k_{1},k_{2}]: \operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.Occupation})\right))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/QutritDickePruningRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

For every natural n at least two and every triple of natural counts summing to n, the pruned circuit is asserted to map the unit amplitude at the identity-permutation input to the Dicke amplitude function. This is the real-coordinate formulation of the proposed preparation identity in qdit_v3.tex, lines 987–1031, with the specific gate order and boundary controls defined above.

**Theorem 1.18 (The occupation (1,3,1) contradicts universal preparation).**

$$\neg (\operatorname{D5.S3.Quantum.PureState.QutritDickePruningRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/QutritDickePruningRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/nepomechie-raveh-2024-qutrit-dicke-pruning-refutation` (refuted) by `D5/S3/Quantum/PureState/QutritDickePruningRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nepomechie-raveh-2024-qutrit-dicke-pruning-refutation","declaration_gid":"D5/S3/Quantum/PureState/QutritDickePruningRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rafael I. Nepomechie; David Raveh (2024). *Qudit Dicke state preparation*. DOI: [10.26421/QIC24.1-2-2](https://doi.org/10.26421/QIC24.1-2-2). URL: <https://arxiv.org/abs/2301.04989v4>.

*Commentary.*

Updating one wire leaves every distinct wire unchanged. Consequently, restriction of amplitudes to a fixed letter on an untouched wire commutes with a controlled exchange and with a controlled rotation. Both operations also commute with multiplication of all amplitudes by a real scalar. These properties pass through the compositions defining V, I and II.

Take n = 5 and k = (1,3,1). Write words as lists of their letters on wires 0,1,2,3,4, and write δ_b for the amplitude function equal to one at b and zero elsewhere. Let u = [2,1,1,1,0], b = [0,2,1,1,1] and v = [0,1,1,1,2]. The first block is prunedW 5 5 k = II 5 5 4 1 composed with I 5 5 3. Evaluating the gates on all 3⁵ words shows that I 5 5 3 fixes δ_u. The same finite evaluation of II shows that restricting prunedW 5 5 k δ_u to wire 0 equal to zero gives δ_b/√5.

The next block is prunedW 5 4 k = II 5 4 3 1 composed with I 5 4 3 and I 5 4 2, so I 5 4 2 acts first. Each of these three gates fixes δ_b, by evaluation on all 3⁵ words. Every target wire in this block is distinct from wire 0, so restriction to wire 0 equal to zero commutes with the block. Together with scalar multiplication, this proves that after both blocks the restriction is still δ_b/√5. In particular, any amplitude with wire 0 equal to zero and wire 1 different from two vanishes.

The remaining blocks apply I 5 3 1, I 5 3 2, II 5 3 2 1, then I 5 2 1. They never target wires 0 or 1, and hence commute with restriction to a specified letter on either wire. For a function f with the preceding vanishing property, its restriction to wire 0 equal to zero is already supported on wire 1 equal to two. Commuting these two restrictions through the remaining composition forces its amplitude at v to be zero, since v has wire 0 equal to zero and wire 1 equal to one. The identity-permutation word for n = 5 and k = (1,3,1) is u, so the full pruned output has zero amplitude at v.

The word v contains one zero, three ones and one two. Its Dicke amplitude is therefore 1/√(5!/(1!3!1!)) = 1/√20. This number is nonzero because 20 is positive. Applying the asserted universal identity at n = 5, k₀ = 1, k₁ = 3 and k₂ = 1, and evaluating both functions at v, would equate this nonzero amplitude with zero. Thus claim is false.

## References

- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.I`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.II`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.Occupation`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.State`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.V`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.claim`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.controlledR`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.controlledX`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.controlsHold`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.dicke`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.initialWord`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedTilde`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedTildeTilde`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedU`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.prunedW`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.put`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.result`
- Truth anchor: `D5/S3/Quantum/PureState/QutritDickePruningRefutation.wire`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWords/SignedBoundary](../../Combinatorics/Graph/LegalWords/SignedBoundary.md)
- Dependency: [D5/S3/Quantum/Entanglement/OccupancyWordSectors](../Entanglement/OccupancyWordSectors.md)
