# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Rows have q colours and k columns. H and V are arbitrary finite sets of in-row and between-row bonds. Exact defect counts, arbitrary residual targets and boundary quotients are handled uniformly. No geometric adjacency or colour count is fixed.

**Definition 1.1 (Finite colour rows).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right) = (\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Fin}}\left(q\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

Both the colour count and the row width are arbitrary natural numbers.

**Definition 1.2 (Counting monochromatic bonds).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall E: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), (\forall t: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(E, r, t\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda z: (\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right)) \mapsto (r\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(z\right)\right) = t\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(z\right)\right)), E\right)\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.bondDefects` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

A bond is specified by its ordered pair of column indices. Equality contributes one defect.

**Definition 1.3 (Defects after an outgoing row).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall H: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall V: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{tailDefects}}\left(H, V, r, \operatorname{\mathit{List}}.\operatorname{\mathit{nil}}\right) = 0) \land (\forall t: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), (\forall \mathit{rs}: \operatorname{\mathit{List}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)\right), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{tailDefects}}\left(H, V, r, \operatorname{\mathit{List}}.\operatorname{\mathit{cons}}\left(t, \mathit{rs}\right)\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(V, r, t\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, t, t\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{tailDefects}}\left(H, V, t, \mathit{rs}\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.tailDefects` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

Each new row contributes its in-row bonds and the bonds from the preceding row.

**Definition 1.4 (Total defects in a word of rows).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall H: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall V: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(H, V, \operatorname{\mathit{List}}.\operatorname{\mathit{nil}}\right) = 0) \land (\forall r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), (\forall \mathit{rs}: \operatorname{\mathit{List}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)\right), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(H, V, \operatorname{\mathit{List}}.\operatorname{\mathit{cons}}\left(r, \mathit{rs}\right)\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{tailDefects}}\left(H, V, r, \mathit{rs}\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.defects` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

The empty strip has zero defects. The first row contributes only in-row bonds.

**Definition 1.5 (The literal labelled count).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall H: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall V: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall D: \mathit{Nat}, (\forall n: \mathit{Nat}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{literalCount}}\left(H, V, D, n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))) \to (\operatorname{\mathit{Fin}}\left(q\right)) \mapsto (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(H, V, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(k\right) \mapsto (A\left((i, j)\right)))\right)\right) = D), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.literalCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

The finite filter enumerates all arrays on the product of the row and column index sets. The defect target D is unrestricted.

**Theorem 1.6 (Invariance under colour permutations).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall H: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall V: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(q\right)\right), (\forall \mathit{rs}: \operatorname{\mathit{List}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)\right), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(H, V, \operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left(\lambda r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right) \mapsto (\operatorname{\mathit{Function}}.\operatorname{\mathit{comp}}\left(e, r\right)), \mathit{rs}\right)\right) = \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(H, V, \mathit{rs}\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.relabel_defects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

A permutation preserves equality at the two endpoints of every bond.

**Theorem 1.7 (The defect count of a constant strip).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall H: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall V: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall c: \operatorname{\mathit{Fin}}\left(q\right), (\forall n: \mathit{Nat}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(H, V, \operatorname{\mathit{List}}.\operatorname{\mathit{replicate}}\left(n + 1, \operatorname{\mathit{Function}}.\operatorname{\mathit{const}}\left(\operatorname{\mathit{Fin}}\left(k\right), c\right)\right)\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(H\right) + n \cdot \left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(V\right) + \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(H\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.constant_defects` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

Every bond is monochromatic in a constant strip. There are n+1 in-row copies and n between-row copies.

**Definition 1.8 (Exact residual-budget continuations).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall B: \mathit{Type}, (\forall H: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall P: (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)) \to (B), (\forall C: (B) \to ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)) \to (\mathit{Nat})), (\forall p: B, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{continuation}}\left(H, P, C, 0, p, d\right) = (\operatorname{\mathit{if}} (d = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) \land (\forall n: \mathit{Nat}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{continuation}}\left(H, P, C, n + 1, p, d\right) = \sum_{r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)} ((\operatorname{\mathit{if}} (C\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right) \le d) \operatorname{\mathit{then}} \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{continuation}}\left(H, P, C, n, P\left(r\right), d - \left(C\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right)\right)\right) \operatorname{\mathit{else}} 0))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.continuation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

P retains a boundary; C counts between-row defects from that boundary. A row exceeding the residual budget contributes zero. Natural subtraction is used only under this budget test.

**Theorem 1.9 (Finite quotients preserve the literal count).**

$$\forall q: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall B: \mathit{Type}, (\forall H: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall P: (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)) \to (B), (\forall C: (B) \to ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)) \to (\mathit{Nat})), (\forall V: \operatorname{\mathit{Finset}}\left((\operatorname{\mathit{Fin}}\left(k\right)) \times (\operatorname{\mathit{Fin}}\left(k\right))\right), (\forall S: \mathit{Type}, ([\operatorname{\mathit{Fintype}}\left(S\right)] [\operatorname{\mathit{DecidableEq}}\left(S\right)], (\forall \mathit{Valid}: (B) \to ((\mathit{Nat}) \to (\mathit{Prop})), (\forall \mathit{cl}: (B) \to ((\mathit{Nat}) \to (S)), (\forall T: \operatorname{\mathit{Matrix}}\left(S, S, \mathit{Int}\right), (\forall v: (S) \to (\mathit{Int}), (\forall e: (S) \to (\mathit{Int}), (\forall D: \mathit{Nat}, (((\forall r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), (\forall t: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(V, r, t\right) = C\left(P\left(r\right), t\right)))) \land ((\forall p: B, (\forall d: \mathit{Nat}, ((\mathit{Valid}\left(p, d\right)) \implies (e\left(\mathit{cl}\left(p, d\right)\right) = (\operatorname{\mathit{if}} (d = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: B, (\forall d: \mathit{Nat}, ((\mathit{Valid}\left(p, d\right)) \implies (\forall r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), ((C\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right) \le d) \implies (\mathit{Valid}\left(P\left(r\right), d - \left(C\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right)\right)\right))))))) \land ((\forall p: B, (\forall d: \mathit{Nat}, ((\mathit{Valid}\left(p, d\right)) \implies (\forall s: S, (\sum_{r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)} ((\operatorname{\mathit{if}} ((C\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right) \le d) \land (\mathit{cl}\left(P\left(r\right), d - \left(C\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = T\left(\mathit{cl}\left(p, d\right), s\right)))))) \land ((\forall r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right) \le D) \implies (\mathit{Valid}\left(P\left(r\right), D - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right)\right)))) \land (\forall s: S, (\sum_{r: \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{Row}}\left(q, k\right)} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right) \le D) \land (\mathit{cl}\left(P\left(r\right), D - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(H, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = v\left(s\right)))))))) \implies (\forall n: \mathit{Nat}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{literalCount}}\left(H, V, D, n + 1\right): \mathit{Int}) = \operatorname{\mathit{dotProduct}}\left(v, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(T^{n}, e\right)\right))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.lumped_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

S is any finite type with its finite and equality instances. The premises state boundary factorization, terminal acceptance, budget preservation, every transition-class count, initial admissibility and every initial-class count. Decomposing arrays into a first row and successive continuations proves the equality, with the natural count cast to an integer.

**Definition 1.10 (Forward row weights).**

$$\forall S: \mathit{Type}, ([\operatorname{\mathit{Fintype}}\left(S\right)] [\operatorname{\mathit{DecidableEq}}\left(S\right)], (\forall T: \operatorname{\mathit{Matrix}}\left(S, S, \mathit{Int}\right), (\forall v: (S) \to (\mathit{Int}), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(T, v, 0\right) = v) \land (\forall n: \mathit{Nat}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(T, v, n + 1\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(T, v, n\right), T\right)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.forward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

S is finite. Each step multiplies a row of weights by T.

**Theorem 1.11 (Forward weights are matrix powers).**

$$\forall S: \mathit{Type}, ([\operatorname{\mathit{Fintype}}\left(S\right)] [\operatorname{\mathit{DecidableEq}}\left(S\right)], (\forall T: \operatorname{\mathit{Matrix}}\left(S, S, \mathit{Int}\right), (\forall v: (S) \to (\mathit{Int}), (\forall n: \mathit{Nat}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(T, v, n\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(v, T^{n}\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.forward_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

S is finite. Associativity identifies recursive forward weights with the corresponding matrix power.

**Theorem 1.12 (Propagating an initial polynomial relation).**

$$\forall S: \mathit{Type}, ([\operatorname{\mathit{Fintype}}\left(S\right)] [\operatorname{\mathit{DecidableEq}}\left(S\right)], (\forall T: \operatorname{\mathit{Matrix}}\left(S, S, \mathit{Int}\right), (\forall v: (S) \to (\mathit{Int}), (\forall e: (S) \to (\mathit{Int}), (\forall d: \mathit{Nat}, (\forall b: \mathit{Nat}, (\forall c: (\operatorname{\mathit{Fin}}\left(d\right)) \to (\mathit{Int}), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(T, v, b + d\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(d\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(c\left(j\right), \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{forward}}\left(T, v, b + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right))) \implies (\forall n: \mathit{Nat}, (\operatorname{\mathit{dotProduct}}\left(v, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(T^{n + b + d}, e\right)\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(d\right)} (c\left(j\right) \cdot \operatorname{\mathit{dotProduct}}\left(v, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left(T^{n + b + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)}, e\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.forward_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229580: one-defect three-colour width-two sheared strips*. URL: <https://oeis.org/A229580>.

*Commentary.*

S is finite. Multiplying the initial vector relation by any further power of T preserves it, and taking its dot product with any terminal vector gives the shifted scalar relation.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.bondDefects`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.constant_defects`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.continuation`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.defects`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.forward`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.forward_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.forward_shift`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.literalCount`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.lumped_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.relabel_defects`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer.tailDefects`
