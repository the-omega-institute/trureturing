# Exact two-defect strip transfer

## Abstract

Exact two-defect strip transfer.

**Definition 1.1 (Classes at budget zero).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{exhaustedClass}} : (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}) \to (\operatorname{\mathit{Fin}}\left(96\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhaustedClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

If Valid(p,1) holds, let i be the value of the A229585 class of p at budget zero. The return value is i minus 16 in Fin 96 when i is at least 16, and zero otherwise. If Valid(p,1) fails, use the A229635 first-occurrence equality-pattern index. Its first 40 entries are the lexicographically ordered canonical six-cell boundaries with exactly two adjacent equalities. Return 56 plus the residue of that index modulo 40. A pattern absent from the 40 entries in this branch has more than two adjacent equalities. Its equality mask is absent from the 96 A229635 representatives, whose lookup returns 96 before reduction modulo 96. The resulting index is zero, so the exhausted class is 56.

**Definition 1.2 (Class of a boundary and budget).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (d = 0) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, \operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{exhaustedClass}}\left(p\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(96, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A positive budget d uses the A229585 boundary class at budget d minus one.

**Definition 1.3 (Column indices of the exhausted block).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{exitRead}} : (\operatorname{\mathit{Fin}}\left(96\right)) \to (\operatorname{\mathit{Fin}}\left(108\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exitRead` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

This 96-entry map selects the leading column at indices below 72 and one of 36 stored profiles at indices from 72 through 107. The transition multiplicity formula pins the selected profile to its exhausted destination class.

**Definition 1.4 (Transfer matrix).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T} : \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(168\right), \operatorname{\mathit{Fin}}\left(168\right), \mathit{Int}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The leading block is the A229585 transfer matrix. The lower left block is zero. For every boundary and budget satisfying HardinA229635State.Valid, the right-block entries of the classified source row count next rows that spend the entire remaining budget. The 16 upper-right rows selected by zeroBudgetClass use the exhausted columns of the corresponding A229585 row followed by 40 zeros. In the other upper-right rows, 24 columns use entries of the leading block and the others use 36 multiplicity profiles. Within the lower right block, the original exhausted sources use the exhausted rows and columns of A229585, extended by zero columns. Each new lower-right row vanishes at exitRead values below 72. At greater or equal values it reads the radix-16 multiplicity at exitRead minus 72.

**Theorem 1.5 (Multiplicity of a successor class).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\forall s: \operatorname{\mathit{Fin}}\left(168\right), (((\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \lor (((d = 0) \land (\forall k: \operatorname{\mathit{Fin}}\left(16\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) \ne 56 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{zeroBudgetClass}}\left(k\right)\right)))) \lor (((d = 1) \land ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 72) \land (\forall k: \operatorname{\mathit{Fin}}\left(16\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) \ne \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{zeroBudgetClass}}\left(k\right)\right))))) \lor ((((d = 1) \lor (13 \le d)) \land (128 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right))) \lor ((15 \le d) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) < 16)))))) \implies (\sum_{r: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le d) \land (\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), d - (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = s)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(p, d\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Every next row whose cost fits the available budget contributes one to its destination.

At budget zero the possible destinations are 56 plus a value of zeroBudgetClass. At budget one the support is contained in the values of zeroBudgetClass and the interval 72 through 127. Both sides vanish outside these supports. At a constant zero boundary with budget one and destination 29, the literal count is two and the matrix entry is one.

The horizontal and antidiagonal filters each contain at most six bonds. At budgets at least thirteen no row exhausts the budget, and the matrix vanishes at destinations from 128 onward. At budgets at least fifteen every successor retains at least three units, and both sides vanish below destination 16.

**Definition 1.6 (Reindex an inherited exhausted class).**

$$\forall i: \operatorname{\mathit{Fin}}\left(72\right), (\operatorname{\mathit{oldZeroImage}}\left(i\right) = (\operatorname{\mathit{if}} (16 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(i\right)) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(40, \operatorname{\mathit{Fin}}.\operatorname{\mathit{subNat}}\left(16, i\right)\right) \operatorname{\mathit{else}} 0))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.oldZeroImage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Subtract 16 below the embedding into Fin 96. The index is zero when the input is below 16.

**Theorem 1.7 (Source validity).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{Valid}}\left(p, d\right) \Leftrightarrow (d \le 2) \land (\operatorname{\mathit{HardinA229635State}}.\operatorname{h}\left(p\right) \le 2 - d)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.valid_parts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Validity bounds the remaining budget and the number of equal neighbours in the boundary.

**Theorem 1.8 (New class under relabelling).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{fresh}}\left((\lambda i \mapsto e\left(p\left(i\right)\right))\right) = \operatorname{\mathit{HardinA229635State}}.\operatorname{\mathit{fresh}}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.fresh_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Permuting colours preserves the equality pattern.

**Theorem 1.9 (Exhausted class under relabelling).**

$$\forall e: \operatorname{\mathit{Equiv}}.\operatorname{\mathit{Perm}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\operatorname{\mathit{exhaustedClass}}\left((\lambda i \mapsto e\left(p\left(i\right)\right))\right) = \operatorname{\mathit{exhaustedClass}}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The exhausted index depends on the equality pattern.

**Theorem 1.10 (Successor in the leading block).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\forall c: \mathit{Nat}, (\forall j: \operatorname{\mathit{Fin}}\left(72\right), ((c \le d) \land (\operatorname{\mathit{cl}}\left(p, d - c\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(96, j\right)) \Leftrightarrow (0 < d) \land ((c \le d - 1) \land (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1 - c\right) = j))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.active_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A leading destination occurs with strictly positive budget after the transition.

**Theorem 1.11 (Successor in the exhausted block).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\forall c: \mathit{Nat}, (\forall j: \operatorname{\mathit{Fin}}\left(96\right), ((c \le d) \land (\operatorname{\mathit{cl}}\left(p, d - c\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, j\right)) \Leftrightarrow (c = d) \land (\operatorname{\mathit{exhaustedClass}}\left(p\right) = j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

An exhausted destination occurs when the cost equals the remaining budget.

**Theorem 1.12 (Horizontal charge of a new head).**

$$\forall x: \operatorname{\mathit{Fin}}\left(3\right), (\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(x, p\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(x, p\right)\right) = (\operatorname{\mathit{if}} (x = p\left(0\right)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0) + \operatorname{\mathit{HardinA229635State}}.\operatorname{h}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.horizontal_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Prepending a colour adds one comparison with the first boundary cell.

**Theorem 1.13 (Support of the exhausted matrix rows).**

$$\forall s: \operatorname{\mathit{Fin}}\left(168\right), (\left(\exists i \in \operatorname{\mathit{Fin}}\left(96\right),\; (\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, i\right), s\right) \ne 0)\right) \Leftrightarrow \left(\exists k \in \operatorname{\mathit{Fin}}\left(16\right),\; (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(s\right) = 56 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{zeroBudgetClass}}\left(k\right)\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A destination occurs in at least one of the 96 exhausted matrix rows precisely when it lies in this image.

**Definition 1.14 (Cost of a colour match).**

$$\operatorname{\mathit{matchCost}} : (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to ((\operatorname{\mathit{Fin}}\left(3\right)) \to (\mathit{Nat})), \operatorname{\mathit{matchCost}}\left(\mathit{none}, x\right) = 0, \operatorname{\mathit{matchCost}}\left(\operatorname{\mathit{some}}\left(p\right), x\right) = (\operatorname{\mathit{if}} (p = x) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.matchCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

An absent colour costs zero. A present colour costs one exactly when it agrees with the current colour.

**Definition 1.15 (Cost of a completion).**

$$\operatorname{\mathit{completionCost}} : \forall k: \mathit{Nat}, (((\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right))) \to ((\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to (((\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))) \to (\mathit{Nat})))), \operatorname{\mathit{completionCost}}\left(0, p, b, r\right) = \operatorname{\mathit{matchCost}}\left(b, r\left(0\right)\right), \operatorname{\mathit{completionCost}}\left(k + 1, p, b, r\right) = \operatorname{\mathit{matchCost}}\left(b, r\left(0\right)\right) + \operatorname{\mathit{matchCost}}\left(p\left(0\right), r\left(0\right)\right) + \operatorname{\mathit{completionCost}}\left(k, \operatorname{\mathit{Fin}}.\operatorname{\mathit{tail}}\left(p\right), \operatorname{\mathit{some}}\left(r\left(0\right)\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{tail}}\left(r\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Sum the initial match, when a previous colour is supplied, the matches between neighbours, and the matches against the optional boundary colours.

**Definition 1.16 (Pruned completion list).**

$$\operatorname{\mathit{completionRows}} : \forall k: \mathit{Nat}, (((\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right))) \to ((\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to ((\mathit{Nat}) \to (\operatorname{\mathit{List}}\left((\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))\right))))), \operatorname{\mathit{completionRows}}\left(0, p, b, d\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left((\lambda x \mapsto (\lambda i \mapsto x)), \operatorname{\mathit{List}}.\operatorname{\mathit{filter}}\left((\lambda x \mapsto \operatorname{\mathit{matchCost}}\left(b, x\right) = d), \operatorname{\mathit{List}}.\operatorname{\mathit{finRange}}\left(3\right)\right)\right), \operatorname{\mathit{completionRows}}\left(k + 1, p, b, d\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{flatMap}}\left((\lambda x \mapsto \operatorname{\mathit{let}} c : = \operatorname{\mathit{matchCost}}\left(b, x\right) + \operatorname{\mathit{matchCost}}\left(p\left(0\right), x\right), (\operatorname{\mathit{if}} (c \le d) \operatorname{\mathit{then}} \operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(x\right), \operatorname{\mathit{completionRows}}\left(k, \operatorname{\mathit{Fin}}.\operatorname{\mathit{tail}}\left(p\right), \operatorname{\mathit{some}}\left(x\right), d - c\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{List}}.\operatorname{\mathit{nil}})), \operatorname{\mathit{List}}.\operatorname{\mathit{finRange}}\left(3\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Try the three available colours in order, keep each head whose cost fits the budget, and prepend it to the completions at the remaining budget. The last cell must spend the entire remaining budget.

**Theorem 1.17 (Multiplicity of qualifying rows).**

$$\forall k: \mathit{Nat}, (\forall p: (\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)), (\forall b: \operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall d: \mathit{Nat}, (\forall f: ((\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))) \to (\mathit{Bool}), (\operatorname{\mathit{List}}.\operatorname{\mathit{countP}}\left(f, \operatorname{\mathit{completionRows}}\left(p, b, d\right)\right) = \sum_{r: (\operatorname{\mathit{Fin}}\left(k + 1\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (\mathit{if} (\operatorname{\mathit{completionCost}}\left(p, b, r\right) = d) \land (\operatorname{f}\left(r\right) = \mathit{true}) \mathit{then} 1 \mathit{else} 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionRows_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The sum counts each qualifying row once.

**Definition 1.18 (Pruned list in base three).**

$$\operatorname{\mathit{completionCodes}} : (\operatorname{\mathit{List}}\left(\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)\right)) \to ((\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)) \to ((\mathit{Nat}) \to (\operatorname{\mathit{List}}\left(\mathit{Nat}\right)))), \operatorname{\mathit{completionCodes}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{nil}}, b, d\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}, \operatorname{\mathit{List}}.\operatorname{\mathit{filter}}\left((\lambda x \mapsto \operatorname{\mathit{matchCost}}\left(b, x\right) = d), \operatorname{\mathit{List}}.\operatorname{\mathit{finRange}}\left(3\right)\right)\right), \operatorname{\mathit{completionCodes}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{cons}}\left(a, \mathit{bs}\right), b, d\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{flatMap}}\left((\lambda x \mapsto \operatorname{\mathit{let}} c : = \operatorname{\mathit{matchCost}}\left(b, x\right) + \operatorname{\mathit{matchCost}}\left(a, x\right), (\operatorname{\mathit{if}} (c \le d) \operatorname{\mathit{then}} \operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left((\lambda r \mapsto \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(x\right) + 3 \cdot r), \operatorname{\mathit{completionCodes}}\left(\mathit{bs}, \operatorname{\mathit{some}}\left(x\right), d - c\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{List}}.\operatorname{\mathit{nil}})), \operatorname{\mathit{List}}.\operatorname{\mathit{finRange}}\left(3\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionCodes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Run the same recursion on a list of boundary colours. Prepending a colour x replaces the tail code c with the natural value of x plus three times c.

**Theorem 1.19 (Code of a row with a new head).**

$$\forall m: \mathit{Nat}, (\forall k: \mathit{Nat}, (\forall x: \operatorname{\mathit{Fin}}\left(m\right), (\forall r: (\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Fin}}\left(m\right)), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{finFunctionFinEquiv}}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{cons}}\left(x, r\right)\right)\right) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(x\right) + m \cdot \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{finFunctionFinEquiv}}\left(r\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.rowCode_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The leading cell is the least significant digit of the code.

**Theorem 1.20 (Agreement of the two lists).**

$$\forall k: \mathit{Nat}, (\forall p: (\operatorname{\mathit{Fin}}\left(k\right)) \to (\operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right)), (\forall b: \operatorname{\mathit{Option}}\left(\operatorname{\mathit{Fin}}\left(3\right)\right), (\forall d: \mathit{Nat}, (\operatorname{\mathit{completionCodes}}\left(\operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(p\right), b, d\right) = \operatorname{\mathit{List}}.\operatorname{\mathit{map}}\left(\lambda r \mapsto \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{finFunctionFinEquiv}}\left(r\right)\right), \operatorname{\mathit{completionRows}}\left(p, b, d\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionCodes_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The numeric enumerator returns the codes of the pruned completion list in the same order.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.active_cut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionCodes`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionCodes_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionCost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionRows`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.completionRows_count`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhaustedClass`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_cut`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhausted_support`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exitRead`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.fresh_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.horizontal_cons`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.matchCost`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.oldZeroImage`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.rowCode_cons`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.valid_parts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Column](../../../../Combinatorics/TraceAvoidingArrays/HardinA233154Column.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233154Rows](../../../../Combinatorics/TraceAvoidingArrays/HardinA233154Rows.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233155ColumnTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233155RowTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry](../../../../Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Laws](../../CrossedStripDefectsWide/P5b/HardinA229635Laws.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635State](../../CrossedStripDefectsWide/P5b/HardinA229635State.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229584StripData](../../StripDefects/HardinA229584StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip](../HardinA229585Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](../HardinA229585StripData.md)
