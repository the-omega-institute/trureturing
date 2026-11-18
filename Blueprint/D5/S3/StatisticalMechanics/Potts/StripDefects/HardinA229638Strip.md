# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.

**Definition 1.1 (Column letters).**

$$\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(2\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

A transfer letter is one column of the literal array.

**Definition 1.2 (No internal column bonds).**

$$\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

Every registered bond joins consecutive columns; none lies within a column.

**Definition 1.3 (Residual budgets).**

$$\forall p: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (d \le 2)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

The remaining budget is at most the registered exact budget.

**Definition 1.4 (Equality and budget classes).**

$$\forall p: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} ((d = 2) \land (p\left(0\right) = p\left(1\right))) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 2) \land (p\left(0\right) \neq p\left(1\right))) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land (p\left(0\right) = p\left(1\right))) \operatorname{\mathit{then}} 2 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land (p\left(0\right) \neq p\left(1\right))) \operatorname{\mathit{then}} 3 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land (p\left(0\right) = p\left(1\right))) \operatorname{\mathit{then}} 4 \operatorname{\mathit{else}} 5)))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

Global colour permutations preserve the equality pattern of the retained column.

**Definition 1.5 (T).**

$$\operatorname{\mathit{HardinA229638Strip}}.\operatorname{T} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

The leading four-state block and the one-defect transition block call HardinA229535Strip.T. Fin.append adds only the two new two-defect rows. The other tables give initial weights, terminal acceptance and successive forward weights.

**Definition 1.6 (initial).**

$$\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{initial}} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.7 (terminal).**

$$\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{terminal}} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.8 (W).**

$$\operatorname{\mathit{HardinA229638Strip}}.\operatorname{W} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(30, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(60, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(180, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(84, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(60, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(72, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(144, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(348, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(384, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(228, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(168, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(288, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(384, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1200, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1728, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(624, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(456, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(960, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1248, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4464, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(5184, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1704, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1248, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3168, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3744, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(15024, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(17328, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.9 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(2\right)) \times (\operatorname{\mathit{Fin}}\left(n\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda i: \operatorname{\mathit{Fin}}\left(2\right) \mapsto (A\left((i, j)\right)))\right)\right) = 2) \land (\forall p: (\operatorname{\mathit{Fin}}\left(2\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(2\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

Canonical is the original HardinA233177Canonical.Canonical predicate, with order lifted through finProdFinEquiv to retain literal row-major order. The filter enumerates all k by n arrays. The ordinal i*n+j is the original row-major order, including when transfer sweeps columns.

**Theorem 1.10 (Exact finite transfer certificate).**

$$(\forall p: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Valid}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(6\right), (\sum_{r: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229638Strip}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 2) \implies (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Valid}}\left(r, 2 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(6\right), (\sum_{r: \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 2) \land (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{cl}}\left(r, 2 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229638Strip}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229638Strip}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(6\right), (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229638Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229638Strip}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{W}\left(6\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(8, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-16), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-6), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229638Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(0 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

The clauses certify acceptance, budget preservation, transition sums, initial admissibility and weights, every forward step and the polynomial relation. The last index has value b+j, bounded by the table length.

**Theorem 1.11 (The registered integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) = 6 \cdot (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) - 6 \cdot (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) - 16 \cdot (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) + 12 \cdot (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) + 24 \cdot (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}) + 8 \cdot (\operatorname{\mathit{HardinA229638Strip}}.\operatorname{a}\left(n + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229638` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229638","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229638: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229638>.

*Commentary.*

The column transfer counts labelled arrays. Coordinate exchange is an equivalence of labelled arrays; the original row-major canonical representatives have six labelled realizations. Multiplication propagates the certified vector relation to every further length.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229638Strip.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations](../../../Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip](HardinA229535Strip.md)
