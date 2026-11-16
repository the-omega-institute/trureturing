# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exactly 1 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.

**Definition 1.1 (Column letters).**

$$\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

A transfer letter is one column of the literal array.

**Definition 1.2 (No internal column bonds).**

$$\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

Every registered bond joins consecutive columns; none lies within a column.

**Definition 1.3 (Bonds joining consecutive columns).**

$$\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((0, 0), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((1, 1), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((2, 2), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((3, 3), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((1, 0), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((2, 1), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((3, 2), \operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

Pairs give the row in the previous column and the row in the next column. Diagonal and antidiagonal orientations are kept literal.

**Definition 1.4 (Residual budgets).**

$$\forall p: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (d \le 1)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

The remaining budget is at most the registered exact budget.

**Definition 1.5 (Equality and budget classes).**

$$\forall p: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 2 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 3 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 4 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 5 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 6 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 7 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 8 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 9 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 10 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 11 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 12 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 13 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 14 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 15 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 16 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 17 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 18 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 19 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 20 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 21 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 22 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) = p\left(3\right)))))))) \operatorname{\mathit{then}} 23 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 24 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) \neq p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 25 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land ((p\left(0\right) \neq p\left(1\right)) \land ((p\left(0\right) \neq p\left(2\right)) \land ((p\left(0\right) \neq p\left(3\right)) \land ((p\left(1\right) \neq p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \neq p\left(3\right)))))))) \operatorname{\mathit{then}} 26 \operatorname{\mathit{else}} 27)))))))))))))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

Global colour permutations preserve the equality pattern of the retained column.

**Definition 1.6 (T).**

$$\operatorname{\mathit{HardinA229589StripData}}.\operatorname{T} = ![![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0], ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 3, 3, 2, 2, 0, 2, 1, 2, 0, 1, 1, 1, 2], ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 3, 2, 1, 3, 2, 1, 0, 0, 1, 2, 1, 1], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 2, 3, 2, 1, 1, 2, 2, 1, 2, 1, 2], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 2, 2, 1, 1, 0, 1, 2, 2, 2, 0, 2, 1], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 2], ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2], ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 0, 2, 2], ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 0, 1, 1, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 2, 1, 2, 0, 2, 2, 1, 1, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 2, 2, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 3, 2, 1, 1, 0, 2, 2, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.7 (initial).**

$$\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{initial}} = ![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.8 (terminal).**

$$\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{terminal}} = ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.9 (W).**

$$\operatorname{\mathit{HardinA229589StripData}}.\operatorname{W} = ![![3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![48, 48, 24, 48, 24, 24, 12, 12, 24, 48, 24, 12, 12, 24, 24, 120, 108, 120, 108, 108, 78, 78, 108, 120, 108, 78, 78, 108], ![324, 324, 216, 324, 108, 216, 144, 72, 180, 324, 144, 36, 72, 108, 918, 1458, 864, 1350, 1026, 828, 552, 636, 870, 1350, 1020, 534, 600, 954], ![2376, 2376, 1512, 2160, 648, 1476, 972, 504, 1260, 2160, 900, 144, 432, 576, 9756, 13428, 8604, 12960, 8244, 8646, 5994, 5064, 7998, 13104, 8562, 4008, 4680, 7536], ![16668, 16668, 10548, 14976, 4428, 10548, 6912, 3636, 8856, 14868, 6012, 792, 2736, 3528, 94314, 119838, 76362, 112416, 63270, 74778, 51804, 40074, 68112, 112506, 68118, 28812, 36192, 57588], ![116712, 116712, 73728, 104472, 30744, 73728, 48204, 25524, 61488, 102672, 41184, 5220, 18504, 23724, 831588, 1009788, 641940, 936912, 485412, 632940, 434550, 317478, 567084, 938472, 535548, 206706, 278040, 434454], ![814428, 814428, 514296, 728460, 214164, 514296, 336096, 178200, 428328, 714420, 286092, 35964, 128196, 164160, 7010946, 8253702, 5240520, 7611714, 3699918, 5179032, 3530232, 2478888, 4587048, 7595226, 4150926, 1489374, 2120994, 3261744], ![5679180, 5679180, 3586032, 5078916, 1492884, 3586032, 2343276, 1242756, 2985768, 4978908, 1993140, 250128, 892620, 1142748, 57312234, 65977182, 41858244, 60598062, 28005030, 41429916, 28088910, 19128078, 36400932, 60313734, 31877478, 10745028, 16094718, 24412014], ![39596472, 39596472, 25002216, 35410176, 10407960, 25002216, 16337268, 8664948, 20815920, 34709904, 13893984, 1743012, 6221664, 7964676, 458298864, 518711256, 328905972, 474978708, 210671424, 325920204, 220056066, 146210994, 284630940, 471916548, 242811432, 77480586, 121405212, 181963818], ![276067116, 276067116, 174315240, 246878604, 72563364, 174315240, 113902848, 60412392, 145126728, 241992036, 96865308, 12150972, 43374852, 55525824, 3604507650, 4025701494, 2551529736, 3677491602, 1576344222, 2530713816, 1703069676, 1108940292, 2199541464, 3648822642, 1836399942, 558174258, 910677618, 1350878292], ![1924732044, 1924732044, 1215320112, 1721228292, 505908180, 1215320112, 794126268, 421193844, 1011816360, 1687153212, 675336852, 84714336, 302404428, 387118764, 27983643750, 30920192154, 19590697692, 28190758266, 11740112730, 19445570964, 13050899334, 8355856590, 16834926492, 27940236714, 13804279794, 4017095208, 6797386242, 9991982502], ![13419160488, 13419160488, 8473165704, 12000336624, 3527170920, 8473165704, 5536617300, 2936548404, 7054341840, 11762757792, 4708415952, 590622516, 2108347056, 2698969572, 214992582372, 235466084700, 149145632964, 214333304256, 87079997484, 148133816604, 99197452926, 62609667174, 127829237508, 212234286024, 103222148148, 28882447938, 50516232336, 73664261622], ![93557866428, 93557866428, 59074581096, 83665876860, 24591295764, 59074581096, 38601078768, 20473502328, 49182591528, 82009474164, 32826882636, 4117793436, 14699306196, 18817099632, 1637603470098, 1780343928054, 1127405471616, 1618343660538, 643570636446, 1120351129776, 748820220696, 466860643056, 964125058392, 1601253691722, 768320699022, 207471087990, 373986155322, 541477118160]]$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

For rows 0 through 8, the zero-defect block calls HardinA233259PairTransferPowers.W after reflection [0,9,5,3,13,2,6,12,8,1,10,11,7,4], scaled by 3 for coordinate 0 and 6 otherwise. Row 1 calls HardinA233259PairTransferCore.weights. The defect sector and final four rows remain tabulated here.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](../../../Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers](../../../Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.md)
