# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exactly 1 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.

**Definition 1.1 (Column letters).**

$$\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(2\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

A transfer letter is one column of the literal array.

**Definition 1.2 (No internal column bonds).**

$$\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

Every registered bond joins consecutive columns; none lies within a column.

**Definition 1.3 (Bonds joining consecutive columns).**

$$\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}} = \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((0, 0), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((1, 1), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((1, 0), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((0, 1), \operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

Pairs give the row in the previous column and the row in the next column. Diagonal and antidiagonal orientations are kept literal.

**Definition 1.4 (Residual budgets).**

$$\forall p: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (d \le 1)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

The remaining budget is at most the registered exact budget.

**Definition 1.5 (Equality and budget classes).**

$$\forall p: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} ((d = 1) \land (p\left(0\right) = p\left(1\right))) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 1) \land (p\left(0\right) \neq p\left(1\right))) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((d = 0) \land (p\left(0\right) = p\left(1\right))) \operatorname{\mathit{then}} 2 \operatorname{\mathit{else}} 3)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

Global colour permutations preserve the equality pattern of the retained column.

**Definition 1.6 (T).**

$$\operatorname{\mathit{HardinA229535Strip}}.\operatorname{T} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(2, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.7 (initial).**

$$\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{initial}} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.8 (terminal).**

$$\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{terminal}} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(1, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

These integer tables give class transitions, initial weights, terminal acceptance and successive forward weights.

**Definition 1.9 (W).**

$$\operatorname{\mathit{HardinA229535Strip}}.\operatorname{W} = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(3, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(12, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(6, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(30, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(24, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(84, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(60, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(72, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(144, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(228, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(168, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(288, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(384, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

The first two forward coordinates call HardinColumnContinuations.vB, scaled by colour-orbit sizes 3 and 6. Only the exact-defect sector is tabulated here.

**Definition 1.10 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(2\right)) \times (\operatorname{\mathit{Fin}}\left(n\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda i: \operatorname{\mathit{Fin}}\left(2\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(2\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(2\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

Canonical is the original HardinA233177Canonical.Canonical predicate, with order lifted through finProdFinEquiv to retain literal row-major order. The filter enumerates all k by n arrays. The ordinal i*n+j is the original row-major order, including when transfer sweeps columns.

**Theorem 1.11 (Exact finite transfer certificate).**

$$(\forall p: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Valid}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(4\right), (\sum_{r: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229535Strip}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Valid}}\left(r, 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(4\right), (\sum_{r: \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{cl}}\left(r, 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229535Strip}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229535Strip}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(4\right), (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229535Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229535Strip}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{W}\left(4\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(4\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-4), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-8), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(0, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229535Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(0 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

The clauses certify acceptance, budget preservation, transition sums, initial admissibility and weights, every forward step and the polynomial relation. The last index has value b+j, bounded by the table length.

**Theorem 1.12 (The registered integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229535Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) = 4 \cdot (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) - 8 \cdot (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}) - 4 \cdot (\operatorname{\mathit{HardinA229535Strip}}.\operatorname{a}\left(n + 1\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229535` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229535","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229535: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229535>.

*Commentary.*

The column transfer counts labelled arrays. Coordinate exchange is an equivalence of labelled arrays; the original row-major canonical representatives have six labelled realizations. Multiplication propagates the certified vector relation to every further length.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229535Strip.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinColumnContinuations](../../../Combinatorics/TraceAvoidingArrays/HardinColumnContinuations.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
