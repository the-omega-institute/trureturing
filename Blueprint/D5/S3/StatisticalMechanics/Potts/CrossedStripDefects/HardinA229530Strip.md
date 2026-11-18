# Hardin A229530: exact defect recurrence

## Abstract

Literal HDA colourings and exact defect transfer.

The literal array has n rows, 4 columns and exactly 1 monochromatic HDA bonds. Rows are swept by an exact-budget transfer with 10 equality-and-budget classes, identifying reflection. Every proper-row diagonal block calls the published zero-temperature owner. The frozen four_class_certificate supplies proper transitions through scanner_fibres at saturated Seen flags, an exact budget/class cut and division by sixteen. The remaining defective-source and defect-consuming entries are computed separately.

**Definition 1.1 (Shared between).**

$$\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{between}} = \operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{antidiagonal}} \cup \operatorname{\mathit{Finset}}.\operatorname{\mathit{image}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{swap}}, \operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{antidiagonal}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.between` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The exact HDA bonds between consecutive rows, shared with the two-defect extension.

**Definition 1.2 (Shared Valid).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Nat}}, (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{Valid}}\left(p, d\right) = ((d \le 1) \land (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, p, p\right) \le 1 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The one-defect residual-budget domain, reused after subtracting one from the two-defect residual budget.

**Definition 1.3 (Shared cl).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Nat}}, ((\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{cl}}\left(p, d\right): \operatorname{\mathit{Fin}}\left(10\right)) = (\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 1))) \operatorname{\mathit{then}} (0) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 2))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 1) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 3))) \operatorname{\mathit{then}} (2) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 1))) \operatorname{\mathit{then}} (3) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 2))) \operatorname{\mathit{then}} (4) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, p, p\right) = 0) \land (\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right) = 3))) \operatorname{\mathit{then}} (5) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) = p\left(3\right)) \land (p\left(2\right) \ne p\left(3\right))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) = p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land (p\left(2\right) = p\left(3\right))))))))) \operatorname{\mathit{then}} (6) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) = p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land (p\left(2\right) \ne p\left(3\right))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) \ne p\left(3\right)) \land ((p\left(1\right) \ne p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land (p\left(2\right) = p\left(3\right))))))))) \operatorname{\mathit{then}} (7) \operatorname{\mathit{else}} ((\operatorname{\mathit{if}} ((d = 0) \land (((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land (p\left(2\right) \ne p\left(3\right))))))) \lor ((p\left(0\right) \ne p\left(1\right)) \land ((p\left(0\right) \ne p\left(2\right)) \land ((p\left(0\right) = p\left(3\right)) \land ((p\left(1\right) = p\left(2\right)) \land ((p\left(1\right) \ne p\left(3\right)) \land (p\left(2\right) \ne p\left(3\right))))))))) \operatorname{\mathit{then}} (8) \operatorname{\mathit{else}} (9))))))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The 10 equality-and-budget classes. The two-defect extension embeds this class index as its active leading sector.

**Definition 1.4 (Shared T).**

$$(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(10\right), \operatorname{\mathit{Fin}}\left(10\right), \operatorname{\mathit{Int}}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The 10 by 10 exact integer transfer, pinned by finite_certificate. The two-defect extension uses this matrix as its leading block.

**Definition 1.5 (Shared initial).**

$$(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{initial}}: (\operatorname{\mathit{Fin}}\left(10\right)) \to (\operatorname{\mathit{Int}}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The raw labelled initial vector on Fin 10, shared as the leading initial sector and pinned by finite_certificate.

**Definition 1.6 (Shared W).**

$$(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{W}: (\operatorname{\mathit{Fin}}\left(7\right)) \to ((\operatorname{\mathit{Fin}}\left(10\right)) \to (\operatorname{\mathit{Int}})))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The Fin 7 cached forward prefix on Fin 10, shared by the two-defect extension and pinned by finite_certificate.

**Theorem 1.7 (Shared finite_certificate).**

$$(\forall p: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((![0, 0, 0, 1, 1, 1, 1, 1, 1, 1]: (\operatorname{\mathit{Fin}}\left(10\right)) \to (\operatorname{\mathit{Int}}))\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = ((\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}}))))) \land ((\forall p: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{Valid}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right))\right))))))) \land ((\forall p: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(10\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - (\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right))\right) = s)) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229530Strip}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{Valid}}\left(r, 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(10\right), (\sum_{r: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{cl}}\left(r, 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}})) = \operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229530Strip}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(6\right), (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229530Strip}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229530Strip}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{W}\left(6\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(4\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left((![(-16), 56, (-57), 14]\left(j\right): \operatorname{\mathit{Int}}), \operatorname{\mathit{HardinA229530Strip}}.\operatorname{W}\left((\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(2 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right): \operatorname{\mathit{Fin}}\left(7\right))\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

Exact terminal values, validity preservation, successor and initial counts, cached forward recurrence and polynomial relation. The two-defect extension reuses its active successor and initial projections.

**Theorem 1.8 (Proper successor counts from saturated scanner fibres).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(p\right)) \implies (\forall j: \operatorname{\mathit{Fin}}\left(4\right), (16 \cdot (\sum_{q: (\operatorname{\mathit{Fin}}\left(4\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))} (((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{proper}}\left(q\right)) \land ((\operatorname{\mathit{HardinThinGraphTransport}}.\operatorname{\mathit{compatible}}\left(\operatorname{\mathit{true}}, p, q\right)) \land (\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), q\right) = j))) \operatorname{\mathit{then}} (1) \operatorname{\mathit{else}} (0)): \operatorname{\mathit{Int}}))) = \operatorname{\mathit{HardinSourceContinuations}}.\operatorname{M}\left(\operatorname{\mathit{HardinSourceContinuations}}.\operatorname{\mathit{sourceClass}}\left((\operatorname{\mathit{true}}, \operatorname{\mathit{true}}), p\right), j\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.raw_successors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

At saturated Seen flags, sixteen times every actual proper three-colour successor count is the corresponding HardinSourceContinuations.M entry. The theorem applies the frozen four_class_certificate through scanner_fibres and preserves all target classes.

**Definition 1.9 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229582Strip}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229530Strip}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(4\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(4\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 4 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 4 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The filter ranges over every actual array over Fin 3. Canonical uses the lifted row-major order, independently of the transfer sweep. Each listed bond contributes exactly one when its two endpoint colours agree.

**Theorem 1.10 (The registered all-index recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 6\right): \operatorname{\mathit{Int}}) = 14 \cdot (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 5\right): \operatorname{\mathit{Int}}) - 57 \cdot (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 4\right): \operatorname{\mathit{Int}}) + 56 \cdot (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 3\right): \operatorname{\mathit{Int}}) - 16 \cdot (\operatorname{\mathit{HardinA229530Strip}}.\operatorname{a}\left(n + 2\right): \operatorname{\mathit{Int}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229530` (proved) by `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229530","declaration_gid":"D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229530: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229530>.

*Commentary.*

The recurrence holds at every index at least 6. DefectTransfer.lumped_count and forward_shift propagate the finite certificate. The literal row-major canonical representative is independent of the row sweep. canonical_pattern_card supplies the factor six in the range used here, where a constant array cannot have the prescribed defect count. This is a finite combinatorial count and makes no thermodynamic-limit claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.raw_successors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229530Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge](../../../Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinSourceContinuations](../../../Combinatorics/TraceAvoidingArrays/HardinSourceContinuations.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip](../StripDefects/HardinA229582Strip.md)
