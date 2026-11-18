# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exactly 2 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.

**Definition 1.1 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{antidiagonal}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda i: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (A\left((i, j)\right)))\right)\right) = 2) \land (\forall p: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(n\right)) \times (\operatorname{\mathit{Fin}}\left(5\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot 5 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

Canonical is the original HardinA233177Canonical.Canonical predicate, with order lifted through finProdFinEquiv to retain literal row-major order. The filter enumerates all n by k arrays. The ordinal i*k+j is the original row-major order, matching the row transfer.

**Theorem 1.2 (Exact finite transfer certificate).**

$$(\forall p: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \operatorname{\mathit{Fin}}\left(3\right), ((\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(27\right), (\sum_{r: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229691StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 2) \implies (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{Valid}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 2 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(27\right), (\sum_{r: \operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 2) \land (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{boundary}}\left(r\right), 2 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229583StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229691StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229691StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(7\right), (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229691StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229691StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229691StripData}}.\operatorname{W}\left(7\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-5832), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(14580, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-13122), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(4995, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-729), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(45, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229691StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(1 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The clauses certify acceptance, budget preservation, transition sums, initial admissibility and weights, every forward step and the polynomial relation. The last index has value b+j, bounded by the table length.

**Theorem 1.3 (The registered integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n + 8\right): \mathit{Int}) = 45 \cdot (\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}) - 729 \cdot (\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n + 6\right): \mathit{Int}) + 4995 \cdot (\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n + 5\right): \mathit{Int}) - 13122 \cdot (\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n + 4\right): \mathit{Int}) + 14580 \cdot (\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n + 3\right): \mathit{Int}) - 5832 \cdot (\operatorname{\mathit{HardinA229691Strip}}.\operatorname{a}\left(n + 2\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229691` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229691","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229691: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229691>.

*Commentary.*

The row transfer counts labelled arrays. the original row-major canonical representatives have six labelled realizations. Multiplication propagates the certified vector relation to every further length.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583Strip](HardinA229583Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripCertificate](HardinA229691StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses0](HardinA229691StripClasses0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses1](HardinA229691StripClasses1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses10](HardinA229691StripClasses10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses11](HardinA229691StripClasses11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses12](HardinA229691StripClasses12.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses13](HardinA229691StripClasses13.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses2](HardinA229691StripClasses2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses3](HardinA229691StripClasses3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses4](HardinA229691StripClasses4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses5](HardinA229691StripClasses5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses6](HardinA229691StripClasses6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses7](HardinA229691StripClasses7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses8](HardinA229691StripClasses8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripClasses9](HardinA229691StripClasses9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229691StripData](HardinA229691StripData.md)
