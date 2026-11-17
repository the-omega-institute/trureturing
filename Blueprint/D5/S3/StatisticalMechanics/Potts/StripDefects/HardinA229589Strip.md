# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exactly 1 monochromatic bonds are allowed. These are unsatisfied bonds of the three-state Potts antiferromagnet; the theorem concerns finite combinatorial counts.

**Definition 1.1 (The literal canonical array count).**

$$\forall n: \mathit{Nat}, (\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n\right) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda A: ((\operatorname{\mathit{Fin}}\left(4\right)) \times (\operatorname{\mathit{Fin}}\left(n\right))) \to (\operatorname{\mathit{Fin}}\left(3\right)) \mapsto ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{defects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}}, \operatorname{\mathit{List}}.\operatorname{\mathit{ofFn}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(n\right) \mapsto (\lambda i: \operatorname{\mathit{Fin}}\left(4\right) \mapsto (A\left((i, j)\right)))\right)\right) = 1) \land (\forall p: (\operatorname{\mathit{Fin}}\left(4\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), (\forall c: \operatorname{\mathit{Fin}}\left(3\right), ((c < A\left(p\right)) \implies (\exists q: (\operatorname{\mathit{Fin}}\left(4\right)) \times (\operatorname{\mathit{Fin}}\left(n\right)), ((\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(q\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(q\right)\right) < \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{fst}}\left(p\right)\right) \cdot n + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{Prod}}.\operatorname{\mathit{snd}}\left(p\right)\right)) \land (A\left(q\right) = c))))))), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.a` (`✓ std3`).

*Citation.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

Canonical is the original HardinA233177Canonical.Canonical predicate, with order lifted through finProdFinEquiv to retain literal row-major order. The filter enumerates all k by n arrays. The ordinal i*n+j is the original row-major order, including when transfer sweeps columns.

**Theorem 1.2 (Exact finite transfer certificate).**

$$(\forall p: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{terminal}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) = (\operatorname{\mathit{if}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) = 0) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0))))) \land ((\forall p: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall r: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \implies (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Valid}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right))))))) \land ((\forall p: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(28\right), (\sum_{r: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)) \land (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{cl}}\left(r, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right) - \left(\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{between}}, p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229589StripData}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right), s\right)))))) \land ((\forall r: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \implies (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Valid}}\left(r, 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)))) \land ((\forall s: \operatorname{\mathit{Fin}}\left(28\right), (\sum_{r: \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le 1) \land (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{cl}}\left(r, 1 - \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right) = s)) \operatorname{\mathit{then}} 1 \operatorname{\mathit{else}} 0)) = \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{initial}}\left(s\right))) \land (((\operatorname{\mathit{HardinA229589StripData}}.\operatorname{W}\left(0\right) = \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{initial}}) \land (\forall i: \operatorname{\mathit{Fin}}\left(12\right), (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(i\right)\right) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecMul}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(i\right)\right), \operatorname{\mathit{HardinA229589StripData}}.\operatorname{T}\right)))) \land (\operatorname{\mathit{HardinA229589StripData}}.\operatorname{W}\left(12\right) = \sum_{j: \operatorname{\mathit{Fin}}\left(6\right)} (\operatorname{\mathit{HSMul}}.\operatorname{\mathit{hSMul}}\left(\operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-36), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(180, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-333), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(282, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left((-111), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecCons}}\left(18, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{vecEmpty}}\right)\right)\right)\right)\right)\right)\left(j\right), \operatorname{\mathit{HardinA229589StripData}}.\operatorname{W}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{mk}}\left(6 + \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(j\right)\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

The clauses certify acceptance, budget preservation, transition sums, initial admissibility and weights, every forward step and the polynomial relation. The last index has value b+j, bounded by the table length.

**Theorem 1.3 (The registered integer recurrence).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n + 13\right): \mathit{Int}) = 18 \cdot (\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n + 12\right): \mathit{Int}) - 111 \cdot (\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n + 11\right): \mathit{Int}) + 282 \cdot (\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n + 10\right): \mathit{Int}) - 333 \cdot (\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n + 9\right): \mathit{Int}) + 180 \cdot (\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n + 8\right): \mathit{Int}) - 36 \cdot (\operatorname{\mathit{HardinA229589Strip}}.\operatorname{a}\left(n + 7\right): \mathit{Int}))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229589` (proved) by `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229589","declaration_gid":"D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229589: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229589>.

*Commentary.*

The column transfer counts labelled arrays. Coordinate exchange is an equivalence of labelled arrays; the original row-major canonical representatives have six labelled realizations. Multiplication propagates the certified vector relation to every further length.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.a`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589Strip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripCertificate](HardinA229589StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses0](HardinA229589StripClasses0.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses1](HardinA229589StripClasses1.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses10](HardinA229589StripClasses10.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses11](HardinA229589StripClasses11.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses12](HardinA229589StripClasses12.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses13](HardinA229589StripClasses13.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses2](HardinA229589StripClasses2.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses3](HardinA229589StripClasses3.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses4](HardinA229589StripClasses4.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses5](HardinA229589StripClasses5.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses6](HardinA229589StripClasses6.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses7](HardinA229589StripClasses7.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses8](HardinA229589StripClasses8.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripClasses9](HardinA229589StripClasses9.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](HardinA229589StripData.md)
