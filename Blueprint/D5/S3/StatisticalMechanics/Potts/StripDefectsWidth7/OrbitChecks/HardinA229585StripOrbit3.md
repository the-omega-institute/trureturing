# Exact defective strip colourings

## Abstract

Exact bond-defect transfer and integer recurrence.

Exact successor multisets share the finite enumeration across destination classes. All multiplicities retain the literal labelled-row count.

**Theorem 1.1 (Successor multiset on a class interval).**

$$\forall p: \mathit{Boundary}, (\forall d: \operatorname{\mathit{Fin}}\left(2\right), ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Valid}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)) \implies ((\operatorname{\mathit{HardinA233177Canonical}}.\operatorname{\mathit{Canonical}}\left(p\right)) \implies (((24 \le \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right)) \land (\operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right) < 32)) \implies (\operatorname{\mathit{HardinA229585StripOrbit}}.\operatorname{\mathit{nextClasses}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right) = \operatorname{\mathit{HardinA229585StripOrbit}}.\operatorname{\mathit{images}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, \operatorname{\mathit{Fin}}.\operatorname{\mathit{val}}\left(d\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit3.canonical_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229585: one-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229585>.

*Commentary.*

All canonical boundaries in this interval are checked with their exact residual budget.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/OrbitChecks/HardinA229585StripOrbit3.canonical_next`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](../HardinA229585StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripOrbit](../HardinA229585StripOrbit.md)
