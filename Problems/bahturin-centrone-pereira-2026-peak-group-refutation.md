---
slug: bahturin-centrone-pereira-2026-peak-group-refutation
bibkey: bahturincentronepereira2026peak
doi: 10.48550/arXiv.2608.21936
url: https://arxiv.org/abs/2608.21936v1
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/BahturinCentronePereiraPeakGroups.result
---

## Problem

Bahturin, Centrone and Pereira, *Quantum regularity of finite dimensional semisimple algebras*, arXiv:2608.21936v1, Conjecture 31, asks whether every peak group satisfies exactly one of solvability and the stated Frobenius-complement alternative. The preregistration is [#19254](https://github.com/the-omega-institute/trureturing/issues/19254).

The settling declaration is `D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.result`. It proves the negation of the literal `claim`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A peak group has a greatest irreducible-character degree for divisibility. | `BCP31.IsPeak` and `BCP31.degreeSet` | The degree set is defined by simple finite-dimensional complex representations, and every degree divides the selected degree. |
| A Frobenius complement is nontrivial, proper, and has trivial intersection with each conjugate outside it. | `BCP31.IsFrobeniusWithComplement` | The subgroup-map expression is the literal conjugation condition. |
| The complement quotient contains the specified `SL(2, 5) × T` normal subgroup, with cyclic Sylows and excluded primes. | `BCP31.ComplementCondition` and `BCP31.AlternativeTwo` | The quantified finite group $T$ and all three structural conditions are retained. The cyclic-Sylow condition is written directly as a quantification over primes and Sylow subgroups; Mathlib’s `IsZGroup` states the corresponding property and is not on the proof dependency path. |
| Exactly one of solvability and the Frobenius alternative holds for every finite peak group. | `BCP31.claim` | The result proves the full negation, including the exclusive-or conjunction. |

## Motivation

The counterexample is the direct product $B \times C_2$, where $B$ is the source's semidirect product of $(\mathbb{Z}/11\mathbb{Z})^2$ by $\mathrm{SL}(2,5)$. The supporting declarations show that $B$ has peak degree $120$, that adjoining the abelian factor preserves the simple degree set, and that the resulting group is nonsolvable.

## Gap

The source leaves Conjecture 31 open. The settlement addresses the conjecture through the concrete group specified in #19254. Literature completeness remains `ASSUMED-UNVERIFIED`; the source and the recorded literature screen do not establish an exhaustive search of later work.

## Route

The module constructs the sparse $\mathrm{SL}(2,5)$ action on $(\mathbb{Z}/11\mathbb{Z})^2$, verifies the finite action certificates, forms the semidirect product and its direct product with $C_2$, constructs a simple degree-$120$ representation, and proves that every simple degree divides $120$. The abelian-product theorem transfers peakness. The central-obstruction theorem shows that a nontrivial central element rules out every Frobenius complement, while the $\mathrm{SL}(2,5)$ quotient rules out solvability.

## Falsifier

A finite group satisfying the literal `claim` would not falsify the result. A contradiction would require a counterexample to one of the kernel-checked declarations, especially the degree divisibility, degree-$120$ simplicity, or central obstruction statements.

## Evidence

The compiled settling module has the public definitions `degreeSet`, `IsPeak`, `IsFrobeniusWithComplement`, `fitting`, `HasAllowedOrder`, `ComplementCondition`, `AlternativeTwo`, and `claim`, together with the public theorem `result`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). The other public theorems in the delivered modules have an unfinished escape audit recorded in [#19389](https://github.com/the-omega-institute/trureturing/issues/19389).

### Proof shape

The classification expands every same-delivery helper, public or private, across all ten modules and stops at the protected frozen base or pinned Mathlib. A theorem is content when its own non-normalization step or a same-delivery content proposition remains on its proof path. The invariant-span proposition `CliffordConstituents.TauCeti.Representation.iSup_conjSubrep_eq_top` is the surviving witness for the common multiplicity and restriction isomorphism results. Their atom-existence projections do not retain universal conjugacy. The multiplicity comparison instead uses the conjugate-isomorphism classification and its invariant-span proof. The supporting modules use `escape-witness`; the settling module uses `open-problem-resolution (#19254; Refuted)`.

The module keys below name their Lean namespaces. Numeric witness and consumer references point to the `id` column of this same table; private declarations use their fully qualified source names. Direct frozen dependencies are absent: the mathematical prerequisites here are pinned Mathlib or same-delivery declarations.

- A: `D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups`.
- B: `D5.S3.FiniteGroups.CharacterDegreeDivisibility`.
- C: `D5.S3.FiniteGroups.CliffordConstituents`.
- D: `D5.S3.FiniteGroups.CliffordDecomposition`.
- E: `D5.S3.FiniteGroups.ComplexCharacterAbelianProducts`.
- F: `D5.S3.FiniteGroups.FiniteCharacterAlgebra`.
- G: `D5.S3.FiniteGroups.FrobeniusCentralObstruction`.
- H: `D5.S3.FiniteGroups.FrobeniusCharacterDegrees`.
- I: `D5.S3.FiniteGroups.InducedCharacterFormula`.
- J: `D5.S3.FiniteGroups.MackeyCharacterFormula`.

|id|module|declaration|proof_shape|escape_witness|direct consumers|direct frozen dependencies|
|---|---|---|---|---|---|---|
|1|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.factPrimeFive`|bind-only|none|43,21,55,60,20,44,45,46,47,48,28,29,30,31,32,41,50,39,36,40,37,22,23,24,25,26|none|
|2|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.factPrimeEleven`|bind-only|none|56,75,76,43,21,20,12,14,15,16,17,18,69,71,70,72,44,45,46,47,48,54,65,67,28,29,30,31,32,50,36,37,52,53,57,51,19,77,22,23,24,25,26,58,59,63,64,66,74,68,73|none|
|3|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degreeSet`|bind-only|none|76,4,77|none|
|4|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.IsPeak`|bind-only|none|11,62,77|none|
|5|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.IsFrobeniusWithComplement`|bind-only|none|10,62|none|
|6|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.fitting`|bind-only|none|9|none|
|7|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.fitting_normal`|bind-only|none|9|none|
|8|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.HasAllowedOrder`|bind-only|none|9|none|
|9|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.ComplementCondition`|bind-only|none|10,62|none|
|10|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.AlternativeTwo`|bind-only|none|11,62|none|
|11|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.claim`|bind-only|none|62|none|
|12|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable`|bind-only|none|43,21,20,14,15,16,17,18,44,45,46,47,48,28,29,30,31,32,36,37,13,19,22,23,24,25,26|none|
|13|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.rawAction`|bind-only|none|34,36,37,19|none|
|14|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_det0`|bind-only|none|19|none|
|15|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_det1`|bind-only|none|19|none|
|16|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_det2`|bind-only|none|19|none|
|17|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_det3`|bind-only|none|19|none|
|18|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_det4`|bind-only|none|19|none|
|19|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.rawAction_det`|bind-only|none|34|none|
|20|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.UpperCertificate`|bind-only|none|27|none|
|21|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.LowerCertificate`|bind-only|none|33|none|
|22|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.upper_one_0`|bind-only|none|27|none|
|23|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.upper_one_1`|bind-only|none|27|none|
|24|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.upper_one_2`|bind-only|none|27|none|
|25|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.upper_one_3`|bind-only|none|27|none|
|26|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.upper_one_4`|bind-only|none|27|none|
|27|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_upper_one`|bind-only|none|36|none|
|28|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.lower_one_0`|bind-only|none|33|none|
|29|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.lower_one_1`|bind-only|none|33|none|
|30|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.lower_one_2`|bind-only|none|33|none|
|31|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.lower_one_3`|bind-only|none|33|none|
|32|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.lower_one_4`|bind-only|none|33|none|
|33|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_lower_one`|bind-only|none|37|none|
|34|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixActionValue`|bind-only|none|42,41,35,38,39,36,40,37|none|
|35|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixActionValue_one`|bind-only|none|42,39,40|none|
|36|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixAction_transvection0_one`|bind-only|none|39|none|
|37|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixAction_transvection1_one`|bind-only|none|40|none|
|38|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixActionValue_pow_mul`|bind-only|none|39,40|none|
|39|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixAction_transvection0`|bind-only|none|41|none|
|40|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixAction_transvection1`|bind-only|none|41|none|
|41|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixActionValue_mul`|bind-only|none|42|none|
|42|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixAction`|bind-only|none|50,53,57,51,59|none|
|43|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.FixedCertificate`|bind-only|none|49|none|
|44|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.fixed_0`|bind-only|none|49|none|
|45|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.fixed_1`|bind-only|none|49|none|
|46|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.fixed_2`|bind-only|none|49|none|
|47|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.fixed_3`|bind-only|none|49|none|
|48|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.fixed_4`|bind-only|none|49|none|
|49|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.actionTable_fixed`|bind-only|none|50|none|
|50|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.matrixAction_no_eigenvalue_one`|bind-only|none|57,59|none|
|51|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.pairLinearAction`|bind-only|none|52|none|
|52|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.pairAction`|bind-only|none|56,75,76,69,71,70,72,54,65,67,53,57,77,59,63,64,66,74,68,73|none|
|53|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.pairAction_apply`|bind-only|none|59|none|
|54|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.instFiniteSemidirectProductMultiplicativeProdZModOfNatNatSpecialLinearGroupFinPairAction`|bind-only|none|75,70|none|
|55|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.SL2F5_card`|bind-only|none|56,68|none|
|56|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.B_card`|bind-only|none|75|none|
|57|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.pairAction_fixed`|bind-only|none|74|none|
|58|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorCharacter`|bind-only|none|65,67,59|none|
|59|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorCharacter_free_orbit`|bind-only|none|67|none|
|60|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.SL2F5_not_solvable`|bind-only|none|61|none|
|61|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.semidirect_C2_not_solvable`|bind-only|none|62|none|
|62|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.refutation_of_peak`|content|317|77|none|
|63|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorKernelEquiv`|bind-only|none|65,67,64,66,74,73|none|
|64|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorKernelEquivSymmApply`|bind-only|none|66|none|
|65|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.kernelCharacter`|bind-only|none|69,71,70,67|none|
|66|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorKernel_conj`|bind-only|none|67,74|none|
|67|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.kernelCharacter_free_orbit`|bind-only|none|70|none|
|68|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorKernel_index`|bind-only|none|75,71|none|
|69|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120Representation`|bind-only|none|71,72|none|
|70|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120Representation_simple`|content|443|72|none|
|71|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120Representation_finrank`|bind-only|none|72|none|
|72|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.degree120_mem`|content|443|76|none|
|73|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorKernel_isMulCommutative`|bind-only|none|75|none|
|74|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.vectorKernel_fixedPointFree`|bind-only|none|75|none|
|75|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.B_degree_dvd`|content|324|76|none|
|76|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.B_peak`|content|324|77|none|
|77|A|`D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.result`|content|231|terminal|none|
|78|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centerToEnd`|bind-only|none|79,80|none|
|79|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.centralCharacter`|bind-only|none|85,84,87,105,104,88,86|none|
|80|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.smul_eq_centralCharacter_smul`|bind-only|none|84|none|
|81|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.isIntegral_classSumCenter`|bind-only|none|88|none|
|82|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.asAlgebraHom_classSum`|bind-only|none|83|none|
|83|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.trace_asAlgebraHom_classSum`|bind-only|none|87|none|
|84|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.asAlgebraHom_center_apply`|bind-only|none|85|none|
|85|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.asAlgebraHom_center`|bind-only|none|86|none|
|86|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.trace_asAlgebraHom_center`|bind-only|none|87|none|
|87|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one`|bind-only|none|104|none|
|88|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.isIntegral_centralCharacter_classSumCenter`|bind-only|none|105|none|
|89|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.pow_eq_one_of_isRoot_charpoly`|bind-only|none|90,95|none|
|90|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.isIntegral_trace_of_pow_eq_one_of_splits`|bind-only|none|91|none|
|91|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.isIntegral_trace_of_pow_eq_one`|bind-only|none|101|none|
|92|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.isSemisimple_of_pow_eq_one`|bind-only|none|98,96|none|
|93|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.mapsTo_pow_eigenspace`|bind-only|none|97,94|none|
|94|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.trace_restrict_eigenspace`|bind-only|none|97|none|
|95|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.pow_eq_one_of_hasEigenvalue`|bind-only|none|98|none|
|96|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.isInternal_eigenspace_of_pow_eq_one`|bind-only|none|97|none|
|97|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.trace_pow_eq_sum_eigenvalue_pow`|bind-only|none|98|none|
|98|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.Module.End.exists_eq_smul_of_norm_trace_eq_finrank`|bind-only|none|99|none|
|99|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.eq_one_of_trace_eq_finrank`|bind-only|none|100|none|
|100|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.End.trace_eq_finrank_iff`|bind-only|none|326|none|
|101|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.isIntegral_char`|bind-only|none|105|none|
|102|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.dvd_of_isIntegral_of_natCast_mul_eq`|bind-only|none|105|none|
|103|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.character_mul_character_inv_mem_classFunction`|bind-only|none|104|none|
|104|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card`|bind-only|none|105|none|
|105|B|`D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card`|content|105|321|none|
|106|C|`D5.S3.FiniteGroups.CliffordConstituents.MonoidAlgebra.conjNormalAlgAut`|bind-only|none|166,173,170|none|
|107|C|`D5.S3.FiniteGroups.CliffordConstituents.MonoidAlgebra.conjNormalAlgAut_single`|bind-only|none|166|none|
|108|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.mem_conj_smul`|bind-only|none|381,397|none|
|109|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conj_mul_smul`|bind-only|none|392|none|
|110|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.coe_conjSubgroupEquiv_apply`|bind-only|none|406|none|
|111|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.apply_conjNormal_inv`|bind-only|none|166,127,136|none|
|112|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormal_inv_one`|bind-only|none|115|none|
|113|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormal_inv_mul`|bind-only|none|116|none|
|114|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepFunctor`|bind-only|none|125,126,191,116,115,121,124,122,118,117,190,189,123,222,220,226,221,193,223,225,323,422,430,442,433,443|none|
|115|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepFunctor_one`|bind-only|none|117|none|
|116|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepFunctor_mul`|bind-only|none|118|none|
|117|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRep_one`|bind-only|none|124|none|
|118|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRep_mul`|bind-only|none|124|none|
|119|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepEquiv`|bind-only|none|120,430|none|
|120|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepEquiv_functor`|bind-only|none|430|none|
|121|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepIso`|bind-only|none|190|none|
|122|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepSkeletonSMul`|bind-only|none|124,189,199,202,203,204,205,206,207,208,200,193|none|
|123|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.smul_toSkeleton`|bind-only|none|124,189,193|none|
|124|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.conjNormalFDRepSkeletonMulAction`|bind-only|none|191,190,189,222,220,227,226,221,207,208,209,223,224,225,324,322,323,325|none|
|125|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.char_conjNormalFDRep`|bind-only|none|126,323|none|
|126|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.char_conjNormalFDRep_mk`|bind-only|none|191|none|
|127|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.conjSubrep`|bind-only|none|146,145,182,178,179,136,133,132,130,143,141,138,137,135,139,144,129,128,227,199,192,200,193,223|none|
|128|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.toSubmodule_conjSubrep`|bind-only|none|133,132,130,137|none|
|129|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.mem_conjSubrep_iff`|bind-only|none|178|none|
|130|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.conjSubrep_eq_self_of_mem`|bind-only|none|131|none|
|131|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.conjSubrep_one`|bind-only|none|133|none|
|132|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.conjSubrep_conjSubrep`|bind-only|none|133,137|none|
|133|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.conjSubrepOrderIso`|bind-only|none|134,135|none|
|134|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.conjSubrepOrderIso_apply`|bind-only|none|135|none|
|135|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isAtom_conjSubrep_iff`|bind-only|none|141,139,144,199,223|none|
|136|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.conjSubrepEquiv`|bind-only|none|192|none|
|137|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.iSup_conjSubrep_eq_top`|content|137|138|none|
|138|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.iSup_asSubmodule_conjSubrep_eq_top`|content|137|141,139|none|
|139|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isSemisimpleRepresentation_comp_subtype_of_isAtom`|content|137|140|none|
|140|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isSemisimpleRepresentation_comp_subtype`|content|137|225|none|
|141|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_nonempty_linearEquiv_asSubmodule_conjSubrep`|content|137|179,142,144,200|none|
|142|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_nonempty_linearEquiv_conjSubrep`|content|137|143|none|
|143|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep`|content|137|182,227|none|
|144|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.isotypicComponents_eq_range`|content|137|145|none|
|145|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjSubrepIsotypicComponent`|bind-only|none|199,204,208,209,223|none|
|146|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.coe_conjSubrepIsotypicComponent`|bind-only|none|223|none|
|147|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.le_isotypicComponent_iff_nonempty_linearEquiv`|bind-only|none|154|none|
|148|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.SimpleSubmoduleClasses`|bind-only|none|151,152,154,197,199,198,201,196,200,195|none|
|149|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.SimpleSubmoduleClasses.mk`|bind-only|none|151,153,154,199,196,200,195|none|
|150|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.SimpleSubmoduleClasses.mk_eq_mk_iff`|bind-only|none|154,196|none|
|151|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.SimpleSubmoduleClasses.ind`|bind-only|none|154,196,200|none|
|152|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.SimpleSubmoduleClasses.lift`|bind-only|none|153,154,194,195|none|
|153|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.SimpleSubmoduleClasses.lift_mk`|bind-only|none|195|none|
|154|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.simpleSubmoduleClassesEquiv`|bind-only|none|197,199,198,201|none|
|155|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_pi_eq_natCard`|bind-only|none|156|none|
|156|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi`|bind-only|none|157|none|
|157|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_eq_natCard_of_linearEquiv_pi_const`|bind-only|none|162|none|
|158|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.isotypicComponent_self_eq_top`|bind-only|none|159|none|
|159|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.apply_mem_isotypicComponent`|bind-only|none|160|none|
|160|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.linearMapIsotypicComponentEquiv`|bind-only|none|161|none|
|161|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_isotypicComponent`|bind-only|none|162|none|
|162|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.nonempty_linearEquiv_isotypicComponent`|bind-only|none|223|none|
|163|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.finrank_linearMap_pos_of_ne_bot`|bind-only|none|181|none|
|164|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.asModuleConjEquiv`|bind-only|none|165,166,173,177,175,167,169,170|none|
|165|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.asModuleConjEquiv_apply`|bind-only|none|166|none|
|166|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.asModuleConjEquiv_smul`|bind-only|none|173,170|none|
|167|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjSubrepMap`|bind-only|none|168,173,177,175,169,171,172,170|none|
|168|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.coe_conjSubrepMap`|bind-only|none|169,170|none|
|169|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjSubrepMap_add`|bind-only|none|173|none|
|170|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjSubrepMap_smul`|bind-only|none|173|none|
|171|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjSubrepMap_inv_self_apply`|bind-only|none|177|none|
|172|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjSubrepMap_self_inv_apply`|bind-only|none|177|none|
|173|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjHom`|bind-only|none|177,174,175|none|
|174|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjHom_apply`|bind-only|none|177,175|none|
|175|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjHomₗ`|bind-only|none|177,176|none|
|176|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjHomₗ_apply`|bind-only|none|177|none|
|177|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.conjHomEquiv`|bind-only|none|178|none|
|178|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.finrank_linearMap_conjSubrep`|bind-only|none|179|none|
|179|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.finrank_linearMap_eq_of_isAtom`|content|137|180|none|
|180|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.finrank_linearMap_eq_of_isAtom_of_isAtom`|content|137|182|none|
|181|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.finrank_linearMap_pos`|bind-only|none|182|none|
|182|C|`D5.S3.FiniteGroups.CliffordConstituents.Representation.exists_forall_finrank_linearMap_eq`|content|137|226|none|
|183|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.equivOfAsModuleLinearEquiv`|bind-only|none|185,186,226|none|
|184|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.asModuleLinearEquivOfEquiv`|bind-only|none|185,187,192,223|none|
|185|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation.nonempty_equiv_iff`|bind-only|none|188|none|
|186|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.fdRepIsoOfAsModuleLinearEquiv`|bind-only|none|187,192|none|
|187|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.nonempty_fdRepIso_iff`|bind-only|none|188,226,223|none|
|188|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.toSkeleton_fdRepOf_toRepresentation_eq_iff`|bind-only|none|199,194,196,200,195|none|
|189|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.mem_inertia_iff`|bind-only|none|191,190|none|
|190|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.le_inertia`|bind-only|none|322|none|
|191|C|`D5.S3.FiniteGroups.CliffordConstituents.TauCeti.char_conj_eq_of_mem_inertia`|bind-only|none|322|none|
|192|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.fdRepIsoConjSubrep`|bind-only|none|193,223|none|
|193|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.toSkeleton_fdRepOf_conjSubrep`|bind-only|none|199,200|none|
|194|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton`|bind-only|none|197,199,196,200,195|none|
|195|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mk`|bind-only|none|199,196,200|none|
|196|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_injective`|bind-only|none|198|none|
|197|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap`|bind-only|none|199,198,202,204|none|
|198|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_injective`|bind-only|none|203|none|
|199|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_conjSubrepIsotypicComponent`|bind-only|none|204,208|none|
|200|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.submoduleClassToSkeleton_mem_orbit`|content|137|201|none|
|201|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentClassMap_mem_orbit`|content|137|202|none|
|202|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentOrbitMap`|bind-only|none|203,204,205,208|none|
|203|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentOrbitMap_injective`|bind-only|none|205|none|
|204|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentOrbitMap_surjective`|bind-only|none|205|none|
|205|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentsEquivOrbit`|bind-only|none|206,207,208|none|
|206|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.componentsEquivOrbit_apply`|bind-only|none|208|none|
|207|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia`|content|137|208,209,223,224,225|none|
|208|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_conjSubrepIsotypicComponent`|bind-only|none|209|none|
|209|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.isotypicComponentsEquivQuotientInertia_symm_mk`|bind-only|none|223|none|
|210|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.isUnit_natCard_subgroup`|bind-only|none|368,416,420|none|
|211|D|`D5.S3.FiniteGroups.CliffordDecomposition.LinearMap.trace_pi_of_apply_eq`|bind-only|none|374|none|
|212|D|`D5.S3.FiniteGroups.CliffordDecomposition.LinearMap.trace_pi_of_apply_eq_dependent`|bind-only|none|217|none|
|213|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.Representation.ofModule'_apply`|bind-only|none|218|none|
|214|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.Representation.asAlgebraHom_ofModule'`|bind-only|none|215|none|
|215|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.Representation.asAlgebraHom_ofModule'_apply`|bind-only|none|216|none|
|216|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.Representation.ofModule'AsModuleEquiv`|bind-only|none|226|none|
|217|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.Representation.char_ofModule'_pi`|bind-only|none|222|none|
|218|D|`D5.S3.FiniteGroups.CliffordDecomposition.Representation.char_ofModule'_asModule`|bind-only|none|222|none|
|219|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.IsSemisimpleModule.linearEquivIsotypicComponents`|bind-only|none|225|none|
|220|D|`D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum`|bind-only|none|222,227,226,221,324,323,325|none|
|221|D|`D5.S3.FiniteGroups.CliffordDecomposition.FDRep.finrank_cliffordSum`|bind-only|none|325|none|
|222|D|`D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum`|bind-only|none|323|none|
|223|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.componentLinearEquiv`|bind-only|none|225|none|
|224|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.finite_quotient_inertia`|content|137|226|none|
|225|D|`D5.S3.FiniteGroups.CliffordDecomposition.TauCeti.restrictLinearEquivPi`|content|137|226|none|
|226|D|`D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso_of_isAtom`|content|137|227|none|
|227|D|`D5.S3.FiniteGroups.CliffordDecomposition.FDRep.clifford_restrict_iso`|content|137|325|none|
|228|E|`D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.central_action_scalar`|bind-only|none|229,319|none|
|229|E|`D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.firstFactorSubrepresentationOrderIso`|bind-only|none|230|none|
|230|E|`D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.irreducible_firstFactor`|bind-only|none|231|none|
|231|E|`D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.degreesProdAbelian`|content|231|77|none|
|232|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_bot`|bind-only|none|137,236,310,306,307|none|
|233|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_top`|bind-only|none|138,237,310,306,307|none|
|234|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_le_toSubmodule`|bind-only|none|309|none|
|235|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toSubmodule_lt_toSubmodule`|bind-only|none|309|none|
|236|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IntertwiningMap.eq_zero_iff_range_eq_bot`|bind-only|none|243|none|
|237|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IntertwiningMap.surjective_iff_range_eq_top`|bind-only|none|244|none|
|238|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype`|bind-only|none|239,241,243,242,244,240,251,257,253,254,249,250,252,256|none|
|239|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.coe_subtype`|bind-only|none|242|none|
|240|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.toLinearMap_subtype`|bind-only|none|241|none|
|241|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.range_subtype`|bind-only|none|243,244|none|
|242|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype_injective`|bind-only|none|249|none|
|243|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype_eq_zero_iff`|bind-only|none|250|none|
|244|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.subtype_surjective_iff`|bind-only|none|251|none|
|245|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.coe_toRepresentation_asAlgebraHom_apply`|bind-only|none|246|none|
|246|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.asModuleEquivAsSubmodule`|bind-only|none|188,223|none|
|247|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Subrepresentation.isSimpleModule_asSubmodule_iff`|bind-only|none|180,141,142,139,144,199,223|none|
|248|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Rep.simple_iff_isIrreducible`|bind-only|none|258|none|
|249|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.mono_repOfHom_subtype`|bind-only|none|254|none|
|250|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.repOfHom_subtype_eq_zero_iff`|bind-only|none|256|none|
|251|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.epi_repOfHom_subtype_iff`|bind-only|none|257|none|
|252|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion`|bind-only|none|258,255,257,254,256|none|
|253|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.map_subInclusion`|bind-only|none|257,254,256|none|
|254|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.mono_map_subInclusion`|bind-only|none|255,257|none|
|255|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.instMonoFDRepSubInclusion`|bind-only|none|258|none|
|256|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.subInclusion_eq_zero_iff`|bind-only|none|258|none|
|257|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.isIso_subInclusion_iff`|bind-only|none|258|none|
|258|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_iff_isIrreducible`|bind-only|none|260,259|none|
|259|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible`|bind-only|none|227,231,439|none|
|260|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple`|bind-only|none|75,227,226,231,319,321,320|none|
|261|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.character_actionRes`|bind-only|none|284,323|none|
|262|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.moduleFiniteForgetObject`|bind-only|none|376,365,363,364|none|
|263|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.finrankForgetObject`|bind-only|none|365|none|
|264|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.characterForgetObject`|bind-only|none|376|none|
|265|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.of_ρ_eq_self`|bind-only|none|187|none|
|266|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.ofShrink`|bind-only|none|222,220,226,221,269,268,267,363|none|
|267|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.ofShrinkEquiv`|bind-only|none|226,269,364|none|
|268|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.finrank_ofShrink`|bind-only|none|221|none|
|269|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.character_ofShrink`|bind-only|none|222|none|
|270|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction`|bind-only|none|103,105,104,312,313,316,314,275,276,284,272,271,278,279,277,273,274,348,349,378,373,369,368,346,345,347,367,366,416,418,417,414,413,409,410,411,420,419|none|
|271|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.mem_iff`|bind-only|none|103,373,346,345,366,417,409|none|
|272|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.eq_of_isConj`|bind-only|none|273|none|
|273|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.toConjClasses`|bind-only|none|105,104,277,274|none|
|274|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.toConjClasses_mk`|bind-only|none|105,104,277|none|
|275|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.comap`|bind-only|none|276,284,369,416,418,417,414,420|none|
|276|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.comap_apply`|bind-only|none|284,369,417,414|none|
|277|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.sum_eq_sum_conjClasses`|bind-only|none|104|none|
|278|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.ofCharacter`|bind-only|none|105,104,315,316,284,279,378,420,419|none|
|279|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.ofCharacter_apply`|bind-only|none|105,104,284,378|none|
|280|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.actionRes_comp`|bind-only|none|116,422|none|
|281|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.finrank_hom_res_mulEquiv`|bind-only|none|424,422|none|
|282|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.resSubrepresentationOrderIso`|bind-only|none|283|none|
|283|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.isIrreducible_comp_surjective_iff`|bind-only|none|231,321|none|
|284|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.comap_subtype_ofFDRep`|bind-only|none|420|none|
|285|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.classSum`|bind-only|none|82,87,83,81,291,289,286,290|none|
|286|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.classSum_eq_sum`|bind-only|none|82,81,289|none|
|287|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.conjugateCarrierEquiv`|bind-only|none|289,288|none|
|288|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.conjugateCarrierEquiv_apply`|bind-only|none|289|none|
|289|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.classSum_commutes`|bind-only|none|290|none|
|290|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.classSum_mem_center`|bind-only|none|291|none|
|291|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.classSumCenter`|bind-only|none|87,105,104,88,81,292|none|
|292|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.classSumCenter_coe`|bind-only|none|87,81|none|
|293|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.finite_end_of_smulCommClass`|bind-only|none|308|none|
|294|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.hom_eq_zero_of_isEmpty_linearEquiv`|bind-only|none|295|none|
|295|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.subsingleton_linearMap_of_isEmpty_linearEquiv`|bind-only|none|301,300|none|
|296|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.endAlgEquivSelfOfIsSimpleModule`|bind-only|none|79,80,308,298,297,302|none|
|297|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.endAlgEquivSelfOfIsSimpleModule_symm_apply`|bind-only|none|298|none|
|298|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.endAlgEquivSelfOfIsSimpleModule_smul`|bind-only|none|80,308|none|
|299|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.homCongrRight`|bind-only|none|156,303,302|none|
|300|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.finrank_linearMap_eq_zero_of_isEmpty_linearEquiv`|bind-only|none|155|none|
|301|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.finiteDimensional_linearMap_of_isEmpty_linearEquiv`|bind-only|none|303|none|
|302|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.finrank_linearMap_eq_one_of_nonempty_linearEquiv`|bind-only|none|155|none|
|303|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.finiteDimensional_linearMap_of_isSimpleModule`|bind-only|none|155|none|
|304|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.nontrivial`|bind-only|none|105,143,140,305,308|none|
|305|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.IsIrreducible.finrank_pos`|bind-only|none|75|none|
|306|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one`|bind-only|none|435|none|
|307|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_toRepresentation_of_isAtom`|bind-only|none|227|none|
|308|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible`|content|308|320|none|
|309|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.exists_isAtom_le`|bind-only|none|310|none|
|310|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.exists_isAtom`|bind-only|none|143,140|none|
|311|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.card_inv_mul_sum_mul_smul`|bind-only|none|312|none|
|312|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.characterPairing`|bind-only|none|313,316,314,369,416,418,417,420|none|
|313|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.characterPairing_apply`|bind-only|none|315,314,369,417|none|
|314|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.characterPairing_symm`|bind-only|none|416|none|
|315|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.characterPairing_ofFDRep`|bind-only|none|316|none|
|316|F|`D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank`|bind-only|none|420|none|
|317|G|`D5.S3.FiniteGroups.FrobeniusCentralObstruction.central_eq_one_of_frobenius`|content|317|62|none|
|318|H|`D5.S3.FiniteGroups.FrobeniusCharacterDegrees.trivial_of_invariant_fixedPointFree`|bind-only|none|322|none|
|319|H|`D5.S3.FiniteGroups.FrobeniusCharacterDegrees.abelian_character_eq_iff`|bind-only|none|322|none|
|320|H|`D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_square_le_card`|content|308|75|none|
|321|H|`D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_quotient_card`|content|105|324|none|
|322|H|`D5.S3.FiniteGroups.FrobeniusCharacterDegrees.inertia_eq_of_fixedPointFree`|bind-only|none|324|none|
|323|H|`D5.S3.FiniteGroups.FrobeniusCharacterDegrees.restriction_trivial_of_clifford_constituent_trivial`|bind-only|none|324|none|
|324|H|`D5.S3.FiniteGroups.FrobeniusCharacterDegrees.degree_dvd_or_index_dvd_of_fixedPointFree`|content|324|75|none|
|325|I|`D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank`|content|137|324|none|
|326|I|`D5.S3.FiniteGroups.InducedCharacterFormula.Representation.char_eq_finrank_iff_of_pow_eq_one`|bind-only|none|327|none|
|327|I|`D5.S3.FiniteGroups.InducedCharacterFormula.Representation.char_eq_finrank_iff`|bind-only|none|323|none|
|328|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.stabilizer_quotientGroup_mk`|bind-only|none|397|none|
|329|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.doubleCosetMk_eq_mk_iff_mem`|bind-only|none|331|none|
|330|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.doubleCoset_one_eq_mul`|bind-only|none|331|none|
|331|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.doubleCosetMk_eq_mk_one_iff`|bind-only|none|332|none|
|332|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.doubleCosetMk_eq_mk_one_iff_mem`|bind-only|none|418,432|none|
|333|I|`D5.S3.FiniteGroups.InducedCharacterFormula.QuotientGroup.mk_out_smul`|bind-only|none|346|none|
|334|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm`|bind-only|none|375,376,339,342,346,344,341,335,336,338,337,343,347,367,366,413,412|none|
|335|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_apply`|bind-only|none|375,376,367,413,412|none|
|336|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_conj`|bind-only|none|346,366|none|
|337|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_one`|bind-only|none|366|none|
|338|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_eq_of_mk_eq_of_conj`|bind-only|none|345|none|
|339|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun`|bind-only|none|348,378,369,368,342,340,346,377,344,347,367,414,413|none|
|340|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun_apply`|bind-only|none|377,413|none|
|341|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_add`|bind-only|none|342|none|
|342|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun_add`|bind-only|none|348|none|
|343|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_smul`|bind-only|none|344|none|
|344|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun_smul`|bind-only|none|348|none|
|345|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indTerm_eq_of_mk_eq`|bind-only|none|376,346,347,413|none|
|346|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun_mem_classFunction`|bind-only|none|348|none|
|347|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.natCard_mul_indClassFun`|bind-only|none|367|none|
|348|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind`|bind-only|none|349,378,369,416,418,414,420|none|
|349|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind_apply`|bind-only|none|378,369,414|none|
|350|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.rightCosetFactor`|bind-only|none|355,356,357,360,352,353,354,374,375|none|
|351|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.rightCoset_mk_mul`|bind-only|none|355,356,352|none|
|352|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.rightCosetFactor_mul`|bind-only|none|355,356|none|
|353|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.rightCosetFactor_mul_out`|bind-only|none|355,356,357,375|none|
|354|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.rightCosetFactor_out`|bind-only|none|355,356|none|
|355|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.coindSubtypeEquivPi`|bind-only|none|356,357,358,359|none|
|356|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.coindSubtypeEquivPi_apply`|bind-only|none|357|none|
|357|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.coindSubtypeEquivPi_ρ_apply`|bind-only|none|360|none|
|358|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.indSubtypeEquivPi`|bind-only|none|361,362,359,360,374|none|
|359|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.indSubtypeEquivPi_apply`|bind-only|none|360|none|
|360|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.indSubtypeEquivPi_ρ_apply`|bind-only|none|374|none|
|361|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.finiteDimensional_ind`|bind-only|none|363,364|none|
|362|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.finrank_ind`|bind-only|none|365|none|
|363|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indFDRep`|bind-only|none|69,71,70,378,376,365,377,421,420,432,431,433,443|none|
|364|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indFDRepForgetEquiv`|bind-only|none|376,365|none|
|365|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.finrank_indFDRep`|bind-only|none|71|none|
|366|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.sum_indTerm_mul_eq_sum_subtype`|bind-only|none|367|none|
|367|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.natCard_mul_sum_indClassFun_mul`|bind-only|none|368|none|
|368|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.frobenius_reciprocity_classFunction`|bind-only|none|369|none|
|369|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.characterPairing_ind`|bind-only|none|416|none|
|370|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.doubleCosetMk_out_mk`|bind-only|none|371|none|
|371|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.finite_doubleCosetQuotient`|bind-only|none|416,418,414,421,413,420,431|none|
|372|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.quotientRightRelEquivQuotientLeftRel_mk`|bind-only|none|376|none|
|373|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.character_mem_classFunction`|bind-only|none|376|none|
|374|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.trace_ind_eq_sum_rightCosets`|bind-only|none|375|none|
|375|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.Rep.trace_ind_eq_sum_terms`|bind-only|none|376|none|
|376|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.character_indFDRep_sum_quotient`|bind-only|none|377|none|
|377|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.indClassFun_ofFDRep_character`|bind-only|none|378|none|
|378|I|`D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind_ofFDRep`|content|378|420|none|
|379|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup`|bind-only|none|427,398,416,418,417,415,394,391,390,396,387,406,414,421,424,422,413,412,399,407,408,409,410,411,400,401,402,428,430,429,403,404,393,389,395,386,392,380,384,388,385,405,381,420,419,431,397|none|
|380|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_def`|bind-only|none|392,384,388,381|none|
|381|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mem_mackeySubgroup_iff`|bind-only|none|412,400,403,397|none|
|382|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_le_right`|bind-only|none|396,406,395,405|none|
|383|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_le_conj`|bind-only|none|406,405|none|
|384|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_of_mem`|bind-only|none|385|none|
|385|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_subgroupOf_self_of_mem`|bind-only|none|386|none|
|386|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroupSelfEquiv`|bind-only|none|417,387|none|
|387|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.coe_mackeySubgroupSelfEquiv_apply`|bind-only|none|417|none|
|388|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_of_normal`|bind-only|none|390,389|none|
|389|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroupNormalEquiv`|bind-only|none|391,390,422|none|
|390|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.coe_mackeySubgroupNormalEquiv_apply`|bind-only|none|391,422|none|
|391|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.coe_mackeySubgroupNormalEquiv`|bind-only|none|422|none|
|392|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroup_conj`|bind-only|none|393|none|
|393|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroupCongr`|bind-only|none|394,396,395|none|
|394|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.coe_mackeySubgroupCongr_apply`|bind-only|none|396|none|
|395|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeySubgroupOfCongr`|bind-only|none|396,424|none|
|396|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.coe_mackeySubgroupOfCongr_apply`|bind-only|none|424|none|
|397|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.stabilizer_eq_mackeySubgroup_subgroupOf`|bind-only|none|398|none|
|398|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.card_orbit_eq_relIndex`|bind-only|none|399|none|
|399|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.instIsFiniteRelIndexMackeySubgroup`|bind-only|none|416,414,413|none|
|400|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyCoset`|bind-only|none|413,401,402,403|none|
|401|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyCoset_mk`|bind-only|none|402,403|none|
|402|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyCoset_out`|bind-only|none|413,403|none|
|403|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyQuotientEquiv`|bind-only|none|413,404|none|
|404|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyQuotientEquiv_apply`|bind-only|none|413|none|
|405|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyToH`|bind-only|none|427,417,415,406,421,424,422,412,407,409,428,430,429,420,419,431|none|
|406|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.coe_mackeyToH_apply`|bind-only|none|417,424,422,412|none|
|407|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFun`|bind-only|none|417,415,414,413,412,408,409,410,419|none|
|408|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFun_apply`|bind-only|none|417,415,412,409|none|
|409|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFun_mem_classFunction`|bind-only|none|410|none|
|410|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFunction`|bind-only|none|416,418,417,414,411,420,419|none|
|411|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyClassFunction_coe`|bind-only|none|417,414|none|
|412|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indTerm_mackeyClassFun`|bind-only|none|413|none|
|413|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.indClassFun_mackey`|bind-only|none|414|none|
|414|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.comap_subtype_ind_mackey`|bind-only|none|416|none|
|415|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.character_res_mackeyToH`|bind-only|none|419|none|
|416|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey`|bind-only|none|418|none|
|417|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_mackeyClassFunction_of_mem`|bind-only|none|418|none|
|418|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.characterPairing_ind_ind_mackey_erase`|bind-only|none|420|none|
|419|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.ofFDRep_res_mackeyToH`|bind-only|none|420|none|
|420|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.natCast_finrank_hom_indFDRep_mackey_erase`|content|378|421|none|
|421|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_indFDRep_mackey_erase`|content|378|431|none|
|422|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_res_mackeyToH_of_normal`|bind-only|none|430|none|
|423|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.res_ρ_comm_ρAut_hom`|bind-only|none|424|none|
|424|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right`|bind-only|none|429|none|
|425|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.isZero_of_finrank_end_eq_zero`|bind-only|none|431|none|
|426|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.finrank_hom_eq_zero_of_isZero`|bind-only|none|431|none|
|427|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.MackeyDisjoint`|bind-only|none|430,429,432,431,433|none|
|428|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyDisjoint_iff_finrank_eq_zero`|bind-only|none|430,429,431|none|
|429|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyDisjoint_mul_left_mul_right_iff`|bind-only|none|432|none|
|430|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.mackeyDisjoint_iff_isEmpty_iso_of_normal`|bind-only|none|433|none|
|431|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff_doubleCoset`|content|378|432|none|
|432|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff`|content|378|433|none|
|433|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_iff_of_normal`|content|378|443|none|
|434|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.Representation.linearCharacterRepresentation`|bind-only|none|436,435|none|
|435|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.Representation.isIrreducible_linearCharacterRepresentation`|bind-only|none|439|none|
|436|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.ofLinearCharacter`|bind-only|none|69,71,70,437,440,439,442,443|none|
|437|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.actionRes_obj_ofLinearCharacter`|bind-only|none|441|none|
|438|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.finrank_ofLinearCharacter`|bind-only|none|71|none|
|439|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.simple_ofLinearCharacter`|bind-only|none|443|none|
|440|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.FDRep.nonempty_iso_ofLinearCharacter_iff`|bind-only|none|442|none|
|441|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.conjNormalFDRep_ofLinearCharacter`|bind-only|none|442|none|
|442|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.nonempty_iso_conjNormalFDRep_ofLinearCharacter_iff`|bind-only|none|443|none|
|443|J|`D5.S3.FiniteGroups.MackeyCharacterFormula.TauCeti.simple_indFDRep_ofLinearCharacter_iff`|content|443|70|none|

## Triage

### What the settlement shows

- **Mechanism — proved, kernel-checked.** `FrobeniusCentralObstruction.central_eq_one_of_frobenius` proves that a Frobenius complement forces every central element to be the identity. The direct $C_2$ factor supplies a nontrivial central element; `BCP31.refutation_of_peak` applies this obstruction to the constructed group.
- **Peakness — proved, kernel-checked.** `ComplexCharacterAbelianProducts.degreesProdAbelian` preserves the simple degree set under a finite abelian direct product. `BCP31.degree120_mem` gives the degree-$120$ member, `BCP31.B_degree_dvd` gives divisibility of all simple degrees, and `BCP31.B_peak` proves peakness of $B$; `BCP31.result` transfers peakness to the constructed direct product.
- **Nonsolvability — proved, kernel-checked.** `BCP31.SL2F5_not_solvable` and `BCP31.semidirect_C2_not_solvable` use the $\mathrm{SL}(2,5)$ quotient to prove that the constructed group is not solvable.
- **Nearest surviving statement — proved, kernel-checked.** For any group $B$ and finite abelian group $A$, the delivered theorem `ComplexCharacterAbelianProducts.degreesProdAbelian` states equality of the simple degree sets of $B \times A$ and $B$.
- **Source dependence — open.** The cited source section ends with Conjecture 31. The literature reading does not establish which results elsewhere depend on it; this settlement makes no claim about those dependencies.
- **Follow-up: trivial centre — open.** Whether an analogue of Conjecture 31 holds for peak groups with trivial centre is outside `result`.
- **Follow-up: direct indecomposability — open.** Whether an analogue holds for directly indecomposable peak groups is outside `result`.
- **Experiment — open.** The supplied preregistration does not name an experiment repository, commit, script hash, or exit code. No experiment citation is asserted.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The experiment citation requested by the lane is absent from the supplied issue material, so no experiment result is used as evidence. The two follow-up questions are recorded as open repository follow-ups rather than as separately verified published open problems.
