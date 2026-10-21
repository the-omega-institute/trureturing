# Actual three-node FiniteSpectrum

## Abstract

Actual three-node FiniteSpectrum

Set tau=U/3+C/6, d=(U/3)(C/6)-(T/sqrt(18))^2 and Delta=(U/3-C/6)^2+4(T/sqrt(18))^2. Delta>=0, rhoPlus=(tau+sqrt(Delta))/2 and rhoMinus=(tau-sqrt(Delta))/2 satisfy rhoMinus<=rhoPlus, sum=tau and product=d.

Direct expansion of the actual finite matrix characteristic determinant yields (X-O)(X^2-tau X+d), then (X-rhoPlus)(X-O)(X-rhoMinus). The complex root multiset and the real eigenvalue multiset each have three entries with multiplicity, including coincident roots.

Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ identifies the complete descending list. Whenever rhoMinus<=O, its entries are [max(rhoPlus,O),min(rhoPlus,O),rhoMinus]. The top roots may tie.

For a=0, h>0, r!=0 and r^2<=1, evaluating the even characteristic quadratic at O gives -8h^2 r^2(5-r^2)(3-r^2)/15<0. The product identity then proves 0<rhoMinus<O<rhoPlus throughout this exterior range.

**Definition 1.1 (evenTau).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenTau`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenTau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def evenTau (g mu a r : ℝ) : ℝ := U g mu a r / 3 + ActualThreeNodeFiniteAlgebra.C g mu a r / 6

**Definition 1.2 (evenRad).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def evenRad (g mu a r : ℝ) : ℝ :=   (U g mu a r / 3 - ActualThreeNodeFiniteAlgebra.C g mu a r / 6) ^ 2 +     4 * (T g mu a r / Real.sqrt 18) ^ 2

**Definition 1.3 (rhoPlus).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoPlus`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoPlus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rhoPlus (g mu a r : ℝ) : ℝ :=   (evenTau g mu a r + Real.sqrt (evenRad g mu a r)) / 2

**Definition 1.4 (rhoMinus).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoMinus`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

def rhoMinus (g mu a r : ℝ) : ℝ :=   (evenTau g mu a r - Real.sqrt (evenRad g mu a r)) / 2

**Theorem 1.5 (evenRad nonneg).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma evenRad_nonneg (g mu a r : ℝ) : 0 ≤ evenRad g mu a r

**Theorem 1.6 (rho order).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_order`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rho_order (g mu a r : ℝ) : rhoMinus g mu a r ≤ rhoPlus g mu a r

**Theorem 1.7 (rho sum).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rho_sum (g mu a r : ℝ) :     rhoMinus g mu a r + rhoPlus g mu a r = evenTau g mu a r

**Theorem 1.8 (evenRad trace det).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad_trace_det`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad_trace_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma evenRad_trace_det (g mu a r : ℝ) :     evenRad g mu a r = evenTau g mu a r ^ 2 - 4 * evenDet g mu a r

**Theorem 1.9 (rho product).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_product`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rho_product (g mu a r : ℝ) :     rhoMinus g mu a r * rhoPlus g mu a r = evenDet g mu a r

**Theorem 1.10 (rhoMinus eq div).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoMinus_eq_div`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoMinus_eq_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma rhoMinus_eq_div (g mu a r : ℝ) (hp : rhoPlus g mu a r ≠ 0) :     rhoMinus g mu a r = evenDet g mu a r / rhoPlus g mu a r

**Definition 1.11 (finiteEigen).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finiteEigen`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finiteEigen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev finiteEigen (g mu a r : ℝ) : Fin 3 → ℝ :=   (finiteMatrix_isHermitian g mu a r).eigenvalues₀

**Theorem 1.12 (finite charpoly quadratic).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_charpoly_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_charpoly_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finite_charpoly_quadratic (g mu a r : ℝ) :     (finiteMatrix g mu a r).charpoly =       (X - Polynomial.C (O g mu a r : ℂ)) *         (X ^ 2 - Polynomial.C (evenTau g mu a r : ℂ) * X +           Polynomial.C (evenDet g mu a r : ℂ))

**Theorem 1.13 (finite charpoly).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma finite_charpoly (g mu a r : ℝ) :     (finiteMatrix g mu a r).charpoly =       (X - Polynomial.C (rhoPlus g mu a r : ℂ)) *       (X - Polynomial.C (O g mu a r : ℂ)) *       (X - Polynomial.C (rhoMinus g mu a r : ℂ))

**Theorem 1.14 (finite roots).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_roots`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem finite_roots (g mu a r : ℝ) :     (finiteMatrix g mu a r).charpoly.roots =       {(rhoPlus g mu a r : ℂ), (O g mu a r : ℂ), (rhoMinus g mu a r : ℂ)}

**Theorem 1.15 (finite spectrum multiset).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_spectrum_multiset`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_spectrum_multiset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem finite_spectrum_multiset (g mu a r : ℝ) :     (List.ofFn (finiteEigen g mu a r) : Multiset ℝ) =       {rhoPlus g mu a r, O g mu a r, rhoMinus g mu a r}

**Theorem 1.16 (finite sorted eq).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_sorted_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_sorted_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem finite_sorted_eq (g mu a r : ℝ) (hmo : rhoMinus g mu a r ≤ O g mu a r) :     finiteEigen g mu a r =       ![max (rhoPlus g mu a r) (O g mu a r),         min (rhoPlus g mu a r) (O g mu a r), rhoMinus g mu a r]

**Theorem 1.17 (exceptional characteristic at odd).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_characteristic_at_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_characteristic_at_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma exceptional_characteristic_at_odd (g mu r : ℝ) :     O g mu 0 r ^ 2 - evenTau g mu 0 r * O g mu 0 r + evenDet g mu 0 r =       -8 * (g ^ 2 + mu) ^ 2 * r ^ 2 * (5 - r ^ 2) * (3 - r ^ 2) / 15

**Theorem 1.18 (exceptional finite order).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_finite_order`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_finite_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem exceptional_finite_order (g mu r : ℝ) (hh : 0 < g ^ 2 + mu)     (hr : r ≠ 0) (hrsq : r ^ 2 ≤ 1) :     0 < rhoMinus g mu 0 r ∧ rhoMinus g mu 0 r < O g mu 0 r ∧       O g mu 0 r < rhoPlus g mu 0 r

**Theorem 1.19 (exceptional finite sorted).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_finite_sorted`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_finite_sorted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem exceptional_finite_sorted (g mu r : ℝ) (hh : 0 < g ^ 2 + mu)     (hr : r ≠ 0) (hrsq : r ^ 2 ≤ 1) :     finiteEigen g mu 0 r = ![rhoPlus g mu 0 r, O g mu 0 r, rhoMinus g mu 0 r]

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad_nonneg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenRad_trace_det`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.evenTau`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_characteristic_at_odd`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_finite_order`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.exceptional_finite_sorted`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finiteEigen`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_charpoly`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_charpoly_quadratic`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_roots`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_sorted_eq`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.finite_spectrum_multiset`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoMinus`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoMinus_eq_div`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rhoPlus`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_order`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_product`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteSpectrum.rho_sum`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteEnergy](ActualThreeNodeFiniteEnergy.md)
