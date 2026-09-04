/- GID: D5/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData
   mirror-E: none(waiver:canonical-zeta-zero-presentation)
   anchors: []
   digest: Assemble unconditional Gamma and Riemann-von Mangoldt sources into a parameter-free exhaustive ZeroData value. -/

import D5.S3.Weil.ZetaGamma.GammaFactsComplete
import D5.S3.Weil.ZetaRvm.Statement
import D5.S3.Weil.ZetaBridge.CanonicalZeroDataNonvacuityAssembly

/-!
# Unconditional canonical zeta `ZeroData`

This node removes the final analytic-source parameter from the canonical
`ZeroData` lane. It composes the proof-complete Gamma certificate with the
Riemann--von Mangoldt assembly, then instantiates the existing nonvacuity,
enumeration, multiplicity, symmetry, local-finiteness, and semantic-realization
chain.

The natural-number ordering is selected classically. The represented zero
set, analytic multiplicities, symmetric finite sums, and convergent zero sums
are independent of that presentation by the existing enumeration-invariance
results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataProvider
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataNonvacuityAssembly

/-- The proof-complete, hypothesis-free Riemann--von Mangoldt source for
Mathlib's Riemann zeta function. -/
theorem zetaRiemannVonMangoldt :
    Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig :=
  Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts

/-- The source consumed by the canonical presentation layer, with no external
field or theorem parameter. -/
noncomputable def zetaCanonicalZeroDataSource : CanonicalZeroDataSource where
  riemannVonMangoldt := zetaRiemannVonMangoldt

/-- A fixed, exhaustive, duplicate-free, multiplicity-aware presentation of
all nontrivial zeta zeros. Only its presentation order depends on classical
choice. -/
noncomputable def zetaZeroData : ZeroData :=
  canonicalZeroData zetaCanonicalZeroDataSource

/-- `ZeroData` is unconditionally inhabited. -/
theorem nonempty_zeroData : Nonempty ZeroData :=
  ⟨zetaZeroData⟩

/-- Every canonical entry is a genuine nontrivial zeta zero. -/
theorem zetaZeroData_isNontrivial (n : ℕ) :
    IsNontrivialZero (zetaZeroData.zero n) :=
  canonicalZeroData_isNontrivial zetaCanonicalZeroDataSource n

/-- Every genuine nontrivial zeta zero occurs at exactly one canonical index. -/
theorem zetaZeroData_exhaustiveUnique {rho : ℂ}
    (hrho : IsNontrivialZero rho) :
    ∃! n : ℕ, zetaZeroData.zero n = rho :=
  canonicalZeroData_exhaustiveUnique zetaCanonicalZeroDataSource hrho

/-- The stored multiplicities are the positive analytic zero orders. -/
theorem zetaZeroData_multiplicity_pos (n : ℕ) :
    0 < zetaZeroData.multiplicity n :=
  canonicalZeroData_multiplicity_pos zetaCanonicalZeroDataSource n

/-- Functional-equation reflection is realized as an index permutation. -/
theorem zetaZeroData_reflection (n : ℕ) :
    zetaZeroData.zero (zetaZeroData.reflection n) = 1 - zetaZeroData.zero n :=
  canonicalZeroData_reflection zetaCanonicalZeroDataSource n

/-- Reflection preserves analytic multiplicity. -/
theorem zetaZeroData_multiplicity_reflection (n : ℕ) :
    zetaZeroData.multiplicity (zetaZeroData.reflection n) =
      zetaZeroData.multiplicity n :=
  canonicalZeroData_multiplicity_reflection zetaCanonicalZeroDataSource n

/-- Complex conjugation is realized as an index permutation. -/
theorem zetaZeroData_conjugation (n : ℕ) :
    zetaZeroData.zero (zetaZeroData.conjugation n) = conj (zetaZeroData.zero n) :=
  canonicalZeroData_conjugation zetaCanonicalZeroDataSource n

/-- Conjugation preserves analytic multiplicity. -/
theorem zetaZeroData_multiplicity_conjugation (n : ℕ) :
    zetaZeroData.multiplicity (zetaZeroData.conjugation n) =
      zetaZeroData.multiplicity n :=
  canonicalZeroData_multiplicity_conjugation zetaCanonicalZeroDataSource n

/-- Every symmetric spectral-radius cutoff is finite. -/
theorem zetaZeroData_locallyFinite (T : ℝ) :
    {n : ℕ | spectralRadius (zetaZeroData.zero n) ≤ T}.Finite :=
  canonicalZeroData_locallyFinite zetaCanonicalZeroDataSource T

/-- The unconditional consumer-facing fidelity certificate. -/
noncomputable def zetaZeroDataCertificate : CanonicalZeroDataCertificate :=
  certificate zetaCanonicalZeroDataSource

/-- Exact soundness, completeness, and uniqueness of the canonical
presentation. -/
theorem zetaZeroData_representation_iff (rho : ℂ) :
    IsNontrivialZero rho ↔ ∃! n : ℕ, zetaZeroData.zero n = rho := by
  simpa [zetaZeroData, zetaZeroDataCertificate] using
    certificate_representation_iff zetaZeroDataCertificate rho

/-- A property holds on the canonical sequence exactly when it holds on every
actual nontrivial zeta zero. -/
theorem zetaZeroData_universal_iff_actual (P : ℂ → Prop) :
    (∀ n : ℕ, P (zetaZeroData.zero n)) ↔
      ∀ rho : ℂ, IsNontrivialZero rho → P rho := by
  constructor
  · intro h rho hrho
    obtain ⟨n, hn, _⟩ := zetaZeroData_exhaustiveUnique hrho
    rw [← hn]
    exact h n
  · intro h n
    exact h (zetaZeroData.zero n) (zetaZeroData_isNontrivial n)

/-- A universal canonical-sequence theorem is witnessed by at least one actual
nontrivial zeta zero. -/
theorem zetaZeroData_exists_of_forall
    (P : ℂ → Prop) (h : ∀ n : ℕ, P (zetaZeroData.zero n)) :
    ∃ rho : ℂ, IsNontrivialZero rho ∧ P rho :=
  ⟨zetaZeroData.zero 0, zetaZeroData_isNontrivial 0, h 0⟩

/-- Any theorem universally quantified over `ZeroData` is unconditionally
realized on the fixed zeta presentation. -/
theorem universal_claim_realized_on_zetaZeroData
    {P : ZeroData → Prop} (h : ∀ Z : ZeroData, P Z) :
    P zetaZeroData ∧ ∃ rho : ℂ, IsNontrivialZero rho :=
  ⟨h zetaZeroData,
    ⟨zetaZeroData.zero 0, zetaZeroData_isNontrivial 0⟩⟩

/-- The entire nonvacuity and fidelity chain, without an analytic input
parameter. -/
theorem zetaZeroData_closed_chain :
    {rho : ℂ | IsNontrivialZero rho}.Infinite ∧
      Nonempty ZeroData ∧
      ∃ C : CanonicalZeroDataCertificate, C.data = zetaZeroData := by
  refine ⟨nontrivial_zeta_zero_set_infinite_of_riemannVonMangoldt
      zetaRiemannVonMangoldt, nonempty_zeroData, ?_⟩
  exact ⟨zetaZeroDataCertificate, rfl⟩

#print axioms zetaRiemannVonMangoldt
#print axioms nonempty_zeroData
#print axioms zetaZeroData_isNontrivial
#print axioms zetaZeroData_exhaustiveUnique
#print axioms zetaZeroData_representation_iff
#print axioms zetaZeroData_universal_iff_actual
#print axioms zetaZeroData_closed_chain

end D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData
