/- GID: D5/S3/Weil/ZetaBridge/CanonicalZeroDataProvider
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/CanonicalZeroDataProvider
   mirror-E: none(waiver:canonical-provider-and-enumeration-invariance)
   anchors: []
   digest: Package the Riemann-von Mangoldt source into a canonical ZeroData provider and prove fidelity for all enumeration-invariant zero sums. -/

import D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt
import D5.S3.Weil.ZetaBridge.ZeroSumEnumerationInvariance

/-!
# Canonical `ZeroData` provider

A `ZeroData` enumeration is obtained by classical choice after proving that
the set of nontrivial zeta zeros is infinite.  The ordering itself is not
canonical.  Its mathematical use is canonical because the repository's
finite symmetric sums, convergence predicate, and zero-sum value are already
proved invariant under every duplicate-free exhaustive enumeration.

This module makes both layers explicit:

* `CanonicalZeroDataSource` records the analytic Riemann--von Mangoldt input;
* `canonicalZeroData` is the resulting actual exhaustive enumeration;
* `CanonicalZeroDataProvider` packages the source and the chosen value;
* the final theorems show that all permitted zero-sum consumers agree with
  every other `ZeroData` enumeration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.CanonicalZeroDataProvider

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt

/-- The precise analytic source needed by the present canonical provider. -/
structure CanonicalZeroDataSource : Prop where
  riemannVonMangoldt : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig

/-- The duplicate-free exhaustive zeta-zero enumeration selected from a
canonical Riemann--von Mangoldt source. -/
noncomputable def canonicalZeroData (S : CanonicalZeroDataSource) : ZeroData :=
  zeroDataOfRiemannVonMangoldt S.riemannVonMangoldt

/-- A provider records both the analytic source and the actual zero-data value
selected from it. -/
structure CanonicalZeroDataProvider where
  source : CanonicalZeroDataSource
  data : ZeroData
  data_eq : data = canonicalZeroData source

/-- Construct the provider from its analytic source. -/
noncomputable def provider (S : CanonicalZeroDataSource) :
    CanonicalZeroDataProvider where
  source := S
  data := canonicalZeroData S
  data_eq := rfl

/-- The provider's data is definitionally the canonical selected enumeration. -/
@[simp]
theorem provider_data (S : CanonicalZeroDataSource) :
    (provider S).data = canonicalZeroData S :=
  rfl

/-- A source yields a genuine inhabitant of `ZeroData`. -/
theorem canonicalZeroData_nonempty (S : CanonicalZeroDataSource) :
    Nonempty ZeroData :=
  ⟨canonicalZeroData S⟩

/-- Every entry of the canonical enumeration is a nontrivial zeta zero. -/
theorem canonicalZeroData_isNontrivial
    (S : CanonicalZeroDataSource) (n : ℕ) :
    IsNontrivialZero ((canonicalZeroData S).zero n) :=
  (canonicalZeroData S).zero_isNontrivial n

/-- Every nontrivial zeta zero occurs at exactly one canonical index. -/
theorem canonicalZeroData_exhaustiveUnique
    (S : CanonicalZeroDataSource) {rho : ℂ}
    (hrho : IsNontrivialZero rho) :
    ∃! n : ℕ, (canonicalZeroData S).zero n = rho :=
  (canonicalZeroData S).existsUnique_zero hrho

/-- Canonically stored analytic multiplicities are positive. -/
theorem canonicalZeroData_multiplicity_pos
    (S : CanonicalZeroDataSource) (n : ℕ) :
    0 < (canonicalZeroData S).multiplicity n :=
  (canonicalZeroData S).multiplicity_pos n

/-- The provider preserves the functional-equation reflection exactly. -/
theorem canonicalZeroData_reflection
    (S : CanonicalZeroDataSource) (n : ℕ) :
    (canonicalZeroData S).zero ((canonicalZeroData S).reflection n) =
      1 - (canonicalZeroData S).zero n :=
  (canonicalZeroData S).zero_reflection n

/-- Reflection preserves the stored analytic multiplicity. -/
theorem canonicalZeroData_multiplicity_reflection
    (S : CanonicalZeroDataSource) (n : ℕ) :
    (canonicalZeroData S).multiplicity ((canonicalZeroData S).reflection n) =
      (canonicalZeroData S).multiplicity n :=
  (canonicalZeroData S).multiplicity_reflection n

/-- The provider preserves complex conjugation exactly. -/
theorem canonicalZeroData_conjugation
    (S : CanonicalZeroDataSource) (n : ℕ) :
    (canonicalZeroData S).zero ((canonicalZeroData S).conjugation n) =
      conj ((canonicalZeroData S).zero n) :=
  (canonicalZeroData S).zero_conjugation n

/-- Conjugation preserves the stored analytic multiplicity. -/
theorem canonicalZeroData_multiplicity_conjugation
    (S : CanonicalZeroDataSource) (n : ℕ) :
    (canonicalZeroData S).multiplicity ((canonicalZeroData S).conjugation n) =
      (canonicalZeroData S).multiplicity n :=
  (canonicalZeroData S).multiplicity_conjugation n

/-- Every canonical symmetric spectral ball is finite. -/
theorem canonicalZeroData_locallyFinite
    (S : CanonicalZeroDataSource) (T : ℝ) :
    {n : ℕ | spectralRadius ((canonicalZeroData S).zero n) ≤ T}.Finite :=
  (canonicalZeroData S).locallyFinite T

/-- The canonical finite symmetric zero sum is identical to the same sum in
any other exhaustive duplicate-free enumeration. -/
theorem canonical_truncatedZeroSum_eq
    (S : CanonicalZeroDataSource) (Z : ZeroData)
    (g : WeilTestFunction) (T : ℝ) :
    truncatedZeroSum (canonicalZeroData S) g T = truncatedZeroSum Z g T :=
  truncatedZeroSum_enum_invariant (canonicalZeroData S) Z g T

/-- Symmetric convergence is independent of replacing the canonical
enumeration by any other `ZeroData` enumeration. -/
theorem canonical_symmetricConvergent_iff
    (S : CanonicalZeroDataSource) (Z : ZeroData)
    (g : WeilTestFunction) :
    SymmetricConvergent (canonicalZeroData S) g ↔ SymmetricConvergent Z g :=
  symmetricConvergent_enum_invariant (canonicalZeroData S) Z g

/-- Whenever both sides are supplied their convergence witnesses, the
canonical zero-sum value agrees with every other enumeration. -/
theorem canonical_zeroSum_eq
    (S : CanonicalZeroDataSource) (Z : ZeroData)
    (g : WeilTestFunction)
    (hCanonical : SymmetricConvergent (canonicalZeroData S) g)
    (hZ : SymmetricConvergent Z g) :
    zeroSum (canonicalZeroData S) g hCanonical = zeroSum Z g hZ :=
  zeroSum_enum_invariant (canonicalZeroData S) Z g hCanonical hZ

#print axioms canonicalZeroData_nonempty
#print axioms canonicalZeroData_isNontrivial
#print axioms canonicalZeroData_exhaustiveUnique
#print axioms canonicalZeroData_multiplicity_pos
#print axioms canonicalZeroData_reflection
#print axioms canonicalZeroData_conjugation
#print axioms canonicalZeroData_locallyFinite
#print axioms canonical_truncatedZeroSum_eq
#print axioms canonical_symmetricConvergent_iff
#print axioms canonical_zeroSum_eq

end D5.S3.Weil.ZetaBridge.CanonicalZeroDataProvider
