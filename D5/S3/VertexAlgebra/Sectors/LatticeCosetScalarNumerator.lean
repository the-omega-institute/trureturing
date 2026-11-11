/- GID: D5/S3/VertexAlgebra/Sectors/LatticeCosetScalarNumerator
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeCosetScalarNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite scalar polynomials for the literal compressed H and Psi under restricted-dual tests. -/
/- Delivery scope and attribution: the supplied native import-to-EOF proof
source is preserved exactly. Source export SHA256 c0c34a65cb7326468d552cd9c16d490e8973c4690a01d46ee49de010a4351767.
proof_shape: content for actual_compressed_mode_grade and actual_scalar_numerator;
all private normalization/decomposition helpers are consumed on their live paths.
admission_basis: escape-witness. Actual injection/projection oscillator support
and the unreduced Schur charge-energy shift give signed compressed grading;
finite homogeneous input decompositions and finite output-weight tests then
compute the exact binary H/Psi degree support and unique scalar polynomials.
The existing scalar extraction supplier is reused rather than reimplemented.
utility: none: these are general symbolic algebraic results over arbitrary
original states, ranks including zero, matrices B and symmetric-even C, and
signed modes/cutoffs; no bounded enumeration, checker, numerical reduction or
certified finite instance is delivered. Only the original Gram is positive.
The actual fields, projection, injection and half-diagonal cocycle are retained.
No ambient positivity, analytic sewing, category, string or AdS/CFT completion
is claimed. Imported suppliers retain their attribution; no literature-priority
claim is made. The Blueprint mirror is produced by make emit. No separate
experimental artifact is specified; mirror-E uses the canonical route's
formal-manifest representation, not an escape-audit exemption.
The bounded typed source-family audit is incomplete: rejected interventions,
readout sensitivity, observational dependence and exact raw occurrence binding
remain unproved. Failed Reg attempts are excluded from retained targets.
Details: https://github.com/the-omega-institute/trureturing/issues/29386.
No Contract registration or declared_validated status is claimed. -/

import D5.S3.VertexAlgebra.Energy.LatticeCosetCompressedEnergy
import D5.S3.VertexAlgebra.Sectors.LatticeCosetWeakAssociativity
import D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator
import Mathlib.Data.Rat.Floor
import Batteries.Tactic.OpenPrivate

/-!
H is EXACTLY LatticeCosetWeakAssociativity.numerator; Psi is EXACTLY its
sharedNumerator. Polynomiality uses their definitions and actual compressed
energy grading. No Borcherds identity, recovery identity, truncation witness,
or homogeneous/finite-support premise on H occurs in the theorem telescope.
R,M,N may be arbitrary integers; their later choice as actual cutoffs is a
separate identification problem, not a condition for this polynomiality.

The test hypothesis is finite WEIGHT support on the original rational grades.
It allows any linear functional within each supported weight space. This is
the algebraic restricted dual, not the unrestricted algebraic dual. Creation
exponentials rule out that stronger, false formulation.

Proof route: actual JP grade; actual finite H grade; actual finite homogeneous
input decompositions; finite output-weight support; degree-preserving finite
shear; DIRECT use of word_polynomial_of_degree_support from its existing owner.
No scalar polynomial extraction is reimplemented here. All ranks, oscillator
states, external charges, B and symmetric-even C retain their original scope.

This is an algebraic construction. It makes no analytic continuation,
occupation-entry identification, ground-propagator, fusion/F, BPZ, pentagon,
string or AdS-CFT completion claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCosetScalarNumerator

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeCosetCompression LatticeDualCosetEnergy LatticeCosetCompressedEnergy
open LatticeCosetWeakAssociativity
open LatticeDiscriminantTheta (gramReal)
open scoped BigOperators VertexOperator

noncomputable section

open private coefficientProjection projection_mem projection_sum from
  D5.S3.VertexAlgebra.Sectors.LatticeDualCosetGrading
open private word_polynomial_of_degree_support from
  D5.S3.VertexAlgebra.Sectors.LatticeSectorScalarNumerator

variable (D : LatticeData) {e : ℕ}
variable (B : Matrix (Fin D.rank) (Fin e) ℤ)
variable (C : Matrix (Fin e) (Fin e) ℤ)
variable (hC : ∀ i j, C i j = C j i) (hCe : ∀ i, Even (C i i))

local notation "I" => compressed D B C hC hCe
local notation "S" => schur D B C
local notation "G[" a "]" => rationalGrade D (moduleShift D B a)
local notation "JP" => productCoefficient D B C hC hCe
local notation "H" => numerator D B C hC hCe
local notation "Psi" => sharedNumerator D B C hC hCe

private theorem schur_add_right (a b c : Fin e → ℤ) :
    S a (b+c) = S a b + S a c := by
  simp only [schur, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

private theorem product_grade (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D) (hu hv hw : ℚ)
    (hU : u ∈ G[a] hu) (hV : v ∈ G[b] hv) (hW : w ∈ G[c] hw)
    (m n : ℤ) :
    JP a b c u v w m n ∈ G[a+b+c]
      (hu+hv+hw-(m : ℚ)-(n : ℚ)-S a b-S a c-S b c-2) := by
  have inner := actual_compressed_mode_grade D B C hC hCe hD b c hv hw v w n hV hW
  have outer := actual_compressed_mode_grade D B C hC hCe hD a (b+c)
    hu (hv+hw-(n : ℚ)-1-S b c) u (I b c v n w) m hU inner
  have he : hu+(hv+hw-(n : ℚ)-1-S b c)-(m : ℚ)-1-S a (b+c) =
      hu+hv+hw-(m : ℚ)-(n : ℚ)-S a b-S a c-S b c-2 := by
    rw [schur_add_right]
    ring
  rw [he] at outer
  simpa only [productCoefficient, ← add_assoc] using outer

/-- Every summand of the literal H has the same total mode index, so H has
this grade without using charged Jacobi or any recovery equation. This
consumed helper retains the full vector-valued statement before testing. -/
private theorem numerator_grade (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D) (hu hv hw : ℚ)
    (hU : u ∈ G[a] hu) (hV : v ∈ G[b] hv) (hW : w ∈ G[c] hw)
    (R M N : ℤ) (d f : ℕ) :
    H a b c u v w R M N d f ∈ G[a+b+c]
      (hu+hv+hw-S a b-S a c-S b c-(N : ℚ)-(R : ℚ)-(M : ℚ)+(d : ℚ)+(f : ℚ)) := by
  classical
  unfold numerator
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have hg := product_grade D B C hC hCe hD a b c u v w hu hv hw hU hV hW
    (N+R-1-(d : ℤ)-(i : ℤ)) (M-1-(f : ℤ)+(i : ℤ))
  have he : hu+hv+hw-((N+R-1-(d : ℤ)-(i : ℤ) : ℤ) : ℚ)-
      ((M-1-(f : ℤ)+(i : ℤ) : ℤ) : ℚ)-S a b-S a c-S b c-2 =
      hu+hv+hw-S a b-S a c-S b c-(N : ℚ)-(R : ℚ)-(M : ℚ)+(d : ℚ)+(f : ℚ) := by
    push_cast
    ring
  rw [he] at hg
  exact hg

private theorem homogeneous_scalar_support (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D) (hu hv hw : ℚ)
    (hU : u ∈ G[a] hu) (hV : v ∈ G[b] hv) (hW : w ∈ G[c] hw)
    (φ : Module.Dual ℂ (Carrier D)) (F : Finset ℚ)
    (hφ : ∀ h x, x ∈ G[a+b+c] h → h ∉ F → φ x = 0)
    (R M N : ℤ) (d k : ℕ) (hne : φ (H a b c u v w R M N d k) ≠ 0) :
    ∃ hp ∈ F, (d : ℚ)+(k : ℚ) =
      (N : ℚ)+(R : ℚ)+(M : ℚ)+S a b+S a c+S b c+hp-hu-hv-hw := by
  let hp := hu+hv+hw-S a b-S a c-S b c-(N : ℚ)-(R : ℚ)-(M : ℚ)+(d : ℚ)+(k : ℚ)
  have hmem : hp ∈ F := by
    by_contra hn
    exact hne (hφ hp _ (numerator_grade D B C hC hCe hD a b c u v w
      hu hv hw hU hV hW R M N d k) hn)
  refine ⟨hp, hmem, ?_⟩
  dsimp only [hp]
  ring

private theorem compressed_sum_source {ι : Type*} (s : Finset ι)
    (f : ι → Carrier D) (a b : Fin e → ℤ) (m : ℤ) (v : Carrier D) :
    I a b (∑ i ∈ s, f i) m v = ∑ i ∈ s, I a b (f i) m v := by
  simp only [compressed, LinearMap.comp_apply, map_sum, Finset.sum_apply,
    LinearMap.sum_apply]

private theorem numerator_sum_left {ι : Type*} (s : Finset ι) (f : ι → Carrier D)
    (a b c : Fin e → ℤ) (v w : Carrier D) (R M N : ℤ) (d k : ℕ) :
    H a b c (∑ i ∈ s, f i) v w R M N d k =
      ∑ i ∈ s, H a b c (f i) v w R M N d k := by
  classical
  unfold numerator productCoefficient
  simp_rw [compressed_sum_source, Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem numerator_sum_middle {ι : Type*} (s : Finset ι) (f : ι → Carrier D)
    (a b c : Fin e → ℤ) (u w : Carrier D) (R M N : ℤ) (d k : ℕ) :
    H a b c u (∑ i ∈ s, f i) w R M N d k =
      ∑ i ∈ s, H a b c u (f i) w R M N d k := by
  classical
  unfold numerator productCoefficient
  simp_rw [compressed_sum_source, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem numerator_sum_right {ι : Type*} (s : Finset ι) (f : ι → Carrier D)
    (a b c : Fin e → ℤ) (u v : Carrier D) (R M N : ℤ) (d k : ℕ) :
    H a b c u v (∑ i ∈ s, f i) R M N d k =
      ∑ i ∈ s, H a b c u v (f i) R M N d k := by
  classical
  unfold numerator productCoefficient
  simp_rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

private def stateWeights (a : Fin e → ℤ) (u : Carrier D) : Finset ℚ :=
  (carrierCoeffEquiv D u).support.image (weight D (moduleShift D B a))

/-- The finite possible rational total degrees, computed from ACTUAL input
coefficient supports and the finite output-weight support of the test. -/
def scalarDegrees (a b c : Fin e → ℤ) (u v w : Carrier D)
    (F : Finset ℚ) (R M N : ℤ) : Finset ℚ :=
  (((stateWeights D B a u ×ˢ stateWeights D B b v) ×ˢ stateWeights D B c w) ×ˢ F).image
    (fun t => (N : ℚ)+(R : ℚ)+(M : ℚ)+S a b+S a c+S b c+
      t.2-t.1.1.1-t.1.1.2-t.1.2)

private theorem numerator_decomposition (a b c : Fin e → ℤ) (u v w : Carrier D)
    (R M N : ℤ) (d k : ℕ) :
    H a b c u v w R M N d k =
      ∑ hu ∈ stateWeights D B a u, ∑ hv ∈ stateWeights D B b v,
        ∑ hw ∈ stateWeights D B c w,
          H a b c
            (coefficientProjection D (weight D (moduleShift D B a)) hu u)
            (coefficientProjection D (weight D (moduleShift D B b)) hv v)
            (coefficientProjection D (weight D (moduleShift D B c)) hw w) R M N d k := by
  classical
  calc
    _ = H a b c
        (∑ hu ∈ stateWeights D B a u,
          coefficientProjection D (weight D (moduleShift D B a)) hu u)
        (∑ hv ∈ stateWeights D B b v,
          coefficientProjection D (weight D (moduleShift D B b)) hv v)
        (∑ hw ∈ stateWeights D B c w,
          coefficientProjection D (weight D (moduleShift D B c)) hw w) R M N d k := by
      dsimp only [stateWeights]
      rw [projection_sum, projection_sum, projection_sum]
    _ = _ := by simp_rw [numerator_sum_left, numerator_sum_middle, numerator_sum_right]

private theorem numerator_scalar_support (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D)
    (φ : Module.Dual ℂ (Carrier D)) (F : Finset ℚ)
    (hφ : ∀ h x, x ∈ G[a+b+c] h → h ∉ F → φ x = 0)
    (R M N : ℤ) (d k : ℕ)
    (hne : φ (H a b c u v w R M N d k) ≠ 0) :
    ((d : ℚ)+(k : ℚ)) ∈ scalarDegrees D B C a b c u v w F R M N := by
  classical
  by_contra outside
  apply hne
  rw [numerator_decomposition, map_sum]
  apply Finset.sum_eq_zero
  intro hu hhu
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro hv hhv
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro hw hhw
  by_contra hn
  obtain ⟨hp, hhp, he⟩ := homogeneous_scalar_support D B C hC hCe hD a b c _ _ _
    hu hv hw (projection_mem D _ hu u) (projection_mem D _ hv v)
    (projection_mem D _ hw w) φ F hφ R M N d k hn
  apply outside
  apply Finset.mem_image.mpr
  refine ⟨(((hu,hv),hw),hp), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hhu,hhv⟩,hhw⟩,hhp⟩
  · exact he.symm

private theorem shared_scalar_support (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D)
    (φ : Module.Dual ℂ (Carrier D)) (F : Finset ℚ)
    (hφ : ∀ h x, x ∈ G[a+b+c] h → h ∉ F → φ x = 0)
    (R M N : ℤ) (d k : ℕ)
    (hne : φ (Psi a b c u v w R M N d k) ≠ 0) :
    ((d : ℚ)+(k : ℚ)) ∈ scalarDegrees D B C a b c u v w F R M N := by
  classical
  by_contra outside
  apply hne
  unfold sharedNumerator coordinateChange
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  have jk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  have hz : φ (H a b c u v w R M N (d+j) (k-j)) = 0 := by
    by_contra hn
    have hs := numerator_scalar_support D B C hC hCe hD a b c u v w φ F hφ
      R M N (d+j) (k-j) hn
    have total : ((d+j : ℕ) : ℚ)+((k-j : ℕ) : ℚ) = (d : ℚ)+(k : ℚ) := by
      exact_mod_cast (show d+j+(k-j) = d+k by omega)
    rw [total] at hs
    exact outside hs
  rw [hz, smul_zero]

/-- The genuine finite scalar numerator theorem for the actual compressed
construction. hφ is finite weight support, not an assumption about H/Psi.
The two exact support statements retain the rational degree formula. The
polynomials are unique and are extracted using the existing theorem.

Here alpha=-S(a,b), beta=-S(a,c), gamma=-S(b,c), so scalarDegrees contains
N+R+M-(alpha+beta+gamma)+hp-hu-hv-hw for the actual input weight components.
No Jacobi, recovery or arbitrary scalar cutoff is a premise. -/
theorem actual_scalar_numerator (hD : (gramReal D).PosDef)
    (a b c : Fin e → ℤ) (u v w : Carrier D)
    (φ : Module.Dual ℂ (Carrier D)) (F : Finset ℚ)
    (hφ : ∀ h x, x ∈ G[a+b+c] h → h ∉ F → φ x = 0)
    (R M N : ℤ) :
    let T := scalarDegrees D B C a b c u v w F R M N
    let K : ℕ := T.sup (fun q => (⌈q⌉ : ℤ).toNat)
    let A : MvPowerSeries (Fin 2) ℂ := fun d => φ (H a b c u v w R M N (d 0) (d 1))
    let Q : MvPowerSeries (Fin 2) ℂ := fun d => φ (Psi a b c u v w R M N (d 0) (d 1))
    (∀ d k, φ (H a b c u v w R M N d k) ≠ 0 → (d : ℚ)+(k : ℚ) ∈ T) ∧
    (∀ d k, φ (Psi a b c u v w R M N d k) ≠ 0 → (d : ℚ)+(k : ℚ) ∈ T) ∧
    (∃! P : MvPolynomial (Fin 2) ℂ,
      (P : MvPowerSeries (Fin 2) ℂ) = A ∧ P.totalDegree ≤ K) ∧
    (∃! P : MvPolynomial (Fin 2) ℂ,
      (P : MvPowerSeries (Fin 2) ℂ) = Q ∧ P.totalDegree ≤ K) := by
  classical
  dsimp only
  let T := scalarDegrees D B C a b c u v w F R M N
  let K : ℕ := T.sup (fun q => (⌈q⌉ : ℤ).toNat)
  let A : MvPowerSeries (Fin 2) ℂ := fun d => φ (H a b c u v w R M N (d 0) (d 1))
  let Q : MvPowerSeries (Fin 2) ℂ := fun d => φ (Psi a b c u v w R M N (d 0) (d 1))
  have hs := numerator_scalar_support D B C hC hCe hD a b c u v w φ F hφ R M N
  have ht := shared_scalar_support D B C hC hCe hD a b c u v w φ F hφ R M N
  have degree (d : Fin 2 →₀ ℕ) : d.degree = d 0+d 1 := by
    rw [Finsupp.degree_eq_sum]
    exact Fin.sum_univ_two _
  have bound (d k : ℕ) (hm : (d : ℚ)+(k : ℚ) ∈ T) : d+k ≤ K := by
    have hh := Finset.le_sup (f := fun q : ℚ => (⌈q⌉ : ℤ).toNat) hm
    have he : (d : ℚ)+(k : ℚ) = ((d+k : ℕ) : ℚ) := by push_cast; rfl
    rw [he] at hh
    simpa only [Int.ceil_natCast, Int.toNat_natCast] using hh
  have sa : ∀ d, MvPowerSeries.coeff d A ≠ 0 → (d.degree : ℤ) ≤ (K : ℤ) := by
    intro d hd
    rw [degree]
    exact_mod_cast bound (d 0) (d 1) (hs _ _ hd)
  have sq : ∀ d, MvPowerSeries.coeff d Q ≠ 0 → (d.degree : ℤ) ≤ (K : ℤ) := by
    intro d hd
    rw [degree]
    exact_mod_cast bound (d 0) (d 1) (ht _ _ hd)
  obtain ⟨PA, hPA, hDA, _⟩ := word_polynomial_of_degree_support A (K : ℤ) sa
  obtain ⟨PQ, hPQ, hDQ, _⟩ := word_polynomial_of_degree_support Q (K : ℤ) sq
  refine ⟨hs, ht, ⟨PA, ⟨hPA, ?_⟩, ?_⟩, ⟨PQ, ⟨hPQ, ?_⟩, ?_⟩⟩
  · simpa only [Int.toNat_natCast] using hDA
  · intro P hP
    exact MvPolynomial.coe_injective (Fin 2) ℂ (hP.1.trans hPA.symm)
  · simpa only [Int.toNat_natCast] using hDQ
  · intro P hP
    exact MvPolynomial.coe_injective (Fin 2) ℂ (hP.1.trans hPQ.symm)

end
end D5.S3.VertexAlgebra.LatticeCosetScalarNumerator
