/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuTransitionSpan
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuTransitionSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full literal quotient spanned by all tied-minimum source transitions. -/
import D5.S3.VertexAlgebra.Lattice.ActualZhuSourceProjectors

/-! Source spanning before applying any bottom representation.
Dong--Li--Mason, DOI 10.1006/jabr.1997.7112, Theorem 3.4 and Remark 2.11. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuTransitionSpan
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeDualCosetEnergy
open LatticeDiscriminantTheta
open ActualZhuFinite ActualZhuAlgebra ActualZhuCurrentNormalForm
open ActualZhuCurrentRelations ActualZhuSourceSupport ActualZhuMinimum ActualZhuSourceProjectors
open scoped BigOperators IsMulCommutative
noncomputable section
variable (D : LatticeData) [hD : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]
local instance : Ring (Q D) := quotientRing D hD.out
local instance : Algebra ℂ (Q D) := quotientAlgebra D hD.out
local instance : IsMulCommutative (currentAlgebra D) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact currents_commute D i j)

omit hD in
theorem gridWeight_injective : Function.Injective (gridWeight D) := by
  intro r s he
  funext i
  apply Fin.ext
  have hi := congrFun he i
  dsimp [gridWeight, node] at hi
  omega

def gridOfWeight (r : Charge D) (hr : AllAlpha D r) : Grid D := fun i =>
  ⟨(r i + (cutoff D i : ℤ)).toNat, by
    have hi := survivor_grid D r hr i
    have hk : (cutoff D i : ℤ) = chargeEnergy D (unitCharge D i) :=
      Int.toNat_of_nonneg (chargeEnergy_nonneg D hD.out _)
    omega⟩

theorem gridOfWeight_spec (r : Charge D) (hr : AllAlpha D r) :
    gridWeight D (gridOfWeight D r hr) = r := by
  funext i
  have hi := survivor_grid D r hr i
  have hk : (cutoff D i : ℤ) = chargeEnergy D (unitCharge D i) :=
    Int.toNat_of_nonneg (chargeEnergy_nonneg D hD.out _)
  dsimp [gridWeight, gridOfWeight, node]
  omega

def minimumWeight (c : Discriminant D) (γ : Min_c D hD.out c) : Charge D :=
  representative D c + gramMap D γ.val

theorem minimumWeight_allAlpha (c : Discriminant D) (γ : Min_c D hD.out c) :
    AllAlpha D (minimumWeight D c γ) :=
  (minimum_iff_allAlpha D _ _ (dualVector_hDual D hD.out _) γ.val).mp
    ((minimum_eq_iff D _ hD.out γ.val).mp γ.property)

def minimumGrid (c : Discriminant D) (γ : Min_c D hD.out c) : Grid D :=
  gridOfWeight D (minimumWeight D c γ) (minimumWeight_allAlpha D c γ)

theorem minimumGrid_spec (c : Discriminant D) (γ : Min_c D hD.out c) :
    gridWeight D (minimumGrid D c γ) = minimumWeight D c γ :=
  gridOfWeight_spec D _ _

/-- The first minimum is the output; the second is the input. -/
def sourceTransition (t : Transition D hD.out) : Q D :=
  E D (t.2.1.val - t.2.2.val) * (projector D (minimumGrid D t.1 t.2.2) : Q D)

private theorem support_scalar (δ : Charge D) (r : Grid D) :
    (((∑ i, δ i * gridWeight D r i) + chargeEnergy D δ : ℤ) : ℂ) •
      (E D δ * (projector D r : Q D)) = 0 := by
  have he := congrArg (fun x : Q D => x * (projector D r : Q D))
    (ground_right_support D δ)
  have hc := congrArg Subtype.val (charged_eigen D r δ)
  simp only [Subalgebra.coe_mul, Subalgebra.coe_smul, chargedCurrent_coe] at hc
  have hk : ((chargeEnergy D δ).toNat : ℤ) = chargeEnergy D δ :=
    Int.toNat_of_nonneg (chargeEnergy_nonneg D hD.out δ)
  rw [zero_mul, mul_assoc, add_mul, hc] at he
  have hn : ((chargeEnergy D δ).toNat : Q D) * (projector D r : Q D) =
      ((chargeEnergy D δ).toNat : ℂ) • (projector D r : Q D) := by
    rw [Algebra.smul_def, map_natCast]
  rw [hn, ← add_smul, mul_smul_comm] at he
  have hkC : ((chargeEnergy D δ).toNat : ℂ) = (chargeEnergy D δ : ℂ) := by
    exact_mod_cast hk
  simpa only [Int.cast_add, hkC] using he

private theorem transition_mem (δ : Charge D) (r : Grid D) :
    E D δ * (projector D r : Q D) ∈
      Submodule.span ℂ (Set.range (sourceTransition D)) := by
  classical
  by_cases hz : projector D r = 0
  · simp [hz]
  obtain ⟨c,γ,hγ⟩ := survivor_minimum D hD.out _ (projector_survives D r hz)
  have hg : r = minimumGrid D c γ := gridWeight_injective D
    (hγ.trans (minimumGrid_spec D c γ).symm)
  by_cases hs : (∑ i, δ i * gridWeight D r i) + chargeEnergy D δ = 0
  · have ho : chargeWeight D (dualVector D (representative D c)) (γ.val + δ) =
        chargeWeight D (dualVector D (representative D c))
          (minimizingCharge D (dualVector D (representative D c)) hD.out) :=
      (minimum_transition D _ _ (dualVector_hDual D hD.out _) hD.out γ δ).mp
        (by simpa only [hγ] using hs)
    let γout : Min_c D hD.out c := ⟨γ.val + δ, ho⟩
    have hd : γout.val - γ.val = δ := by dsimp [γout]; abel
    have ht : E D δ * (projector D r : Q D) = sourceTransition D ⟨c,γout,γ⟩ := by
      simp only [sourceTransition, hd, hg]
    rw [ht]
    exact Submodule.subset_span (Set.mem_range_self _)
  · have hc : (((∑ i, δ i * gridWeight D r i) + chargeEnergy D δ : ℤ) : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr hs
    have hz' := (smul_eq_zero.mp (support_scalar D δ r)).resolve_left hc
    rw [hz']
    exact Submodule.zero_mem _

private theorem ground_current_mem (δ : Charge D) (a : currentAlgebra D) :
    E D δ * (a : Q D) ∈ Submodule.span ℂ (Set.range (sourceTransition D)) := by
  classical
  have hs : (∑ r : Grid D, (projector D r : Q D)) = 1 := by
    exact_mod_cast projector_sum D
  have he : E D δ * (a : Q D) = ∑ r : Grid D,
      E D δ * ((a : Q D) * (projector D r : Q D)) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hs, mul_one]
  rw [he]
  apply Submodule.sum_mem
  intro r _
  obtain ⟨c,hc⟩ := current_scalar D r a
  rw [hc, mul_smul_comm]
  exact Submodule.smul_mem _ _ (transition_mem D δ r)

/-- Every original full quotient class is a finite linear combination of native
minimum-to-minimum transitions, including every tied minimum in every dual class. -/
theorem source_transition_span :
    Submodule.span ℂ (Set.range (sourceTransition D)) = ⊤ := by
  classical
  apply top_unique
  intro q _
  obtain ⟨v,rfl⟩ := (zhuO D).mkQ_surjective q
  have hv : v = ∑ δ ∈ v.support, Finsupp.single δ (v δ) :=
    (Finsupp.sum_single v).symm
  rw [hv, map_sum]
  apply Submodule.sum_mem
  intro δ _
  rw [oscillator_normal_form D]
  exact ground_current_mem D δ _

#print axioms source_transition_span
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuTransitionSpan
