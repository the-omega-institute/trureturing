/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuMinimum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native all-alpha weights and full tied-minimum discriminant fibers. -/
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
import D5.S3.VertexAlgebra.Sectors.LatticeDualCosetSpectrum
import Batteries.Tactic.OpenPrivate

/-! The lattice dictionary used by the literal source transition span.
Dong--Li--Mason, DOI 10.1006/jabr.1997.7112, Theorem 3.4, Remark 2.11.
The inverse Gram map, attained minima and their finite fibers are native suppliers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuMinimum
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeDualCosetEnergy
open LatticeDiscriminantTheta
open private rat_unit from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta
open Matrix
open scoped BigOperators
noncomputable section
variable (D : LatticeData)

theorem dualVector_hDual (hD : (gramReal D).PosDef) (r : Charge D) :
    ∀ i, ∑ j, (D.G i j : ℚ) * dualVector D r j = (r i : ℚ) := by
  intro i
  change (gramRat D *ᵥ dualVector D r) i = (r i : ℚ)
  rw [dualVector, inverseRat, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (rat_unit D hD), Matrix.one_mulVec]

def AllAlpha (r : Charge D) : Prop :=
  ∀ α : Charge D, -chargeEnergy D α ≤ ∑ i, α i * r i ∧
    (∑ i, α i * r i) ≤ chargeEnergy D α

theorem survivor_grid (r : Charge D) (hr : AllAlpha D r) (i : Fin D.rank) :
    -chargeEnergy D (unitCharge D i) ≤ r i ∧
      r i ≤ chargeEnergy D (unitCharge D i) := by
  simpa [unitCharge] using hr (unitCharge D i)

theorem translated_difference (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ)) (γ α : Charge D) :
    chargeWeight D μ (γ + α) - chargeWeight D μ γ =
      (chargeEnergy D α : ℚ) +
        ((∑ i, α i * (β + gramMap D γ) i : ℤ) : ℚ) := by
  let ν : Fin D.rank → ℚ := fun i => μ i + (γ i : ℚ)
  have hg (i : Fin D.rank) : ((gramMap D γ) i : ℚ) =
      ∑ j, (D.G i j : ℚ) * (γ j : ℚ) :=
    (Int.castRingHom ℚ).map_mulVec D.G γ i
  have hd : ∀ i, ∑ j, (D.G i j : ℚ) * ν j = ((β + gramMap D γ) i : ℚ) := by
    intro i
    simp only [ν, mul_add, Finset.sum_add_distrib, hDual,
      Pi.add_apply, Int.cast_add, hg]
  have hv (a : Charge D) : (fun i => (a i : ℚ) + ν i) =
      (fun i => ((γ + a) i : ℚ) + μ i) := by
    funext i
    simp [ν, add_assoc, add_comm]
  have hw (a : Charge D) : chargeWeight D ν a = chargeWeight D μ (γ + a) := by
    simp only [chargeWeight, hv]
  have he := chargeWeight_expansion D (β + gramMap D γ) ν hd α
  simp only [hw, add_zero] at he
  linarith

theorem minimum_iff_allAlpha (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ)) (γ : Charge D) :
    (∀ ν, chargeWeight D μ γ ≤ chargeWeight D μ ν) ↔
      AllAlpha D (β + gramMap D γ) := by
  let r := β + gramMap D γ
  constructor
  · intro hm α
    have hp := translated_difference D β μ hDual γ α
    have hn := translated_difference D β μ hDual γ (-α)
    have mp := hm (γ + α)
    have mn := hm (γ + (-α))
    have en : chargeEnergy D (-α) = chargeEnergy D α := by
      simp [chargeEnergy, bilinear]
    have sn : (∑ i, (-α) i * r i : ℤ) = -(∑ i, α i * r i : ℤ) := by
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    change chargeWeight D μ (γ + -α) - chargeWeight D μ γ =
      (chargeEnergy D (-α) : ℚ) + ((∑ i, (-α) i * r i : ℤ) : ℚ) at hn
    rw [en, sn, Int.cast_neg] at hn
    constructor
    · exact_mod_cast (show -(chargeEnergy D α : ℚ) ≤
        ((∑ i, α i * r i : ℤ) : ℚ) by linarith)
    · exact_mod_cast (show ((∑ i, α i * r i : ℤ) : ℚ) ≤
        (chargeEnergy D α : ℚ) by linarith)
  · intro hr ν
    have hl := (hr (ν - γ)).1
    have hd := translated_difference D β μ hDual γ (ν - γ)
    have ha : γ + (ν - γ) = ν := by abel
    rw [ha] at hd
    have hq : -(chargeEnergy D (ν - γ) : ℚ) ≤
        ((∑ i, (ν - γ) i * r i : ℤ) : ℚ) := by exact_mod_cast hl
    linarith

theorem translated_support_iff (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ)) (γ δ : Charge D) :
    (∑ i, δ i * (β + gramMap D γ) i) + chargeEnergy D δ = 0 ↔
      chargeWeight D μ (γ + δ) = chargeWeight D μ γ := by
  have hd := translated_difference D β μ hDual γ δ
  constructor
  · intro h
    have hq : ((∑ i, δ i * (β + gramMap D γ) i : ℤ) : ℚ) +
        (chargeEnergy D δ : ℚ) = 0 := by exact_mod_cast h
    linarith
  · intro h
    have hq : ((∑ i, δ i * (β + gramMap D γ) i : ℤ) : ℚ) +
        (chargeEnergy D δ : ℚ) = 0 := by linarith
    exact_mod_cast hq

def MinCharge (μ : Fin D.rank → ℚ) (hD : (gramReal D).PosDef) : Type :=
  {γ : Charge D // chargeWeight D μ γ =
    chargeWeight D μ (minimizingCharge D μ hD)}

instance minChargeFinite (μ : Fin D.rank → ℚ) (hD : (gramReal D).PosDef) :
    Finite (MinCharge D μ hD) := by
  have hf : Set.Finite {γ : Charge D | chargeWeight D μ γ =
      chargeWeight D μ (minimizingCharge D μ hD)} :=
    (charge_sublevel_finite D μ hD _).subset (fun _ h => h.le)
  exact hf.to_subtype

theorem minimum_eq_iff (μ : Fin D.rank → ℚ) (hD : (gramReal D).PosDef) (γ : Charge D) :
    chargeWeight D μ γ = chargeWeight D μ (minimizingCharge D μ hD) ↔
      ∀ ν, chargeWeight D μ γ ≤ chargeWeight D μ ν := by
  have hm := (Classical.choose_spec (attained_minimum D μ hD)).2
  constructor
  · intro h ν
    rw [h]
    exact hm ν
  · intro h
    exact le_antisymm (h _) (hm γ)

theorem minimum_transition (β : Charge D) (μ : Fin D.rank → ℚ)
    (hDual : ∀ i, ∑ j, (D.G i j : ℚ) * μ j = (β i : ℚ))
    (hD : (gramReal D).PosDef) (γ : MinCharge D μ hD) (δ : Charge D) :
    (∑ i, δ i * (β + gramMap D γ.val) i) + chargeEnergy D δ = 0 ↔
      chargeWeight D μ (γ.val + δ) =
        chargeWeight D μ (minimizingCharge D μ hD) := by
  rw [translated_support_iff D β μ hDual γ.val δ, γ.property]

abbrev Min_c (hD : (gramReal D).PosDef) (c : Discriminant D) :=
  MinCharge D (dualVector D (representative D c)) hD

theorem survivor_minimum (hD : (gramReal D).PosDef) (r : Charge D)
    (hr : AllAlpha D r) :
    ∃ (c : Discriminant D) (γ : Min_c D hD c),
      r = representative D c + gramMap D γ.val := by
  let e := cosetEquiv D hD
  let p := e.symm r
  have he : representative D p.1 + gramMap D p.2 = r := e.apply_symm_apply r
  have hm := (minimum_iff_allAlpha D (representative D p.1) _
    (dualVector_hDual D hD _) p.2).mpr (he.symm ▸ hr)
  exact ⟨p.1, ⟨p.2, (minimum_eq_iff D _ hD p.2).mpr hm⟩, he.symm⟩

abbrev Transition (hD : (gramReal D).PosDef) :=
  Σ c : Discriminant D, Min_c D hD c × Min_c D hD c

instance transitionFinite (hD : (gramReal D).PosDef) : Finite (Transition D hD) := by
  let : Fact (gramReal D).PosDef := ⟨hD⟩
  infer_instance

#print axioms minimum_iff_allAlpha
#print axioms survivor_minimum
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuMinimum
