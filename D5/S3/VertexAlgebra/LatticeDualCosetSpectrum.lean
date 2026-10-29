/- GID: D5/S3/VertexAlgebra/LatticeDualCosetSpectrum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Algebraic point spectrum and bottom spaces of the actual original-omega dual-coset action. -/

import D5.S3.VertexAlgebra.LatticeDualCosetGrading
import D5.S3.VertexAlgebra.LatticeDualCosetVirasoroLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticeDualCosetEnergy
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticeDualCosetConformal
open LatticeActualConformalState LatticeDualCosetModule
open scoped BigOperators VertexOperator
noncomputable section

variable (D : LatticeData)

/-- Algebraic point spectrum only: every nonzero actual eigenvector has weight h+n. -/
theorem point_spectrum_subset (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i,∑ j,(D.G i j : ℚ)*μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (z : ℂ)
    (hv : ∃ v : Carrier D, v ≠ 0 ∧ moduleL D β H 0 v=z • v) :
    ∃ n : ℕ, z=((chargeWeight D μ (minimizingCharge D μ hD)+(n : ℚ)) : ℂ) := by
  classical
  obtain ⟨v,hv,he⟩ := hv
  have hc : carrierCoeffEquiv D v ≠ 0 := by
    intro h
    exact hv ((carrierCoeffEquiv D).injective (by simpa using h))
  obtain ⟨a,ha⟩ := Finsupp.ne_iff.mp hc
  have h := congrArg (fun w : Carrier D => carrierCoeffEquiv D w a) he
  rw [moduleL_coeff D β H hHG hGH μ hDual] at h
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul] at h
  have heq : (weight D μ a : ℂ)=z := mul_right_cancel₀ ha h
  obtain ⟨n,hn⟩ := weight_levels D β μ hDual (minimizingCharge D μ hD)
    (Classical.choose_spec (attained_minimum D μ hD)).2 a
  exact ⟨n,heq.symm.trans (congrArg (fun x : ℚ => (x : ℂ)) hn)⟩

/-- Positive rank realizes every natural level by a frequency-one oscillator. -/
theorem positive_rank_point_spectrum (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i,∑ j,(D.G i j : ℚ)*μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (hr : 0<D.rank) (z : ℂ) :
    (∃ v : Carrier D, v ≠ 0 ∧ moduleL D β H 0 v=z • v) ↔
      ∃ n : ℕ, z=((chargeWeight D μ (minimizingCharge D μ hD)+(n : ℚ)) : ℂ) := by
  constructor
  · exact point_spectrum_subset D β H hHG hGH μ hDual hD z
  · rintro ⟨n,rfl⟩
    let i : Fin D.rank := ⟨0,hr⟩
    let a : Label D := (minimizingCharge D μ hD,Finsupp.single (i,0) n)
    refine ⟨carrierBasis D a,(carrierBasis D).ne_zero a,?_⟩
    rw [moduleL_basis_zero D β H hHG hGH μ hDual]
    congr 1
    congr 1
    simp [a,weight,oscillatorEnergy,Finsupp.weight_single,add_comm]

/-- Rank zero has the single eigenvalue zero on the nonzero vacuum line. -/
theorem zero_rank_point_spectrum (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (hr : D.rank=0) (z : ℂ) :
    (∃ v : Carrier D, v ≠ 0 ∧ moduleL D β H 0 v=z • v) ↔ z=0 := by
  classical
  letI : IsEmpty (Fin D.rank) := ⟨fun i => by have hi := i.isLt; omega⟩
  have hz : moduleL D β H 0=0 := by simp [moduleL,omega,conformalPolynomial]
  rw [hz]
  constructor
  · rintro ⟨v,hv,he⟩
    exact (smul_eq_zero.mp (by simpa using he.symm)).resolve_right hv
  · rintro rfl
    let e := rankZeroVacuumEquiv D hr
    have hv : e 1 ≠ 0 := by
      intro h
      have hz : (1 : ℂ)=0 := e.injective (h.trans e.map_zero.symm)
      exact one_ne_zero hz
    exact ⟨e 1,hv,by simp⟩

/-- Bottom labels are exactly minimizing charges with no oscillators. -/
theorem bottom_fiber (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Label D) :
    weight D μ a=chargeWeight D μ (minimizingCharge D μ hD) ↔
      chargeWeight D μ a.1=chargeWeight D μ (minimizingCharge D μ hD) ∧ a.2=0 := by
  have hmin := (Classical.choose_spec (attained_minimum D μ hD)).2 a.1
  change chargeWeight D μ (minimizingCharge D μ hD) ≤ chargeWeight D μ a.1 at hmin
  have hn : (0 : ℚ) ≤ (oscillatorEnergy a.2 : ℚ) := Nat.cast_nonneg _
  constructor
  · intro h
    have ho : oscillatorEnergy a.2=0 := by
      have : (oscillatorEnergy a.2 : ℚ)=0 := by dsimp [weight] at h; linarith
      exact_mod_cast this
    refine ⟨?_,(oscillatorEnergy_eq_zero_iff D a.2).mp ho⟩
    dsimp [weight] at h
    simp only [ho,Nat.cast_zero,zero_add] at h
    exact h
  · rintro ⟨hq,hd⟩
    simp [weight,hd,hq,oscillatorEnergy]

/-- Genuine conformal modes map the actual energy e space to e-m. -/
theorem conformal_mode_grade (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i,∑ j,(D.G i j : ℚ)*μ j=(β i : ℚ))
    (m : ℤ) (e : ℚ) (v : Carrier D) (hv : v ∈ rationalGrade D μ e) :
    moduleL D β H m v ∈ rationalGrade D μ (e-(m : ℚ)) := by
  apply (moduleL_eigen_iff D β H hHG hGH μ hDual _ _).mp
  have he := (moduleL_eigen_iff D β H hHG hGH μ hDual e v).mpr hv
  have h := LinearMap.congr_fun (moduleL_virasoro D β H hHG hGH 0 m) v
  simp only [LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,
    LinearMap.smul_apply,he,map_smul,zero_add,zero_sub,Int.cast_neg,
    Int.cast_zero,zero_pow (by decide : 3 ≠ 0),sub_zero,mul_zero,ite_self,
    zero_smul,add_zero] at h
  push_cast
  linear_combination (norm := module) h

/-- Every positive conformal mode annihilates every vector of the full bottom space. -/
theorem positive_modes_kill_bottom (β : Charge D)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D=1) (hGH : gramComplex D * H=1)
    (μ : Fin D.rank → ℚ) (hDual : ∀ i,∑ j,(D.G i j : ℚ)*μ j=(β i : ℚ))
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m : ℤ) (hm : 0<m) (v : Carrier D)
    (hv : v ∈ rationalGrade D μ (chargeWeight D μ (minimizingCharge D μ hD))) :
    moduleL D β H m v=0 := by
  by_contra hn
  have he := conformal_mode_grade D β H hHG hGH μ hDual m _ v hv
  have heig := (moduleL_eigen_iff D β H hHG hGH μ hDual _ _).mpr he
  obtain ⟨n,hn⟩ := point_spectrum_subset D β H hHG hGH μ hDual hD _
    ⟨moduleL D β H m v,hn,heig⟩
  have hq : chargeWeight D μ (minimizingCharge D μ hD)-(m : ℚ) =
      chargeWeight D μ (minimizingCharge D μ hD)+(n : ℚ) := Rat.cast_injective hn
  have hmQ : (0 : ℚ)<(m : ℚ) := by exact_mod_cast hm
  have hnQ : (0 : ℚ)≤(n : ℚ) := Nat.cast_nonneg n
  linarith

/-- The constructed bottom energy is zero in rank zero. -/
theorem zero_rank_minimum (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (hr : D.rank=0) :
    chargeWeight D μ (minimizingCharge D μ hD)=0 := by
  have h := congrArg Prod.fst (rank_zero_label D hr (minimizingCharge D μ hD,0))
  change minimizingCharge D μ hD=0 at h
  rw [h]
  letI : IsEmpty (Fin D.rank) := ⟨fun i => by have hi := i.isLt; omega⟩
  simp [chargeWeight,pairing]

/-- The even rank-one lattice has a half-shifted bottom with two distinct charges. -/
def halfShiftLattice : LatticeData where
  rank := 1
  G := fun _ _ => 2
  symmetric := by intros; rfl
  even_diagonal := by intro i; exact ⟨1,by norm_num⟩

theorem half_shift_two_minima :
    let E := halfShiftLattice
    let μ : Fin E.rank → ℚ := fun _ => 1/2
    (∀ i,∑ j,(E.G i j : ℚ)*μ j=(1 : ℚ)) ∧
    ∃ γ δ : Charge E, γ ≠ δ ∧ chargeWeight E μ γ=1/4 ∧ chargeWeight E μ δ=1/4 ∧
      ∀ ν : Charge E, 1/4 ≤ chargeWeight E μ ν := by
  dsimp only
  have hformula (ν : Fin 1 → ℤ) :
      chargeWeight halfShiftLattice (fun _ => 1/2) ν = ((ν 0 : ℚ)+1/2)^2 := by
    change (∑ i : Fin 1, ∑ j : Fin 1,
      ((ν i : ℚ)+1/2)*2*((ν j : ℚ)+1/2))/2 = _
    simp only [Fin.sum_univ_one]
    ring
  constructor
  · intro i
    change (∑ j : Fin 1, (2 : ℚ)*(1/2))=1
    norm_num
  · refine ⟨0,(fun _ => -1),?_,?_,?_,?_⟩
    · intro h
      have hh := congrFun h (0 : Fin 1)
      norm_num at hh
    · rw [hformula]
      norm_num
    · rw [hformula]
      norm_num
    · intro ν
      change Fin 1 → ℤ at ν
      rw [hformula]
      by_cases h : 0 ≤ ν 0
      · have hq : (0 : ℚ) ≤ (ν 0 : ℚ) := by exact_mod_cast h
        nlinarith [sq_nonneg ((ν 0 : ℚ))]
      · have hz : ν 0 ≤ -1 := by omega
        have hq : (ν 0 : ℚ) ≤ -1 := by exact_mod_cast hz
        nlinarith [sq_nonneg ((ν 0 : ℚ)+1)]

end
end D5.S3.VertexAlgebra.LatticeDualCosetEnergy
