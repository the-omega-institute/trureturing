/- GID: D5/S3/VertexAlgebra/LatticeDualCosetEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeDualCosetEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational lattice-coset energies have finite sublevels and an attained global minimum. -/

import D5.S3.VertexAlgebra.LatticeDualCosetModule
import D5.S3.VertexAlgebra.LatticeEnergyGrading
import Mathlib.Data.Rat.Floor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.LatticeDualCosetEnergy
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open scoped BigOperators
noncomputable section

variable (D : LatticeData)

def pairing (x y : Fin D.rank → ℚ) : ℚ :=
  ∑ i, ∑ j, x i * (D.G i j : ℚ) * y j

def chargeWeight (μ : Fin D.rank → ℚ) (γ : Charge D) : ℚ :=
  pairing D (fun i => (γ i : ℚ) + μ i) (fun i => (γ i : ℚ) + μ i) / 2

def weight (μ : Fin D.rank → ℚ) (a : Label D) : ℚ :=
  (oscillatorEnergy a.2 : ℚ) + chargeWeight D μ a.1

/-- A single positive integral denominator works in every coordinate, also in rank zero. -/
theorem common_denominator (μ : Fin D.rank → ℚ) :
    ∃ s : ℕ, 0 < s ∧ ∃ ν : Charge D, ∀ i, (s : ℚ) * μ i = (ν i : ℚ) := by
  classical
  let s : ℕ := ∏ i, (μ i).den
  have hs : 0 < s := Finset.prod_pos (fun i _ => (μ i).den_pos)
  have hd (i : Fin D.rank) : (μ i).den ∣ s :=
    Finset.dvd_prod_of_mem (fun i => (μ i).den) (Finset.mem_univ i)
  refine ⟨s, hs, (fun i => (μ i).num * (s / (μ i).den : ℕ)), ?_⟩
  intro i
  have hid : (s / (μ i).den) * (μ i).den = s := Nat.div_mul_cancel (hd i)
  have hiq : ((s / (μ i).den : ℕ) : ℚ) * ((μ i).den : ℚ) = (s : ℚ) := by
    exact_mod_cast hid
  have hm : μ i * ((μ i).den : ℚ) = ((μ i).num : ℚ) :=
    (eq_div_iff (by exact_mod_cast (μ i).den_ne_zero)).mp (Rat.num_div_den (μ i)).symm
  rw [← hiq]
  simp only [Int.cast_mul, Int.cast_natCast]
  linear_combination ((s / (μ i).den : ℕ) : ℚ) * hm

def clearedCharge (s : ℕ) (ν : Charge D) (γ : Charge D) : Charge D :=
  fun i => (s : ℤ) * γ i + ν i

theorem clearedCharge_injective (s : ℕ) (hs : 0 < s) (ν : Charge D) :
    Function.Injective (clearedCharge D s ν) := by
  intro a b h
  ext i
  have hi := congrFun h i
  dsimp [clearedCharge] at hi
  exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hs)) (add_right_cancel hi)

/-- Exact denominator clearing reduces rational shifted norms to integral charge energy. -/
theorem chargeWeight_cleared (μ : Fin D.rank → ℚ) (s : ℕ) (hs : 0 < s)
    (ν : Charge D) (hν : ∀ i, (s : ℚ) * μ i = (ν i : ℚ)) (γ : Charge D) :
    chargeWeight D μ γ = (chargeEnergy D (clearedCharge D s ν γ) : ℚ) / (s : ℚ)^2 := by
  have hcast (i : Fin D.rank) :
      (clearedCharge D s ν γ i : ℚ) = (s : ℚ) * ((γ i : ℚ) + μ i) := by
    simp only [clearedCharge, Int.cast_add, Int.cast_mul, Int.cast_natCast, ← hν]
    ring
  have he : (2 : ℚ) * (chargeEnergy D (clearedCharge D s ν γ) : ℚ) =
      (bilinear D (clearedCharge D s ν γ) (clearedCharge D s ν γ) : ℚ) := by
    exact_mod_cast two_chargeEnergy D (clearedCharge D s ν γ)
  have hb : (bilinear D (clearedCharge D s ν γ) (clearedCharge D s ν γ) : ℚ) =
      (s : ℚ)^2 * pairing D (fun i => (γ i : ℚ) + μ i)
        (fun i => (γ i : ℚ) + μ i) := by
    simp only [bilinear, Int.cast_sum, Int.cast_mul, hcast, pairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hb] at he
  rw [eq_div_iff (pow_ne_zero 2 (by exact_mod_cast ne_of_gt hs))]
  unfold chargeWeight
  linear_combination -he / 2

theorem chargeWeight_nonneg (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (γ : Charge D) :
    0 ≤ chargeWeight D μ γ := by
  obtain ⟨s, hs, ν, hν⟩ := common_denominator D μ
  rw [chargeWeight_cleared D μ s hs ν hν]
  exact div_nonneg (by exact_mod_cast chargeEnergy_nonneg D hD _) (sq_nonneg _)

/-- No new coercivity proof: the cleared charge injects into an integral sublevel. -/
theorem charge_sublevel_finite (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (R : ℚ) :
    Set.Finite {γ : Charge D | chargeWeight D μ γ ≤ R} := by
  classical
  obtain ⟨s, hs, ν, hν⟩ := common_denominator D μ
  obtain ⟨N, hN⟩ := exists_nat_ge ((s : ℚ)^2 * R)
  have hbound (γ : Charge D) (hγ : chargeWeight D μ γ ≤ R) :
      chargeEnergy D (clearedCharge D s ν γ) ≤ (N : ℤ) := by
    rw [chargeWeight_cleared D μ s hs ν hν] at hγ
    have hsq : (0 : ℚ) < (s : ℚ)^2 := sq_pos_of_pos (by exact_mod_cast hs)
    have hq : (chargeEnergy D (clearedCharge D s ν γ) : ℚ) ≤ (N : ℚ) :=
      ((div_le_iff₀ hsq).mp hγ).trans (by simpa [mul_comm] using hN)
    exact_mod_cast hq
  apply Set.Finite.of_injOn (f := clearedCharge D s ν) (t := {a | chargeEnergy D a ≤ (N : ℤ)})
  · intro γ hγ
    exact hbound γ hγ
  · exact (clearedCharge_injective D s hs ν).injOn
  · exact chargeSublevel_finite D hD N

/-- Every total rational energy sublevel is finite, with no duality hypothesis. -/
theorem sublevel_finite (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (R : ℚ) :
    Set.Finite {a : Label D | weight D μ a ≤ R} := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge R
  let C := {γ : Charge D | chargeWeight D μ γ ≤ (N : ℚ)}
  let O := {d : Exponent D | oscillatorEnergy d ≤ N}
  have hc : C.Finite := charge_sublevel_finite D μ hD N
  have ho : O.Finite := by
    letI : Finite O := oscillatorLeFinite D N
    exact Set.toFinite O
  apply (hc.prod ho).subset
  intro a ha
  have hq := chargeWeight_nonneg D μ hD a.1
  have hw : 0 ≤ (oscillatorEnergy a.2 : ℚ) := Nat.cast_nonneg _
  change chargeWeight D μ a.1 ≤ (N : ℚ) ∧ oscillatorEnergy a.2 ≤ N
  dsimp [weight] at ha
  constructor
  · linarith
  · exact_mod_cast (show (oscillatorEnergy a.2 : ℚ) ≤ (N : ℚ) by linarith)

/-- A nonempty finite sublevel yields an actual global minimizing charge. -/
theorem attained_minimum (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ∃ γ₀ : Charge D, 0 ≤ chargeWeight D μ γ₀ ∧
      ∀ γ : Charge D, chargeWeight D μ γ₀ ≤ chargeWeight D μ γ := by
  classical
  let S := {γ : Charge D | chargeWeight D μ γ ≤ chargeWeight D μ 0}
  have hS : S.Finite := charge_sublevel_finite D μ hD _
  have hn : S.Nonempty := ⟨0, by simp [S]⟩
  obtain ⟨γ₀, hγ₀, hmin⟩ := Set.exists_min_image S (chargeWeight D μ) hS hn
  refine ⟨γ₀, chargeWeight_nonneg D μ hD γ₀, ?_⟩
  intro γ
  by_cases hγ : γ ∈ S
  · exact hmin γ hγ
  · exact hγ₀.trans (le_of_lt (lt_of_not_ge hγ))

theorem fiber_finite (μ : Fin D.rank → ℚ)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (e : ℚ) :
    Finite {a : Label D // weight D μ a = e} := by
  have hs : Set.Finite {a : Label D | weight D μ a = e} :=
    (sublevel_finite D μ hD e).subset (by intro a ha; exact le_of_eq ha)
  exact hs.to_subtype

end
end D5.S3.VertexAlgebra.LatticeDualCosetEnergy
