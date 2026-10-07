/- GID: D5/S3/VertexAlgebra/LatticeChargeCoercivity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeChargeCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Gram coercivity and finite all-integer energy fibers. -/

/-
Real positive Gram coercivity in Euclidean (L2) space and finite integral
charge boxes. The compact-sphere argument includes the empty sphere case,
so rank zero is internal to the theorem. No integral unimodularity is used.
Mathlib imports retain their Apache 2.0 license and original authorship.
-/
import D5.S3.VertexAlgebra.LatticePositiveEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace D5.S3.VertexAlgebra.LatticePositiveEnergy
open LatticeGeneratingFieldLocality Matrix
noncomputable section

def realQuadratic (D : LatticeData) (x : EuclideanSpace ℝ (Fin D.rank)) : ℝ :=
  ∑ i, ∑ j, x i * (D.G i j : ℝ) * x j

theorem realQuadratic_continuous (D : LatticeData) : Continuous (realQuadratic D) := by
  unfold realQuadratic
  fun_prop

@[simp] theorem realQuadratic_zero (D : LatticeData) : realQuadratic D 0 = 0 := by
  simp [realQuadratic]

theorem realQuadratic_smul (D : LatticeData) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin D.rank)) :
    realQuadratic D (t • x) = t ^ 2 * realQuadratic D x := by
  simp only [realQuadratic, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem realQuadratic_positive (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (x : EuclideanSpace ℝ (Fin D.rank)) (hx : x ≠ 0) : 0 < realQuadratic D x := by
  have hv : (fun i => x i) ≠ 0 := by
    intro h
    apply hx
    ext i
    exact congrFun h i
  simpa [realQuadratic, dotProduct, Matrix.mulVec, Matrix.map_apply,
    Finset.mul_sum, mul_assoc] using hD.dotProduct_mulVec_pos hv

/-- The genuine L2 lower bound, uniformly including rank zero. -/
theorem quadratic_coercive (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin D.rank),
      c * (∑ i, (x i)^2) ≤ realQuadratic D x := by
  classical
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin D.rank)) 1
  have normalize (x : EuclideanSpace ℝ (Fin D.rank)) (hx : x ≠ 0) :
      ‖x‖⁻¹ • x ∈ S := by
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp [S, Metric.mem_sphere, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), hn]
  by_cases hs : S.Nonempty
  · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin D.rank)) 1).exists_isMinOn hs (realQuadratic_continuous D).continuousOn
    have hyn : ‖y‖ = 1 := by simpa [S, Metric.mem_sphere, dist_zero_right] using hy
    have hy0 : y ≠ 0 := by intro h; simp [h] at hyn
    refine ⟨realQuadratic D y, realQuadratic_positive D hD y hy0, ?_⟩
    intro x
    rw [← EuclideanSpace.real_norm_sq_eq]
    by_cases hx : x = 0
    · simp [hx]
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have h := hmin (normalize x hx)
      change realQuadratic D y ≤ realQuadratic D (‖x‖⁻¹ • x) at h
      rw [realQuadratic_smul] at h
      have hc := mul_le_mul_of_nonneg_left h (sq_nonneg ‖x‖)
      have hid : ‖x‖ ^ 2 * (‖x‖⁻¹ ^ 2 * realQuadratic D x) = realQuadratic D x := by
        field_simp [ne_of_gt hn]
      rw [hid] at hc
      simpa [mul_comm] using hc
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hx : x = 0 := by
      by_contra hx
      exact hs ⟨_, normalize x hx⟩
    simp [hx]

theorem realQuadratic_charge (D : LatticeData) (a : Charge D) :
    realQuadratic D (WithLp.toLp 2 (fun i => (a i : ℝ))) =
      2 * (chargeEnergy D a : ℝ) := by
  have h := two_chargeEnergy D a
  have hr : (bilinear D a a : ℝ) = 2 * (chargeEnergy D a : ℝ) := by exact_mod_cast h.symm
  simpa [realQuadratic, bilinear, Int.cast_sum, Int.cast_mul] using hr

/-- Each charge sublevel is contained in a derived finite integer box. -/
theorem charge_sublevel_box (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) :
    ∃ B : ℕ, ∀ a : Charge D, chargeEnergy D a ≤ N →
      ∀ i, a i ∈ Set.Icc (-(B : ℤ)) B := by
  classical
  obtain ⟨c, hc, hbound⟩ := quadratic_coercive D hD
  obtain ⟨B, hB⟩ := exists_nat_gt (2 * (N : ℝ) / c + 1)
  refine ⟨B, ?_⟩
  intro a ha i
  have h := hbound (WithLp.toLp 2 (fun i => (a i : ℝ)))
  rw [realQuadratic_charge] at h
  have hs : (a i : ℝ)^2 ≤ ∑ j : Fin D.rank, (a j : ℝ)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j : ℝ)) (Finset.mem_univ i)
  have haR : (chargeEnergy D a : ℝ) ≤ (N : ℝ) := by exact_mod_cast ha
  have hdiv : 2 * (N : ℝ) / c < (B : ℝ) - 1 := by linarith
  have hb : 2 * (N : ℝ) < c * ((B : ℝ) - 1) := by
    simpa [mul_comm] using (div_lt_iff₀ hc).mp hdiv
  have hcq : c * (a i : ℝ)^2 ≤ 2 * (N : ℝ) :=
    (mul_le_mul_of_nonneg_left hs hc.le).trans (h.trans (by linarith))
  have hlo : -(B : ℝ) ≤ (a i : ℝ) := by
    by_contra hn
    have hb0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have hsq : (B : ℝ) ≤ (a i : ℝ)^2 + 1 := by nlinarith [sq_nonneg ((a i : ℝ) + 1)]
    nlinarith
  have hhi : (a i : ℝ) ≤ (B : ℝ) := by
    by_contra hn
    have hb0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have hsq : (B : ℝ) ≤ (a i : ℝ)^2 + 1 := by nlinarith [sq_nonneg ((a i : ℝ) - 1)]
    nlinarith
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

theorem chargeSublevel_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) :
    Set.Finite {a : Charge D | chargeEnergy D a ≤ N} := by
  obtain ⟨B, hB⟩ := charge_sublevel_box D hD N
  exact (Set.Finite.pi' (fun _ : Fin D.rank => Set.finite_Icc (-(B : ℤ)) B)).subset
    (fun a ha => hB a ha)

abbrev EnergyFiber (D : LatticeData) (n : ℤ) := {a : Label D // energy D a = n}

theorem energyFiber_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) :
    Finite (EnergyFiber D n) := by
  classical
  haveI : Finite {a : Charge D // chargeEnergy D a ≤ n.toNat} :=
    (chargeSublevel_finite D hD n.toNat).to_subtype
  haveI := oscillatorLeFinite D n.toNat
  let f (a : EnergyFiber D n) :
      {b : Charge D // chargeEnergy D b ≤ n.toNat} ×
        {d : Exponent D // oscillatorEnergy d ≤ n.toNat} :=
    ⟨⟨a.1.1, by
        have he := a.2
        have hq := chargeEnergy_nonneg D hD a.1.1
        dsimp [energy] at he
        omega⟩,
     ⟨a.1.2, by
        have he := a.2
        have hq := chargeEnergy_nonneg D hD a.1.1
        dsimp [energy] at he
        omega⟩⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)

#print axioms quadratic_coercive
#print axioms chargeSublevel_finite
#print axioms energyFiber_finite
end
end D5.S3.VertexAlgebra.LatticePositiveEnergy
