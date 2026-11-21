/- GID: D5/S3/Quantum/PureState/PhaseProductFidelity
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PhaseProductFidelity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp purity-loss comparison for finite singleton and product phase ensembles. -/

import D5.S3.Factorization.JordanCototientRecordLimitInfinity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace D5.S3.Quantum.PureState.PhaseProductFidelity
open scoped BigOperators

/-- Squared overlap for the constant tag and the individual phases. -/
noncomputable def simplex {n : ℕ} (u : Fin n → ℂ) : ℝ :=
  Complex.normSq (1 + ∑ i, u i) / (n+1 : ℝ)^2

/-- Squared overlap for the product of the two-component equatorial vectors. -/
noncomputable def cube {n : ℕ} (u : Fin n → ℂ) : ℝ :=
  ∏ i, ((1+(u i).re)/2)

private theorem normSq_one_add (z : ℂ) :
    Complex.normSq (1+z) = 1+2*z.re+Complex.normSq z := by
  rw [Complex.normSq_add]
  simp [add_assoc, add_comm, add_left_comm]

private theorem loss_le {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    1-cube u ≤ ((n:ℝ)+1)^2/4*(1-simplex u) := by
  let z := ∑ i, u i
  have hz : ‖z‖ ≤ n := calc
    ‖z‖ ≤ ∑ i, ‖u i‖ := norm_sum_le _ _
    _ = n := by simp [hu]
  have hs : Complex.normSq z ≤ (n:ℝ)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hr : ∀ i, |(u i).re| ≤ 1 := fun i => (Complex.abs_re_le_norm _).trans_eq (hu i)
  have h := D5.S3.Factorization.JordanCototientRecordLimitInfinity.one_sub_prod_le_sum
    Finset.univ (fun i => 1-(1+(u i).re)/2)
    (fun i _ => by linarith [(abs_le.mp (hr i)).2])
    (fun i _ => by linarith [(abs_le.mp (hr i)).1])
  simp only [sub_sub_cancel] at h
  have hf : ∑ i, (1-(1+(u i).re)/2) = ((n:ℝ)-z.re)/2 := by
    change _ = ((n:ℝ)-(∑ i, u i).re)/2
    rw [Complex.re_sum]
    simp only [div_eq_mul_inv, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  rw [hf] at h
  change 1-cube u ≤ _ at h
  change 1-cube u ≤ ((n:ℝ)+1)^2/4*(1-Complex.normSq (1+z)/((n:ℝ)+1)^2)
  rw [normSq_one_add]
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp [hn]
  nlinarith only [hs,h]

/-- The uniform coefficient is attained in the limit when all phases approach one together. -/
private theorem sharp {n : ℕ} (hn : 0 < n) {C : ℝ}
    (bound : ∀ u : Fin n → ℂ, (∀ i, ‖u i‖ = 1) → 1-cube u ≤ C*(1-simplex u)) :
    ((n:ℝ)+1)^2/4 ≤ C := by
  have npos : 0 < (n:ℝ) := by exact_mod_cast hn
  have nn : (n:ℝ)+1 ≠ 0 := by positivity
  have H (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
      (∑ k ∈ Finset.range n, (1-b)^k) ≤ C*4*n/((n:ℝ)+1)^2 := by
    let x : ℝ := 1-2*b
    have hx : ‖x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      dsimp [x]
      constructor <;> linarith
    let z : ℂ := (x : ℂ) + Complex.I * (Real.sqrt (1-x^2) : ℂ)
    have hz : Complex.normSq z = 1 := Complex.normSq_ofReal_add_I_mul_sqrt_one_sub hx
    have hzre : z.re = 1-2*b := by simp [z, x]
    have hzn : ‖z‖ = 1 := by nlinarith only [Complex.sq_norm z,hz,norm_nonneg z]
    have V := bound (fun _ => z) (fun _ => hzn)
    have hcube : cube (fun _ : Fin n => z) = (1-b)^n := by
      change ∏ _i : Fin n, ((1+z.re)/2) = _
      rw [hzre]
      simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]
      ring
    have hsimplex : simplex (fun _ : Fin n => z) = 1-4*n*b/((n:ℝ)+1)^2 := by
      simp only [simplex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        normSq_one_add,Complex.normSq_mul,hz,mul_one,Complex.mul_re,
        Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,Complex.normSq_natCast,hzre]
      change (1+2*((n:ℝ)*(1-2*b))+(n:ℝ)*(n:ℝ))/((n:ℝ)+1)^2 = _
      field_simp
      ring
    rw [hcube,hsimplex] at V
    have mulgeom := geom_sum_mul_neg (1-b) n
    have G : (∑ k ∈ Finset.range n, (1-b)^k)*b = 1-(1-b)^n := by linarith only [mulgeom]
    apply (le_of_mul_le_mul_right _ hb)
    rw [G]
    convert V using 1
    ring
  let F (b : ℝ) := ∑ k ∈ Finset.range n, (1-b)^k
  have hc : Continuous F := by unfold F; fun_prop
  have lim : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)) :=
    hc.continuousAt.continuousWithinAt
  have small : ∀ᶠ b : ℝ in nhdsWithin 0 (Set.Ioi 0), b ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have bounded : F 0 ≤ C*4*n/((n:ℝ)+1)^2 := by
    apply le_of_tendsto lim
    filter_upwards [self_mem_nhdsWithin,small] with b hb hb1 using H b hb hb1
  have f0 : F 0 = (n:ℝ) := by simp [F]
  rw [f0] at bounded
  have hmul := (le_div_iff₀ (sq_pos_of_ne_zero nn)).mp bounded
  have hcancel : ((n:ℝ)+1)^2 ≤ C*4 := by
    apply le_of_mul_le_mul_right _ npos
    simpa only [mul_comm (((n:ℝ)+1)^2) (n:ℝ)] using hmul
  linarith only [hcancel]


/-- Weighted sum of pairwise fidelity losses of a finite list of phase vectors. -/
noncomputable def mixedDeficit {m n : ℕ} (F : (Fin n → ℂ) → ℝ)
    (p : Fin m → ℝ) (v : Fin m → Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, p i * p j * (1 - F (fun k => star (v i k) * v j k))

private theorem simplex_conj {n : ℕ} (u : Fin n → ℂ) :
    simplex (fun i => star (u i)) = simplex u := by
  have h : 1 + ∑ i, star (u i) = star (1 + ∑ i, u i) := by rw [star_add,star_one,star_sum]
  unfold simplex
  rw [h]
  exact congrArg (fun t : ℝ => t / ((n:ℝ)+1)^2) (Complex.normSq_conj _)

private theorem cube_conj {n : ℕ} (u : Fin n → ℂ) :
    cube (fun i => star (u i)) = cube u := by simp [cube]

private theorem two_points {n : ℕ} (F : (Fin n → ℂ) → ℝ) (h1 : F 1 = 1)
    (hc : ∀ u, F (fun k => star (u k)) = F u)
    (u : Fin n → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    mixedDeficit F (fun _ : Fin 2 => (1:ℝ)/2) ![(1 : Fin n → ℂ),u] =
    (1 - F u)/2 := by
  have hd : (fun k => star (u k) * u k) = 1 := by
    funext k
    change (starRingEnd ℂ) (u k) * u k = 1
    rw [Complex.conj_mul', hu]
    norm_num
  simp [mixedDeficit, Fin.sum_univ_two]
  change (2:ℝ)⁻¹*2⁻¹*(1-F 1)+(2:ℝ)⁻¹*2⁻¹*(1-F u)+
    ((2:ℝ)⁻¹*2⁻¹*(1-F (fun k => star (u k)))+
     (2:ℝ)⁻¹*2⁻¹*(1-F (fun k => star (u k)*u k))) = _
  rw [hd,h1,hc]
  ring

/-- The same sharp coefficient controls all finite phase ensembles with nonnegative weights. -/
theorem mixed_coefficient_iff {n : ℕ} (hn : 0 < n) (C : ℝ) :
    (∀ (m : ℕ) (p : Fin m → ℝ) (v : Fin m → Fin n → ℂ),
      (∀ i, 0 ≤ p i) → (∀ i k, ‖v i k‖ = 1) →
      mixedDeficit cube p v ≤ C * mixedDeficit simplex p v) ↔
    ((n:ℝ)+1)^2/4 ≤ C := by
  constructor
  · intro h
    apply sharp hn
    intro u hu
    let v : Fin 2 → Fin n → ℂ := ![1,u]
    have hv (i : Fin 2) (k : Fin n) : ‖v i k‖ = 1 := by fin_cases i <;> simp [v,hu]
    have hb := h 2 (fun _ => (1:ℝ)/2) v (by intro; norm_num) hv
    have hco : cube (1 : Fin n → ℂ) = 1 := by simp [cube]
    have hsi : simplex (1 : Fin n → ℂ) = 1 := by
      simp [simplex, normSq_one_add]
      field_simp
      ring
    dsimp only [v] at hb
    rw [two_points cube hco cube_conj u hu,two_points simplex hsi simplex_conj u hu] at hb
    linarith only [hb]
  · intro hC m p v hp hv
    unfold mixedDeficit
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    let u (k : Fin n) := star (v i k) * v j k
    have hu (k : Fin n) : ‖u k‖ = 1 := by simp [u, hv]
    have h := loss_le u hu
    have hS : 0 ≤ 1-simplex u := by
      have hsum : ‖1 + ∑ k, u k‖ ≤ (n:ℝ)+1 := calc
        _ ≤ ‖(1:ℂ)‖ + ‖∑ k, u k‖ := norm_add_le _ _
        _ ≤ ‖(1:ℂ)‖ + ∑ k, ‖u k‖ := add_le_add_right (norm_sum_le ..) _
        _ = _ := by simp [hu,add_comm]
      apply sub_nonneg.mpr
      change Complex.normSq _ / _ ≤ 1
      rw [Complex.normSq_eq_norm_sq, div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hsum 2
    have g := mul_le_mul_of_nonneg_left
      (h.trans (mul_le_mul_of_nonneg_right hC hS)) (mul_nonneg (hp i) (hp j))
    change p i*p j*(1-cube u) ≤ C*(p i*p j*(1-simplex u))
    linarith only [g]


end D5.S3.Quantum.PureState.PhaseProductFidelity
