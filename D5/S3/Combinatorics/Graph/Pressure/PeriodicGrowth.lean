/- GID: D5/S3/Combinatorics/Graph/Pressure/PeriodicGrowth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/PeriodicGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every-state periodic-safe weighted growth from the actual positive eigenvector. -/
import D5.S3.Combinatorics.Graph.Pressure.PerronDoob
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Finite weighted graph pressure on the original support. -/
noncomputable section
open scoped BigOperators Matrix Topology
open Filter Matrix
namespace D5.S3.Combinatorics.Graph.Pressure.Network
universe u
variable {X : Type u} [Fintype X] [DecidableEq X] (G : Network X)
variable (c : X → X → ℝ) (τ : ℝ)

private lemma eigen_pow (n : ℕ) :
    (G.W c τ ^ n) *ᵥ (G.perron c τ).right = (G.perron c τ).root ^ n • (G.perron c τ).right := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,(G.perron c τ).eigen]
    simp [smul_smul,pow_succ,mul_comm]

/-- The factors are r_i/M and r_i/m, valid at every n including zero. -/
theorem growth_sandwich (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hmin : ∀ i, m ≤ (G.perron c τ).right i) (hmax : ∀ i, (G.perron c τ).right i ≤ M)
    (n : ℕ) (i : X) :
    ((G.perron c τ).right i / M) * (G.perron c τ).root ^ n ≤ ((G.W c τ ^ n) *ᵥ (fun _ => 1)) i ∧
    ((G.W c τ ^ n) *ᵥ (fun _ => 1)) i ≤ ((G.perron c τ).right i / m) * (G.perron c τ).root ^ n := by
  classical
  let r := (G.perron c τ).right
  let lam := (G.perron c τ).root
  have hn := Matrix.pow_apply_nonneg (G.W_nonneg c τ) n
  have he : ∑ j, (G.W c τ ^ n) i j * r j = lam ^ n * r i := by
    simpa [Matrix.mulVec,dotProduct,r,lam] using congrFun (G.eigen_pow c τ n) i
  have hlow : m * ((G.W c τ ^ n) *ᵥ (fun _ => 1)) i ≤ lam ^ n * r i := by
    rw [← he]
    simp only [Matrix.mulVec,dotProduct,mul_one,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmin j) (hn i j)
  have hhigh : lam ^ n * r i ≤ M * ((G.W c τ ^ n) *ᵥ (fun _ => 1)) i := by
    rw [← he]
    simp only [Matrix.mulVec,dotProduct,mul_one,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hmax j) (hn i j)
  constructor
  · have hh := (div_le_iff₀ hM).2 (by simpa [mul_comm] using hhigh)
    simpa [r,lam,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  · have hh := (le_div_iff₀ hm).2 (by simpa [mul_comm] using hlow)
    simpa [r,lam,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

/-- Every starting state has the same growth rate, even when the support is periodic. -/
theorem weighted_growth (i : X) :
    Tendsto (fun n : ℕ => Real.log (((G.W c τ ^ n) *ᵥ (fun _ => 1)) i) / (n : ℝ))
      atTop (𝓝 (Real.log (G.perron c τ).root)) := by
  classical
  letI : Nonempty X := ⟨G.hasEdge.choose⟩
  let r := (G.perron c τ).right
  let lam := (G.perron c τ).root
  obtain ⟨imin,_,hmin⟩ := Finset.exists_min_image Finset.univ r Finset.univ_nonempty
  obtain ⟨imax,_,hmax⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hm : 0 < r imin := (G.perron c τ).right_pos imin
  have hM : 0 < r imax := (G.perron c τ).right_pos imax
  have hlam : 0 < lam := (G.perron c τ).root_pos
  have ha : 0 < r i / r imax := div_pos ((G.perron c τ).right_pos i) hM
  have hb : 0 < r i / r imin := div_pos ((G.perron c τ).right_pos i) hm
  have hs (n : ℕ) := G.growth_sandwich c τ (r imin) (r imax) hm hM
    (fun j => hmin j (Finset.mem_univ j)) (fun j => hmax j (Finset.mem_univ j)) n i
  have hp (n : ℕ) : 0 < ((G.W c τ ^ n) *ᵥ (fun _ => 1)) i :=
    lt_of_lt_of_le (mul_pos ha (pow_pos hlam n)) (hs n).1
  have hlog (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
      Real.log (a * lam ^ n) / (n : ℝ) = Real.log lam + Real.log a / (n : ℝ) := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [Real.log_mul (ne_of_gt ha) (pow_ne_zero n (ne_of_gt hlam)),Real.log_pow]
    field_simp
    <;> ring
  have hbounds : ∀ᶠ n : ℕ in atTop,
      Real.log lam + Real.log (r i / r imax) / (n : ℝ) ≤
        Real.log (((G.W c τ ^ n) *ᵥ (fun _ => 1)) i) / (n : ℝ) ∧
      Real.log (((G.W c τ ^ n) *ᵥ (fun _ => 1)) i) / (n : ℝ) ≤
        Real.log lam + Real.log (r i / r imin) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · rw [← hlog _ ha n hn0]
      exact div_le_div_of_nonneg_right (Real.log_le_log (mul_pos ha (pow_pos hlam n)) (hs n).1) hnR
    · rw [← hlog _ hb n hn0]
      exact div_le_div_of_nonneg_right (Real.log_le_log (hp n) (hs n).2) hnR
  have hL : Tendsto (fun n : ℕ => Real.log lam + Real.log (r i / r imax) / (n : ℝ))
      atTop (𝓝 (Real.log lam)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hU : Tendsto (fun n : ℕ => Real.log lam + Real.log (r i / r imin) / (n : ℝ))
      atTop (𝓝 (Real.log lam)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)

/-- The adjacency uses counting weight one, never normalized outdegree weights. -/
def adjacency : Matrix X X ℝ := by
  classical
  exact fun i j => if G.edge i j then 1 else 0

lemma W_eq_adjacency (hc : ∀ i j, G.edge i j → c i j = 0) : G.W c τ = G.adjacency := by
  classical
  ext i j
  by_cases he : G.edge i j <;> simp [W,adjacency,he,hc i j]

/-- Zero supported costs give the logarithm of the actual complex adjacency radius. -/
theorem zero_cost_growth (τ : ℝ) (hc : ∀ i j, G.edge i j → c i j = 0) (i : X) :
    Tendsto (fun n : ℕ => Real.log (((G.adjacency ^ n) *ᵥ (fun _ => 1)) i) / (n : ℝ))
      atTop (𝓝 (Real.log (spectralRadius ℂ (G.adjacency.map (algebraMap ℝ ℂ))).toReal)) := by
  have hr := (G.perron c τ).radius
  rw [G.W_eq_adjacency c τ hc] at hr
  have hreal : (spectralRadius ℂ (G.adjacency.map (algebraMap ℝ ℂ))).toReal = (G.perron c τ).root := by
    rw [hr,ENNReal.toReal_ofReal (G.perron c τ).root_pos.le]
  rw [hreal]
  simpa only [G.W_eq_adjacency c τ hc] using G.weighted_growth c τ i
end D5.S3.Combinatorics.Graph.Pressure.Network
