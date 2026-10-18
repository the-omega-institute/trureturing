/- GID: D5/S3/Combinatorics/Graph/Pressure/WeightedWalks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/WeightedWalks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite unrestricted supported walks, their exact weighted matrix-power sum and counting entropy. -/
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
open scoped BigOperators Matrix ENNReal
open Matrix
namespace D5.S3.Combinatorics.Graph.Pressure
universe u
variable {X : Type u} [Fintype X] [DecidableEq X]

/-- A finite directed support. Prop-valued edges exclude parallel edges; looplessness is
not needed by the proof, so the result also covers the original simple graphs. -/
structure Network (X : Type u) where
  edge : X → X → Prop
  connected : @Quiver.IsStronglyConnected X ⟨fun i j => PLift (edge i j)⟩
  hasEdge : ∃ i j, edge i j

namespace Network
variable (G : Network X)
/-- Counting weights on the actual support, with arbitrary finite real edge costs. -/
def W (c : X → X → ℝ) (τ : ℝ) : Matrix X X ℝ :=
  by
  classical
  exact fun i j => if G.edge i j then Real.exp (-c i j / τ) else 0

lemma W_nonneg (c : X → X → ℝ) (τ : ℝ) (i j : X) : 0 ≤ G.W c τ i j := by
  classical
  unfold W
  split_ifs <;> positivity

lemma W_pos_iff (c : X → X → ℝ) (τ : ℝ) (i j : X) :
    0 < G.W c τ i j ↔ G.edge i j := by
  classical
  simp only [W]
  split_ifs with h
  · exact iff_of_true (Real.exp_pos _) h
  · simp [h]

/-- The actual exponential weights have precisely the original strongly connected support. -/
theorem W_irreducible (c : X → X → ℝ) (τ : ℝ) : (G.W c τ).IsIrreducible := by
  classical
  refine ⟨G.W_nonneg c τ, ?_⟩
  letI : Quiver X := Matrix.toQuiver (G.W c τ)
  have hc : Quiver.IsStronglyConnected X := by
    intro i j
    obtain ⟨p⟩ := G.connected i j
    induction p with
    | nil => exact ⟨Quiver.Path.nil⟩
    | cons p e ih => exact ⟨ih.some.cons ⟨(G.W_pos_iff c τ _ _).2 e.down⟩⟩
  obtain ⟨i,j,hij⟩ := G.hasEdge
  exact hc.isSStronglyConnected_of_hom (i₀ := i) (j₀ := j)
    (PLift.up ((G.W_pos_iff c τ i j).2 hij))

/-- Constructed Perron data, including the actual complex spectral radius, never an input. -/
structure Perron (c : X → X → ℝ) (τ : ℝ) where
  root : ℝ
  right : X → ℝ
  root_pos : 0 < root
  right_pos : ∀ i, 0 < right i
  eigen : G.W c τ *ᵥ right = root • right
  radius : spectralRadius ℂ ((G.W c τ).map (algebraMap ℝ ℂ)) = ENNReal.ofReal root

/-- Apply the retained source supplier directly; the only new spectral step is the
real-to-complex eigenpair transport and the two supremum inequalities. -/
theorem exists_perron (c : X → X → ℝ) (τ : ℝ) : Nonempty (G.Perron c τ) := by
  classical
  letI : Nonempty X := ⟨G.hasEdge.choose⟩
  have hi := G.W_irreducible c τ
  obtain ⟨lam,r,hlam,hr,he,hs⟩ := Matrix.perron_root_eq_positive_eigenvalue hi hi.nonneg
  have rn : r ≠ 0 := Pi.ne_zero_of_pos hr
  let z : X → ℂ := fun i => (r i : ℂ)
  have zn : z ≠ 0 := by
    intro hz
    apply rn
    ext i
    have hh : (r i : ℂ) = 0 := congrFun hz i
    exact_mod_cast hh
  have ze : (G.W c τ).map (algebraMap ℝ ℂ) *ᵥ z = (lam : ℂ) • z := by
    ext i
    have hh : (G.W c τ *ᵥ r) i = lam * r i := by simpa using congrFun he i
    simpa [z,smul_eq_mul,Matrix.mulVec,dotProduct,Matrix.map_apply] using
      congrArg (fun a : ℝ => (a : ℂ)) hh
  have hm := Matrix.mem_spectrum_of_eigenvalue zn ze
  refine ⟨⟨lam,r,hlam,hr,he,?_⟩⟩
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · refine iSup₂_le fun μ hμ => ?_
    have hb := Matrix.eigenvalue_abs_le_perron_root hi hi.nonneg hμ
    rw [hs] at hb
    simpa only [← coe_nnnorm,ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hb
  · have hl : (‖(lam : ℂ)‖₊ : ℝ≥0∞) = ENNReal.ofReal lam := by
      simp [Complex.nnnorm_real,Real.nnnorm_of_nonneg hlam.le,ENNReal.ofReal_eq_coe_nnreal hlam.le]
    rw [← hl]
    exact le_iSup_of_le (lam : ℂ) (le_iSup_of_le hm le_rfl)

/-- The canonical actual eigenpair is chosen from the supplier-applied existence proof. -/
def perron (c : X → X → ℝ) (τ : ℝ) : G.Perron c τ := Classical.choice (G.exists_perron c τ)

end Network
end D5.S3.Combinatorics.Graph.Pressure

noncomputable section
open scoped BigOperators Matrix Topology
open Filter Matrix
namespace D5.S3.Combinatorics.Graph.Pressure.Network
universe u
variable {X : Type u} [Fintype X] [DecidableEq X] (G : Network X)
variable (c : X → X → ℝ) (τ : ℝ)

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
    have hr_ne : r ≠ 0 := by
      obtain ⟨i₀, _, _⟩ := G.hasEdge
      intro hz
      have hzero := congrFun hz i₀
      exact (ne_of_gt ((G.perron c τ).right_pos i₀)) hzero
    have hev : Module.End.HasEigenvector (G.W c τ).toLin' lam r :=
      ⟨Module.End.mem_eigenspace_iff.mpr (G.perron c τ).eigen, hr_ne⟩
    have hpow : (G.W c τ ^ n) *ᵥ r = lam ^ n • r := by
      simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using
        Module.End.HasEigenvector.pow_apply hev n
    simpa [Matrix.mulVec,dotProduct,r,lam] using congrFun hpow i
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

noncomputable section
open scoped BigOperators Matrix Topology
open Filter Matrix
namespace D5.S3.Combinatorics.Graph.Pressure.Network
universe u
variable {X : Type u} [Fintype X] [DecidableEq X] (G : Network X)

/-- All length-n supported walks from x, with no distinctness restriction.
The unique length-zero walk is included; successors may repeat any earlier vertex. -/
def Walks (G : Network X) : ℕ → X → Type u
  | 0, _ => PUnit
  | n + 1, x => Σ y : {y // G.edge x y}, Walks G n y.1

instance walksFintype (n : ℕ) (x : X) : Fintype (G.Walks n x) := by
  classical
  induction n generalizing x with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI : ∀ y : {y // G.edge x y}, Fintype (G.Walks n y.1) := fun y => ih y.1
    exact inferInstanceAs (Fintype (Σ y : {y // G.edge x y}, G.Walks n y.1))

def walkBoltzmann (G : Network X) (c : X → X → ℝ) (τ : ℝ) :
    {n : ℕ} → {x : X} → G.Walks n x → ℝ
  | 0, _, _ => 1
  | _ + 1, x, w => Real.exp (-c x w.1.1 / τ) * walkBoltzmann G c τ w.2

def walkSum (c : X → X → ℝ) (τ : ℝ) (n : ℕ) (x : X) : ℝ :=
  ∑ w : G.Walks n x, G.walkBoltzmann c τ w

/-- Exact enumeration of all unrestricted supported walks at every length and start. -/
private theorem walkSum_eq_matrix (c : X → X → ℝ) (τ : ℝ) (n : ℕ) (x : X) :
    G.walkSum c τ n x = ((G.W c τ ^ n) *ᵥ (fun _ => 1)) x := by
  classical
  induction n generalizing x with
  | zero =>
    calc
      G.walkSum c τ 0 x = ∑ _w : PUnit.{u+1}, (1 : ℝ) :=
        Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)
      _ = ((G.W c τ ^ 0) *ᵥ (fun _ => 1)) x := by simp
  | succ n ih =>
    calc
      G.walkSum c τ (n + 1) x =
          ∑ w : (Σ y : {y // G.edge x y}, G.Walks n y.1),
            Real.exp (-c x w.1.1 / τ) * G.walkBoltzmann c τ w.2 :=
        Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)
      _ = ∑ y : {y // G.edge x y},
          Real.exp (-c x y.1 / τ) * G.walkSum c τ n y.1 := by
        rw [Fintype.sum_sigma]
        simp only [walkSum, Finset.mul_sum]
      _ = ∑ y : {y // G.edge x y}, G.W c τ x y.1 *
          (((G.W c τ ^ n) *ᵥ (fun _ => 1)) y.1) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [ih]
        simp [W, y.2]
      _ = ∑ y : X, G.W c τ x y * (((G.W c τ ^ n) *ᵥ (fun _ => 1)) y) := by
        symm
        apply Finset.sum_congr_set {y | G.edge x y}
        · intro y hy; rfl
        · intro y hy
          change ¬G.edge x y at hy
          simp [W, hy]
      _ = _ := by rw [pow_succ', ← Matrix.mulVec_mulVec] <;> rfl

/-- The unrestricted weighted-walk sum has the actual periodic-safe Perron growth. -/
private theorem walk_growth (c : X → X → ℝ) (τ : ℝ) (x : X) :
    Tendsto (fun n : ℕ => Real.log (G.walkSum c τ n x) / (n : ℝ))
      atTop (𝓝 (Real.log (G.perron c τ).root)) := by
  simpa only [G.walkSum_eq_matrix] using G.weighted_growth c τ x

/-- Zero supported costs count the actual unrestricted walk type, including n=0. -/
private theorem zero_cost_walkSum (c : X → X → ℝ) (τ : ℝ)
    (hc : ∀ i j, G.edge i j → c i j = 0) (n : ℕ) (x : X) :
    G.walkSum c τ n x = (Nat.card (G.Walks n x) : ℝ) := by
  classical
  have hw : ∀ (n : ℕ) (x : X) (w : G.Walks n x), G.walkBoltzmann c τ w = 1 := by
    intro n
    induction n with
    | zero => intro x w; rfl
    | succ n ih =>
      intro x w
      simp [walkBoltzmann, hc x w.1.1 w.1.2, ih]
  simp [walkSum, hw, Nat.card_eq_fintype_card]

/-- Path-counting entropy is the logarithm of the actual complex adjacency radius. -/
private theorem counting_entropy (x : X) :
    Tendsto (fun n : ℕ => Real.log (Nat.card (G.Walks n x) : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log (spectralRadius ℂ (G.adjacency.map (algebraMap ℝ ℂ))).toReal)) := by
  have hc : ∀ i j, G.edge i j → (fun _ _ : X => (0 : ℝ)) i j = 0 := by simp
  have hh (n : ℕ) := G.zero_cost_walkSum (fun _ _ => 0) 1 hc n x
  simp_rw [G.walkSum_eq_matrix, G.W_eq_adjacency (fun _ _ => 0) 1 hc] at hh
  simpa only [← hh] using G.zero_cost_growth (fun _ _ => 0) 1 hc x
/-- The full unrestricted-walk interpretation, including zero-length counting and
periodic growth, on the exact support and actual complex spectral radius. -/
theorem unrestricted_walk_laws (c : X → X → ℝ) (τ : ℝ) :
    (∀ n x, G.walkSum c τ n x = ((G.W c τ ^ n) *ᵥ (fun _ => 1)) x) ∧
    (∀ x, Tendsto (fun n : ℕ => Real.log (G.walkSum c τ n x) / (n : ℝ))
      atTop (𝓝 (Real.log (G.perron c τ).root))) ∧
    ((∀ i j, G.edge i j → c i j = 0) → ∀ n x,
      G.walkSum c τ n x = (Nat.card (G.Walks n x) : ℝ)) ∧
    (∀ x, Tendsto (fun n : ℕ => Real.log (Nat.card (G.Walks n x) : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log (spectralRadius ℂ (G.adjacency.map (algebraMap ℝ ℂ))).toReal))) := by
  exact ⟨G.walkSum_eq_matrix c τ, G.walk_growth c τ,
    fun hc => G.zero_cost_walkSum c τ hc, G.counting_entropy⟩
end D5.S3.Combinatorics.Graph.Pressure.Network
