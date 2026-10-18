/- GID: D5/S3/Combinatorics/Graph/Pressure/PerronDoob
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/PerronDoob
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual weighted adjacency Perron data and supported stationary Doob kernel. -/
import D5.S3.Combinatorics.Graph.PerronFrobenius.MCMCSupplier.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing

/-! Finite weighted graph pressure on the original support. -/
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

def Qstar (c : X → X → ℝ) (τ : ℝ) : Matrix X X ℝ :=
  fun i j => G.W c τ i j * (G.perron c τ).right j /
    ((G.perron c τ).root * (G.perron c τ).right i)

lemma Qstar_nonneg (c : X → X → ℝ) (τ : ℝ) (i j : X) : 0 ≤ G.Qstar c τ i j :=
  div_nonneg (mul_nonneg (G.W_nonneg c τ i j) ((G.perron c τ).right_pos j).le)
    (mul_pos (G.perron c τ).root_pos ((G.perron c τ).right_pos i)).le

lemma Qstar_pos_iff (c : X → X → ℝ) (τ : ℝ) (i j : X) :
    0 < G.Qstar c τ i j ↔ G.edge i j := by
  rw [Qstar,div_pos_iff_of_pos_right (mul_pos (G.perron c τ).root_pos ((G.perron c τ).right_pos i)),
    mul_pos_iff_of_pos_right ((G.perron c τ).right_pos j),G.W_pos_iff]

lemma Qstar_rowsum (c : X → X → ℝ) (τ : ℝ) (i : X) : ∑ j, G.Qstar c τ i j = 1 := by
  classical
  simp only [Qstar,← Finset.sum_div]
  change (G.W c τ *ᵥ (G.perron c τ).right) i / _ = 1
  rw [(G.perron c τ).eigen]
  exact div_self (mul_ne_zero (ne_of_gt (G.perron c τ).root_pos)
    (ne_of_gt ((G.perron c τ).right_pos i)))

/-- All admissible stationary pairs, allowing zero masses and zero transition entries. -/
structure StationaryPair where
  π : X → ℝ
  Q : Matrix X X ℝ
  nonnegπ : ∀ i, 0 ≤ π i
  sumπ : ∑ i, π i = 1
  nonnegQ : ∀ i j, 0 ≤ Q i j
  sumQ : ∀ i, ∑ j, Q i j = 1
  supported : ∀ i j, ¬G.edge i j → Q i j = 0
  stationary : ∀ j, ∑ i, π i * Q i j = π j

/-- Finite stationary existence is used on the actual row-stochastic Doob kernel;
no primitivity or aperiodicity premise is used. -/
theorem exists_stationary_doob (c : X → X → ℝ) (τ : ℝ) :
    ∃ p : G.StationaryPair, p.Q = G.Qstar c τ := by
  classical
  letI : Nonempty X := ⟨G.hasEdge.choose⟩
  letI : D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing.RowStochastic
      (G.Qstar c τ) := ⟨fun i => ⟨G.Qstar_nonneg c τ i,G.Qstar_rowsum c τ i⟩⟩
  obtain ⟨π,hπ,hs⟩ :=
    D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing.stationary_distribution_exists
      (G.Qstar c τ)
  refine ⟨⟨π,G.Qstar c τ,hπ.nonneg,hπ.rowsum,G.Qstar_nonneg c τ,G.Qstar_rowsum c τ,?_,?_⟩,rfl⟩
  · intro i j h
    exact le_antisymm (le_of_not_gt (by simpa [G.Qstar_pos_iff] using h)) (G.Qstar_nonneg c τ i j)
  · intro j
    exact congrFun hs.stationary j
end Network
end D5.S3.Combinatorics.Graph.Pressure
