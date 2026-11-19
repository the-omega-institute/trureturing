/- GID: D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/MarkovAdditiveCycles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported directed closed-walk obstruction and global pressure dichotomy. -/
import D5.S3.Combinatorics.Graph.Pressure.MarkovAdditiveGlobal
import D5.S3.Combinatorics.Graph.Pressure.CyclePressure

/-! # The directed closed-walk obstruction to strict pressure curvature -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix Topology
open Matrix Maths Maths.MaxPlusPotential

namespace D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

/-- A common mean on every supported directed closed walk of positive length. -/
def CommonClosedWalkMean (P : Matrix V V ℝ) (hI : P.IsIrreducible)
    (g : V → V → ℝ) : Prop :=
  ∃ c : ℝ, ∀ i, ∀ w : (supportNetwork P hI).supportGraph.Walk i i,
    0 < w.length → walkWeight ((supportNetwork P hI).edgeCost g) w = (w.length : ℝ) * c

theorem coboundary_iff_closedWalkMean (P : Matrix V V ℝ) (hI : P.IsIrreducible)
    (g : V → V → ℝ) :
    (∃ c : ℝ, ∃ f : V → ℝ, ∀ i j, 0 < P i j → g i j = c + f i - f j) ↔
      CommonClosedWalkMean P hI g := by
  let G := supportNetwork P hI
  constructor
  · rintro ⟨c, f, hf⟩
    have ht {i j : V} (w : G.supportGraph.Walk i j) :
        walkWeight (G.edgeCost g) w = (w.length : ℝ)*c + f i - f j := by
      induction w with
      | nil => simp [walkWeight]
      | @concat j w e he ih =>
        rw [walkWeight_concat, ih]
        have hh : g e.1.1 e.1.2 = c + f e.1.1 - f e.1.2 := hf _ _ e.2
        change (w.length : ℝ)*c + f _ - f j + g e.1.1 e.1.2 = _
        have hj : e.1.1 = j := he
        simp only [EdgeGraph.Walk.length_concat, Nat.cast_add, Nat.cast_one]
        change _ = ((w.length : ℝ)+1)*c + f _ - f e.1.2
        rw [hh, hj]
        ring
    refine ⟨c, fun i w _ => ?_⟩
    simpa using ht w
  · rintro ⟨c, hc⟩
    let weight : G.SupportEdge → ℝ := fun e => G.edgeCost g e - c
    have hz (i : V) (w : G.supportGraph.Walk i i) : walkWeight weight w = 0 := by
      by_cases hp : 0 < w.length
      · dsimp only [weight]
        rw [walkWeight_sub_const, hc i w hp, nsmul_eq_mul, sub_self]
      · have hlen : w.length = 0 := by omega
        have hel : w.edges = [] := List.length_eq_zero_iff.mp (w.edges_length.trans hlen)
        simp [walkWeight, hel]
    obtain ⟨φ, hφ⟩ := (exists_isPotential_iff_forall_closedWalk_nonpos
      (G := G.supportGraph) weight).mpr (fun i w => (hz i w).le)
    have hn (i : V) (w : G.supportGraph.Walk i i) : walkWeight (fun e => -weight e) w = 0 := by
      have hh : walkWeight (fun e => -weight e) w = -walkWeight weight w := by
        simpa only [walkWeight, List.map_map, Function.comp_def] using
          (List.sum_neg (w.edges.map weight)).symm
      rw [hh, hz, neg_zero]
    obtain ⟨ψ, hψ⟩ := (exists_isPotential_iff_forall_closedWalk_nonpos
      (G := G.supportGraph) (fun e => -weight e)).mpr (fun i w => (hn i w).le)
    have hedge (i j : V) (hij : 0 < P i j) : φ i + ψ i ≤ φ j + ψ j := by
      have hp := hφ ⟨(i,j), hij⟩
      have hq := hψ ⟨(i,j), hij⟩
      change φ i + weight ⟨(i,j), hij⟩ ≤ φ j at hp
      change ψ i + -weight ⟨(i,j), hij⟩ ≤ ψ j at hq
      linarith
    have along {i j : V} (p : @Quiver.Path V (Matrix.toQuiver P) i j) :
        φ i + ψ i ≤ φ j + ψ j := by
      induction p with
      | nil => exact le_rfl
      | cons p e ih => exact ih.trans (hedge _ _ e.down)
    refine ⟨c, fun i => -φ i, ?_⟩
    intro i j hij
    have hp := hφ ⟨(i,j), hij⟩
    have hq := hψ ⟨(i,j), hij⟩
    change φ i + (g i j-c) ≤ φ j at hp
    change ψ i + -(g i j-c) ≤ ψ j at hq
    obtain ⟨p, _⟩ := hI.connected j i
    have hh := along p
    linarith

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

/-- The scalar pressure is either globally linear with unchanged Doob kernel, or has
strictly positive curvature everywhere; the exact obstruction is common cycle mean. -/
theorem pressure_cycle_dichotomy (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) :
    pressure P g 0 = 0 ∧ ContDiff ℝ 2 (pressure P g) ∧
      (π.varianceRate hP hI g = 0 ↔ CommonClosedWalkMean P hI g) ∧
      ((CommonClosedWalkMean P hI g → ∀ t,
          pressure P g t = t * π.meanReward g ∧ π.globalDoob hI g t = P) ∧
        (¬ CommonClosedWalkMean P hI g → ∀ t, 0 < deriv (deriv (pressure P g)) t)) := by
  have he := coboundary_iff_closedWalkMean P hI g
  refine ⟨pressure_zero hP hI g, π.pressure_contDiff hI g,
    (π.varianceRate_eq_zero_iff_coboundary hP hI g).trans he,
    ?_, ?_⟩
  · intro hc t
    obtain ⟨c, f, hf⟩ := he.mpr hc
    have hg := π.coboundary_global hP hI g c f hf t
    have hm : π.meanReward g = c := by
      have hp := π.pressure_hasDerivAt_zero hP hI g
      have hf : pressure P g = fun t => t*c :=
        funext fun t => (π.coboundary_global hP hI g c f hf t).1
      rw [hf] at hp
      exact hp.unique (by simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c))
    simpa [hm] using hg
  · intro hc t
    exact π.pressure_strict_curvature hI g (fun h => hc (he.mp h)) t

end Stationary
end D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
