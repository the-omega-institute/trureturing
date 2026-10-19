/- GID: D5/S3/Combinatorics/Graph/Pressure/CyclePressure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/CyclePressure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual minimum support-cycle mean, maximum successor outdegree and zero-temperature pressure. -/
import D5.S3.Combinatorics.Graph.Pressure.WeightedWalks
import D5.S3.Combinatorics.Graph.LayeredCirculation.PositiveCircuitSupplier
import Mathlib.Data.Set.Finite.Lemmas

/-! Original-support cycle means and actual Perron pressure. -/
noncomputable section
open scoped BigOperators Matrix Topology
open Filter Matrix Maths Maths.AdditiveTransport Maths.MaxPlusPotential
namespace D5.S3.Combinatorics.Graph.Pressure.Network
universe u
variable {X : Type u} [Fintype X] [DecidableEq X] (G : Network X)

/-- Edges are precisely ordered pairs in the original support. -/
def SupportEdge := {e : X × X // G.edge e.1 e.2}
instance supportEdgeFintype : Fintype G.SupportEdge := by
  classical
  unfold SupportEdge
  infer_instance

def supportGraph : EdgeGraph X G.SupportEdge := ⟨fun e => e.1.1, fun e => e.1.2⟩

def edgeCost (c : X → X → ℝ) (e : G.SupportEdge) : ℝ := c e.1.1 e.1.2

def cycleMean (c : X → X → ℝ) {x : X} (w : G.supportGraph.Walk x x) : ℝ :=
  walkWeight (G.edgeCost c) w / w.length

private def supportWalk {x y : X}
    (p : @Quiver.Path X ⟨fun i j => PLift (G.edge i j)⟩ x y) : G.supportGraph.Walk x y := by
  induction p with
  | nil => exact .nil
  | @cons y z p e ih => exact .concat ih ⟨(y,z),e.down⟩ rfl

private theorem simpleCycle_exists :
    ∃ x, ∃ w : G.supportGraph.Walk x x, IsSimpleCycle w := by
  obtain ⟨x,y,h⟩ := G.hasEdge
  obtain ⟨p⟩ := G.connected y x
  let e : G.SupportEdge := ⟨(x,y),h⟩
  let w : G.supportGraph.Walk y y := (G.supportWalk p).concat e rfl
  obtain ⟨b,s,hs,_⟩ := exists_simpleCycle_cycleMeanDominates (fun _ : G.SupportEdge => (0 : ℝ)) w
    (by change 0 < (G.supportWalk p).length + 1; omega)
  exact ⟨b,s,hs⟩

/-- Construct a minimizing actual simple cycle from a finite nonempty set of actual means. -/
private theorem minimum_cycle_exists (c : X → X → ℝ) :
    ∃ x, ∃ w : G.supportGraph.Walk x x, IsSimpleCycle w ∧
      ∀ y (v : G.supportGraph.Walk y y), IsSimpleCycle v → G.cycleMean c w ≤ G.cycleMean c v := by
  classical
  let S : Set ℝ := {m | ∃ x, ∃ w : G.supportGraph.Walk x x, IsSimpleCycle w ∧ G.cycleMean c w = m}
  have hf : S.Finite := by
    have hL : ({l : List G.SupportEdge | l.length ≤ Fintype.card X} : Set (List G.SupportEdge)).Finite :=
      List.finite_length_le _ _
    apply (hL.image (fun l : List G.SupportEdge => (l.map (G.edgeCost c)).sum / l.length)).subset
    rintro m ⟨x,w,hw,rfl⟩
    exact ⟨w.edges, by simpa using hw.length_le_card, by simp [cycleMean,walkWeight]⟩
  have hn : S.Nonempty := by
    obtain ⟨x,w,hw⟩ := G.simpleCycle_exists
    exact ⟨G.cycleMean c w,x,w,hw,rfl⟩
  obtain ⟨m,⟨x,w,hw,hm⟩,hle⟩ := S.exists_min_image id hf hn
  refine ⟨x,w,hw,?_⟩
  intro y v hv
  have h := hle (G.cycleMean c v) ⟨y,v,hv,rfl⟩
  simpa [hm] using h

/-- The witness contains an actual original-support cycle, rather than a prescribed mean. -/
structure MinimumCycle (c : X → X → ℝ) where
  base : X
  walk : G.supportGraph.Walk base base
  simple : IsSimpleCycle walk
  least : ∀ y (v : G.supportGraph.Walk y y), IsSimpleCycle v → G.cycleMean c walk ≤ G.cycleMean c v

def minimumCycle (c : X → X → ℝ) : G.MinimumCycle c :=
  ⟨(G.minimum_cycle_exists c).choose, (G.minimum_cycle_exists c).choose_spec.choose,
    (G.minimum_cycle_exists c).choose_spec.choose_spec.1,
    (G.minimum_cycle_exists c).choose_spec.choose_spec.2⟩

def minimumCycleMean (c : X → X → ℝ) : ℝ := G.cycleMean c (G.minimumCycle c).walk

def outdegree (x : X) : ℕ := by
  classical
  exact Fintype.card {y // G.edge x y}

def maxOutdegree : ℕ := Finset.univ.sup G.outdegree

private theorem outdegree_le (x : X) : G.outdegree x ≤ G.maxOutdegree :=
  Finset.le_sup (f := G.outdegree) (Finset.mem_univ x)

private theorem maxOutdegree_spec :
    (∃ x, G.outdegree x = G.maxOutdegree) ∧ 1 ≤ G.maxOutdegree := by
  classical
  letI : Nonempty X := ⟨G.hasEdge.choose⟩
  obtain ⟨v,_,hv⟩ := Finset.exists_max_image Finset.univ G.outdegree Finset.univ_nonempty
  have hs : G.maxOutdegree ≤ G.outdegree v := Finset.sup_le fun i hi => hv i hi
  obtain ⟨i,j,hij⟩ := G.hasEdge
  have hp : 0 < G.outdegree i := by
    change 0 < Fintype.card {j // G.edge i j}
    exact Fintype.card_pos_iff.mpr ⟨⟨j,hij⟩⟩
  exact ⟨⟨v,le_antisymm (G.outdegree_le v) hs⟩,
    Nat.succ_le_iff.mpr (lt_of_lt_of_le hp (G.outdegree_le i))⟩

/-- Apply the original one-sided potential supplier with weight=-cost and level=-minimum. -/
private theorem minimizing_potential (c : X → X → ℝ) :
    ∃ φ : X → ℝ, ∀ i j, G.edge i j →
      -c i j + φ i - φ j ≤ -G.minimumCycleMean c := by
  have hs : ∀ x, ∀ w : G.supportGraph.Walk x x, IsSimpleCycle w →
      walkWeight (fun e => -G.edgeCost c e) w ≤ w.length * (-G.minimumCycleMean c) := by
    intro x w hw
    have hmin := (G.minimumCycle c).least x w hw
    have hp : (0 : ℝ) < w.length := by exact_mod_cast hw.1
    have hcost : G.minimumCycleMean c * w.length ≤ walkWeight (G.edgeCost c) w := by
      exact (le_div_iff₀ hp).mp hmin
    have hn : walkWeight (fun e => -G.edgeCost c e) w = -walkWeight (G.edgeCost c) w := by
      simpa only [walkWeight, List.map_map, Function.comp_def] using
        (List.sum_neg (w.edges.map (G.edgeCost c))).symm
    rw [hn]
    nlinarith
  have hall := (forall_closedWalk_mean_le_iff_simpleCycle
    (G := G.supportGraph) (fun e => -G.edgeCost c e) (-G.minimumCycleMean c)).mpr hs
  obtain ⟨φ,hφ⟩ := (worstDirectedResidualAtMost_iff_closedWalk_le G.supportGraph
    (fun e => -G.edgeCost c e) (-G.minimumCycleMean c)).mpr hall
  refine ⟨φ,?_⟩
  intro i j hij
  simpa [defect,supportGraph,edgeCost,add_comm] using hφ ⟨(i,j),hij⟩

/-- The selected mean is minimal over every nonempty closed walk, including repetitions. -/
private theorem minimum_cycle_all_closed (c : X → X → ℝ) (x : X)
    (w : G.supportGraph.Walk x x) (hw : 0 < w.length) :
    G.minimumCycleMean c ≤ G.cycleMean c w := by
  obtain ⟨φ,hφ⟩ := G.minimizing_potential c
  have hh : WorstDirectedResidualAtMost G.supportGraph (fun e => -G.edgeCost c e)
      (-G.minimumCycleMean c) := by
    refine ⟨φ,?_⟩
    intro e
    simpa [defect,supportGraph,edgeCost,add_comm] using hφ e.1.1 e.1.2 e.2
  have h := (worstDirectedResidualAtMost_iff_closedWalk_le G.supportGraph _ _).mp hh x w
  have hn : walkWeight (fun e => -G.edgeCost c e) w = -walkWeight (G.edgeCost c) w := by
    simpa only [walkWeight, List.map_map, Function.comp_def] using
      (List.sum_neg (w.edges.map (G.edgeCost c))).symm
  rw [hn] at h
  apply (le_div_iff₀ (show (0 : ℝ) < w.length by exact_mod_cast hw)).mpr
  change G.minimumCycleMean c * (w.length : ℝ) ≤ _
  nlinarith

private theorem perron_edge_le (c : X → X → ℝ) (τ : ℝ) (i j : X) (hij : G.edge i j) :
    Real.exp (-c i j / τ) * (G.perron c τ).right j ≤
      (G.perron c τ).root * (G.perron c τ).right i := by
  have h := Finset.single_le_sum
    (f := fun j => G.W c τ i j * (G.perron c τ).right j)
    (fun j _ => mul_nonneg (G.W_nonneg c τ i j) ((G.perron c τ).right_pos j).le)
    (Finset.mem_univ j)
  have he := congrFun (G.perron c τ).eigen i
  simpa [Matrix.mulVec,dotProduct,W,hij] using h.trans_eq he

/-- Multiply actual Perron row inequalities along an unrestricted support walk. -/
private theorem perron_walk_le (c : X → X → ℝ) (τ : ℝ) (hτ : 0 < τ) {x y : X}
    (w : G.supportGraph.Walk x y) :
    Real.exp (-walkWeight (G.edgeCost c) w / τ) * (G.perron c τ).right y ≤
      (G.perron c τ).root ^ w.length * (G.perron c τ).right x := by
  let lam := (G.perron c τ).root
  let r := (G.perron c τ).right
  let weight : G.SupportEdge → ℝ :=
    fun e => -G.edgeCost c e - τ * Real.log lam
  let potential : X → ℝ := fun i => -τ * Real.log (r i)
  have hpotential : Maths.MaxPlusPotential.IsPotential G.supportGraph weight potential := by
    intro e
    have he := G.perron_edge_le c τ e.1.1 e.1.2 e.2
    have hlog := Real.log_le_log
      (mul_pos (Real.exp_pos _) ((G.perron c τ).right_pos e.1.2)) he
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _))
          (ne_of_gt ((G.perron c τ).right_pos e.1.2)),
      Real.log_mul (ne_of_gt ((G.perron c τ).root_pos))
          (ne_of_gt ((G.perron c τ).right_pos e.1.1)),
      Real.log_exp] at hlog
    dsimp [weight, potential]
    have hlog'' : -c e.1.1 e.1.2 / τ ≤
        Real.log (G.perron c τ).root +
          Real.log ((G.perron c τ).right e.1.1) -
          Real.log ((G.perron c τ).right e.1.2) := by
      linarith [hlog]
    have hlog' : -G.edgeCost c e / τ ≤
        Real.log lam + Real.log (r e.1.1) - Real.log (r e.1.2) := by
      simpa [lam, r, edgeCost] using hlog''
    have hmul := (div_le_iff₀ hτ).mp hlog'
    change -τ * Real.log (r e.1.1) +
      (-G.edgeCost c e - τ * Real.log lam) ≤ -τ * Real.log (r e.1.2)
    nlinarith
  have hwalk := Maths.MaxPlusPotential.IsPotential.walkWeight_add_le hpotential w
  have hsum := Maths.MaxPlusPotential.walkWeight_sub_const
    (G := G.supportGraph) (fun e => -G.edgeCost c e) (τ * Real.log lam) w
  have hn : walkWeight (fun e => -G.edgeCost c e) w =
      -walkWeight (G.edgeCost c) w := by
    simpa only [Maths.MaxPlusPotential.walkWeight, List.map_map, Function.comp_def] using
      (List.sum_neg (w.edges.map (G.edgeCost c))).symm
  dsimp [weight, potential] at hwalk
  rw [hsum, hn] at hwalk
  simp only [nsmul_eq_mul] at hwalk
  have hlog' :
      -walkWeight (G.edgeCost c) w / τ ≤
        (w.length : ℝ) * Real.log lam + Real.log (r x) - Real.log (r y) := by
    apply (div_le_iff₀ hτ).2
    nlinarith
  have hlog :
      -walkWeight (G.edgeCost c) w / τ + Real.log (r y) ≤
        (w.length : ℝ) * Real.log lam + Real.log (r x) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  calc
    Real.exp (-walkWeight (G.edgeCost c) w / τ) * (G.perron c τ).right y =
        Real.exp (-walkWeight (G.edgeCost c) w / τ + Real.log (r y)) := by
          rw [Real.exp_add, Real.exp_log ((G.perron c τ).right_pos y)]
    _ ≤ Real.exp ((w.length : ℝ) * Real.log lam + Real.log (r x)) := hexp
    _ = lam ^ w.length * r x := by
      have hlogpow : Real.log (lam ^ w.length * r x) =
          (w.length : ℝ) * Real.log lam + Real.log (r x) := by
        rw [Real.log_mul (ne_of_gt (pow_pos ((G.perron c τ).root_pos) w.length))
          (ne_of_gt ((G.perron c τ).right_pos x)), Real.log_pow]
      rw [← hlogpow, Real.exp_log]
      exact mul_pos (pow_pos ((G.perron c τ).root_pos) w.length) ((G.perron c τ).right_pos x)
set_option maxHeartbeats 3000000 in
/-- The original-support cycle minimum and actual successor maximum give the exact bracket. -/
private theorem pressure_bracket (c : X → X → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    G.minimumCycleMean c - τ * Real.log (G.maxOutdegree : ℝ) ≤
      -τ * Real.log (G.perron c τ).root ∧
    -τ * Real.log (G.perron c τ).root ≤ G.minimumCycleMean c := by
  classical
  letI : Nonempty X := ⟨G.hasEdge.choose⟩
  let r := (G.perron c τ).right
  let lam := (G.perron c τ).root
  let m := G.minimumCycleMean c
  have hl : 0 < lam := (G.perron c τ).root_pos
  obtain ⟨φ,hφ⟩ := G.minimizing_potential c
  let z : X → ℝ := fun x => Real.exp (-φ x / τ)
  let a := Real.exp (-m / τ)
  have hz : ∀ i, 0 < z i := fun i => Real.exp_pos _
  have ha : 0 < a := Real.exp_pos _
  have hterm (i j : X) (hij : G.edge i j) : G.W c τ i j * z j ≤ a * z i := by
    have he : (-c i j / τ + -φ j / τ) ≤ -m / τ + -φ i / τ := by
      have hd := div_le_div_of_nonneg_right (hφ i j hij) hτ.le
      rw [sub_div, add_div] at hd
      dsimp [m]
      simp only [neg_div] at hd ⊢
      linarith
    simpa [W,hij,z,a,← Real.exp_add] using Real.exp_le_exp.mpr he
  have hrow (i : X) : (G.W c τ *ᵥ z) i ≤ (G.maxOutdegree : ℝ) * a * z i := by
    have hsum : (G.W c τ *ᵥ z) i = ∑ j : {j // G.edge i j}, G.W c τ i j.1 * z j.1 := by
      simp only [Matrix.mulVec,dotProduct]
      apply Finset.sum_congr_set {j | G.edge i j}
      · intro j hj; rfl
      · intro j hj
        change ¬G.edge i j at hj
        simp [W, hj]
    rw [hsum]
    calc
      _ ≤ ∑ _j : {j // G.edge i j}, a * z i := Finset.sum_le_sum fun j _ => hterm i j.1 j.2
      _ = (G.outdegree i : ℝ) * a * z i := by simp [outdegree] <;> ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by exact_mod_cast G.outdegree_le i) ha.le) (hz i).le
  obtain ⟨v,_,hv⟩ := Finset.exists_max_image Finset.univ (fun x => r x / z x) Finset.univ_nonempty
  let R := r v / z v
  have hR : 0 < R := div_pos ((G.perron c τ).right_pos v) (hz v)
  have hrv : r v = R * z v := by dsimp [R]; field_simp [ne_of_gt (hz v)]
  have hr (i : X) : r i ≤ R * z i := (div_le_iff₀ (hz i)).mp (hv i (Finset.mem_univ i))
  have hu : lam ≤ (G.maxOutdegree : ℝ) * a := by
    have he : lam * r v = (G.W c τ *ᵥ r) v := (congrFun (G.perron c τ).eigen v).symm
    have hb : lam * r v ≤ ((G.maxOutdegree : ℝ) * a) * r v := by
      rw [he]
      calc
        _ ≤ R * (G.W c τ *ᵥ z) v := by
          simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          calc
            _ ≤ G.W c τ v i * (R * z i) := mul_le_mul_of_nonneg_left (hr i) (G.W_nonneg c τ v i)
            _ = _ := by ring
        _ ≤ R * ((G.maxOutdegree : ℝ) * a * z v) := mul_le_mul_of_nonneg_left (hrow v) hR.le
        _ = _ := by rw [hrv]; ring
    exact (mul_le_mul_iff_left₀ ((G.perron c τ).right_pos v)).mp hb
  have hd : 0 < (G.maxOutdegree : ℝ) := by
    have : 0 < (G.maxOutdegree : ℝ) * a := lt_of_lt_of_le hl hu
    exact (mul_pos_iff_of_pos_right ha).mp this
  have hlogU : Real.log lam ≤ Real.log (G.maxOutdegree : ℝ) - m / τ := by
    have hh := Real.log_le_log hl hu
    rw [Real.log_mul (ne_of_gt hd) (ne_of_gt ha)] at hh
    change Real.log lam ≤ Real.log (G.maxOutdegree : ℝ) + Real.log (Real.exp (-m / τ)) at hh
    rw [Real.log_exp, neg_div] at hh
    simpa only [sub_eq_add_neg] using hh
  let C := G.minimumCycle c
  have hC : 0 < C.walk.length := C.simple.1
  have hCR : (0 : ℝ) < C.walk.length := by exact_mod_cast hC
  have hw := G.perron_walk_le c τ hτ C.walk
  have hc : Real.exp (-walkWeight (G.edgeCost c) C.walk / τ) ≤ lam ^ C.walk.length :=
    (mul_le_mul_iff_left₀ ((G.perron c τ).right_pos C.base)).mp hw
  have hlogL := Real.log_le_log (Real.exp_pos _) hc
  rw [Real.log_exp, Real.log_pow] at hlogL
  have hm : walkWeight (G.edgeCost c) C.walk = (C.walk.length : ℝ) * m := by
    have hh : m = walkWeight (G.edgeCost c) C.walk / C.walk.length := rfl
    have hh' := (eq_div_iff (ne_of_gt hCR)).mp hh
    linarith
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlogU hτ.le
    dsimp [lam,m] at *
    have ht : τ ≠ 0 := ne_of_gt hτ
    field_simp [ht] at hh
    nlinarith
  · rw [hm] at hlogL
    have hh := mul_le_mul_of_nonneg_left hlogL hτ.le
    have ht : τ ≠ 0 := ne_of_gt hτ
    field_simp [ht] at hh
    apply (mul_le_mul_iff_right₀ hCR).mp
    change (C.walk.length : ℝ) * (-τ * Real.log lam) ≤ (C.walk.length : ℝ) * m
    nlinarith [hh]

/-- Right-hand zero-temperature limit of the actual pressure, with no supplied bracket. -/
private theorem zero_temperature (c : X → X → ℝ) :
    Tendsto (fun τ : ℝ => -τ * Real.log (G.perron c τ).root)
      (𝓝[>] 0) (𝓝 (G.minimumCycleMean c)) := by
  have hL : Tendsto (fun τ : ℝ => G.minimumCycleMean c - τ * Real.log (G.maxOutdegree : ℝ))
      (𝓝[>] 0) (𝓝 (G.minimumCycleMean c)) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left inf_le_left
    simpa only [zero_mul, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => G.minimumCycleMean c)
        (𝓝[>] (0 : ℝ)) (𝓝 (G.minimumCycleMean c))).sub
        (ht.mul_const (Real.log (G.maxOutdegree : ℝ)))
  have hU : Tendsto (fun _ : ℝ => G.minimumCycleMean c) (𝓝[>] 0) (𝓝 (G.minimumCycleMean c)) :=
    tendsto_const_nhds
  have hb : ∀ᶠ τ : ℝ in 𝓝[>] 0,
      G.minimumCycleMean c - τ * Real.log (G.maxOutdegree : ℝ) ≤ -τ * Real.log (G.perron c τ).root ∧
      -τ * Real.log (G.perron c τ).root ≤ G.minimumCycleMean c := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact G.pressure_bracket c τ hτ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
/-- Uniform actual-cycle pressure law. The minimizing cycle is constructed, the
minimum ranges over every nonempty support closed walk, and the degree is the
maximum of the actual successor cardinalities. No potential or bracket is a premise. -/
theorem cycle_pressure_laws (c : X → X → ℝ) :
    (∃ x, ∃ w : G.supportGraph.Walk x x, IsSimpleCycle w ∧
      G.cycleMean c w = G.minimumCycleMean c) ∧
    (∀ x, ∀ w : G.supportGraph.Walk x x, 0 < w.length →
      G.minimumCycleMean c ≤ G.cycleMean c w) ∧
    ((∃ x, G.outdegree x = G.maxOutdegree) ∧ 1 ≤ G.maxOutdegree) ∧
    (∀ τ : ℝ, 0 < τ →
      G.minimumCycleMean c - τ * Real.log (G.maxOutdegree : ℝ) ≤ -τ * Real.log (G.perron c τ).root ∧
      -τ * Real.log (G.perron c τ).root ≤ G.minimumCycleMean c) ∧
    Tendsto (fun τ : ℝ => -τ * Real.log (G.perron c τ).root)
      (𝓝[>] 0) (𝓝 (G.minimumCycleMean c)) := by
  exact ⟨⟨(G.minimumCycle c).base, (G.minimumCycle c).walk, (G.minimumCycle c).simple, rfl⟩,
    G.minimum_cycle_all_closed c, G.maxOutdegree_spec, G.pressure_bracket c, G.zero_temperature c⟩
end D5.S3.Combinatorics.Graph.Pressure.Network
