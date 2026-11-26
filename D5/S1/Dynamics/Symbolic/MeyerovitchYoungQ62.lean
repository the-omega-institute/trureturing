/- GID: D5/S1/Dynamics/Symbolic/MeyerovitchYoungQ62
   generality: I
   mirror-B: D5/B/S1/Dynamics/Symbolic/MeyerovitchYoungQ62
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two finite primitive multigraphs give a nonempty aperiodic and nonsofic Equation (19) payoff shift. -/

/- admission_basis: escape-witness
   PrimitivePayoffSwitching.mechanical_cost_ge_boundary is consumed by the
   equal-endpoint minimum in shift_nonempty and by the all-endpoint estimate
   in shift_has_no_positive_period. The proof of result uses a two-sided
   cycle in every hypothetical nonempty finite presentation.
   edgeMinimum_iff transports attained minima through endpointWalkEquiv and
   is consumed by windowCondition_iff_equation19Window. The latter is used
   in both directions of shift_iff_equation19, which identifies the result's
   shift with the paper's inclusive two-sided interval condition.
   The counterexample concerns all interval lengths and all
   finite presentations and uses uniform real path estimates. -/

import D5.S1.Dynamics.Symbolic.PrimitivePayoffSwitching
import D5.S1.Dynamics.Symbolic.BiInfinitePayoffPeriodicity
import D5.S1.Words.Mechanical.SilverSlopeAbelianPeriodDefs

/-!
The edge-pair shift in Equation (19) of Meyerovitch–Young,
“Rationality and computability of the covering radius for sofic shifts.”

https://arxiv.org/html/2603.21449v1#S5.E19
https://arxiv.org/html/2603.21449v1#S6.Thmlemma2
-/

open scoped BigOperators
open D5.S1.Words.Mechanical
open PrimitivePayoffSwitching

set_option autoImplicit false

namespace MeyerovitchYoungQ62

noncomputable section

universe u v

abbrev GEdge := Bool × Bool
abbrev Alphabet := Bool × (Bool × Bool)

/-- H has two distinct self-loops on its sole vertex. The source and target
of a G edge are its first and second coordinates. -/
def hVertex (_ : Bool) : Unit := ()

def firstEdge {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

def lastEdge {n : ℕ} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

def WalkBetween {Vertex Edge : Type} (source target : Edge → Vertex)
    {n : ℕ} (hn : 0 < n) (s t : Vertex) (edges : Fin n → Edge) : Prop :=
  source (edges (firstEdge hn)) = s ∧
    target (edges (lastEdge hn)) = t ∧
    ∀ j k : Fin n, j.val + 1 = k.val → target (edges j) = source (edges k)

/-- Every positive length connects every ordered pair of vertices. Length
one supplies both irreducibility and a closed walk of length one. -/
def AllPositiveLengths {Vertex Edge : Type} (source target : Edge → Vertex) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (s t : Vertex),
    ∃ edges : Fin n → Edge, WalkBetween source target hn s t edges

private theorem firstEdge_castSucc {n : ℕ} (hn : 0 < n) :
    (firstEdge hn).castSucc = (0 : Fin (n + 1)) := by
  apply Fin.ext
  change 0 = (0 : Fin (n + 1)).val
  rw [Fin.val_zero]

private theorem lastEdge_succ {n : ℕ} (hn : 0 < n) :
    (lastEdge hn).succ = Fin.last n := by
  apply Fin.ext
  change n - 1 + 1 = n
  omega

private def edgesOfResponse {n : ℕ} (p : Response n) : Fin n → GEdge :=
  fun j => (p j.castSucc, p j.succ)

private theorem edgesOfResponse_walk {n : ℕ} (hn : 0 < n) {s t : Bool}
    (p : EndpointResponse n s t) :
    WalkBetween Prod.fst Prod.snd hn s t (edgesOfResponse p.val) := by
  constructor
  · change p.val (firstEdge hn).castSucc = s
    rw [firstEdge_castSucc]
    exact p.property.1
  constructor
  · change p.val (lastEdge hn).succ = t
    rw [lastEdge_succ]
    exact p.property.2
  · intro j k hjk
    have heq : j.succ = k.castSucc := Fin.ext hjk
    exact congrArg p.val heq

private def responseOfEdges {n : ℕ} (hn : 0 < n) (edges : Fin n → GEdge) : Response n :=
  fun j => if hj : j.val < n then (edges ⟨j.val, hj⟩).1 else (edges (lastEdge hn)).2

private theorem responseOfEdges_source {n : ℕ} (hn : 0 < n) (edges : Fin n → GEdge)
    (j : Fin n) : responseOfEdges hn edges j.castSucc = (edges j).1 := by
  change (if hj : j.val < n then (edges ⟨j.val, hj⟩).1 else (edges (lastEdge hn)).2) = _
  rw [dite_eq_left j.isLt]

private theorem responseOfEdges_target {n : ℕ} (hn : 0 < n) {s t : Bool}
    {edges : Fin n → GEdge} (hwalk : WalkBetween Prod.fst Prod.snd hn s t edges)
    (j : Fin n) : responseOfEdges hn edges j.succ = (edges j).2 := by
  change (if hj : j.val + 1 < n then (edges ⟨j.val + 1, hj⟩).1
    else (edges (lastEdge hn)).2) = _
  split
  next hj =>
    exact (hwalk.2.2 j ⟨j.val + 1, hj⟩ rfl).symm
  next hj =>
    have hlast : lastEdge hn = j := by
      apply Fin.ext
      change n - 1 = j.val
      have hjn := j.isLt
      omega
    rw [hlast]

/-- A contiguous G edge path with fixed endpoints is equivalent to a list
of its n + 1 vertices, including both endpoints. -/
def endpointWalkEquiv {n : ℕ} (hn : 0 < n) (s t : Bool) :
    EndpointResponse n s t ≃
      {edges : Fin n → GEdge // WalkBetween Prod.fst Prod.snd hn s t edges} where
  toFun p := ⟨edgesOfResponse p.val, edgesOfResponse_walk hn p⟩
  invFun edges := ⟨responseOfEdges hn edges.val, by
    constructor
    · rw [← firstEdge_castSucc hn, responseOfEdges_source]
      exact edges.property.1
    · rw [← lastEdge_succ hn, responseOfEdges_target hn edges.property]
      exact edges.property.2.1⟩
  left_inv p := by
    apply Subtype.ext
    funext j
    change responseOfEdges hn (edgesOfResponse p.val) j = p.val j
    by_cases hj : j.val < n
    · let k : Fin n := ⟨j.val, hj⟩
      calc
        responseOfEdges hn (edgesOfResponse p.val) j =
            responseOfEdges hn (edgesOfResponse p.val) k.castSucc :=
          congrArg (responseOfEdges hn (edgesOfResponse p.val)) (Fin.ext rfl)
        _ = (edgesOfResponse p.val k).1 :=
          responseOfEdges_source hn (edgesOfResponse p.val) k
        _ = p.val j := rfl
    · have hjlast : (lastEdge hn).succ = j := by
        apply Fin.ext
        change n - 1 + 1 = j.val
        have hjn := j.isLt
        omega
      change (if h : j.val < n then (edgesOfResponse p.val ⟨j.val, h⟩).1
        else (edgesOfResponse p.val (lastEdge hn)).2) = _
      rw [dite_eq_right hj]
      exact congrArg p.val hjlast
  right_inv edges := by
    apply Subtype.ext
    funext j
    apply Prod.ext
    · exact responseOfEdges_source hn edges.val j
    · exact responseOfEdges_target hn edges.property j

private theorem h_allPositiveLengths : AllPositiveLengths hVertex hVertex := by
  intro n hn s t
  cases s
  cases t
  exact ⟨fun _ => false, rfl, rfl, fun _ _ _ => rfl⟩

private theorem g_allPositiveLengths :
    AllPositiveLengths (Prod.fst : GEdge → Bool) Prod.snd := by
  intro n hn s t
  let p : Response n := fun j => if j.val = 0 then s else t
  have hstart : p 0 = s := by simp [p]
  have hfinish : p (Fin.last n) = t := by simp [p, Nat.ne_of_gt hn]
  let edges := endpointWalkEquiv hn s t ⟨p, hstart, hfinish⟩
  exact ⟨edges.val, edges.property⟩

def alpha : ℝ := silverSlope

private theorem alpha_bounds : 0 ≤ alpha ∧ alpha < 1 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  have hlo : (1 : ℝ) ≤ Real.sqrt 2 := by
    by_contra! h
    nlinarith only [hs, h, mul_nonneg hnonneg (sub_nonneg.mpr h.le)]
  have hhi : Real.sqrt 2 < 2 := by
    by_contra! h
    nlinarith only [hs, h, mul_nonneg hnonneg (sub_nonneg.mpr h)]
  unfold alpha silverSlope
  constructor <;> linarith only [hlo, hhi]

private theorem alpha_irrational : Irrational alpha := by
  simpa [alpha, silverSlope] using irrational_sqrt_two.sub_ratCast 1

/-- The real payoff takes the G edge first and the H edge second. -/
def payoff (edge : GEdge) (b : Bool) : ℝ :=
  PrimitivePayoffSwitching.payoff alpha b edge.1 edge.2

def edgeCost {n : ℕ} (a : Fin n → Bool) (edges : Fin n → GEdge) : ℝ :=
  ∑ j : Fin n, payoff (edges j) (a j)

private theorem edgeCost_eq_response_cost {n : ℕ} (hn : 0 < n) {s t : Bool}
    (a : Fin n → Bool)
    (edges : {edges : Fin n → GEdge // WalkBetween Prod.fst Prod.snd hn s t edges}) :
    edgeCost a edges.val = cost alpha a ((endpointWalkEquiv hn s t).symm edges).val := by
  let p := (endpointWalkEquiv hn s t).symm edges
  have he : edgesOfResponse p.val = edges.val :=
    congrArg Subtype.val ((endpointWalkEquiv hn s t).apply_symm_apply edges)
  calc
    edgeCost a edges.val = edgeCost a (edgesOfResponse p.val) :=
      congrArg (edgeCost a) he.symm
    _ = cost alpha a p.val := rfl

/-- Every H word of length n has the same two H endpoints. The particular G
edge block must achieve the minimum at its own endpoints. -/
def windowCondition {n : ℕ} (hn : 0 < n) (block : Fin n → Alphabet) : Prop :=
  let a : Fin n → Bool := fun j => (block j).1
  let edges : Fin n → GEdge := fun j => (block j).2
  Nonimprovable alpha hn a ∧
    ∃ s t : Bool, WalkBetween Prod.fst Prod.snd hn s t edges ∧
      edgeCost a edges = endpointMinimum alpha a hn s t

def blockAt (x : ℤ → Alphabet) (i : ℤ) (n : ℕ) : Fin n → Alphabet :=
  fun j => x (i + (j.val : ℤ))

/-- A length-n window at i includes i through i + n - 1. Thus n ≥ 2
parametrizes the paper's inclusive intervals with distinct endpoints. -/
def shift : Set (ℤ → Alphabet) :=
  {x | (∀ i : ℤ, (x i).2.2 = (x (i + 1)).2.1) ∧
    ∀ (i : ℤ) (n : ℕ) (hn : 2 ≤ n),
      windowCondition (show 0 < n by omega) (blockAt x i n)}

/-- Closedness in the product of discrete alphabets, expressed using the
basis of cylinders on finite intervals. -/
private theorem mem_of_all_windows_realized (x : ℤ → Alphabet)
    (h : ∀ (i : ℤ) (n : ℕ), 2 ≤ n →
      ∃ y ∈ shift, blockAt x i n = blockAt y i n) : x ∈ shift := by
  constructor
  · intro i
    obtain ⟨y, hy, heq⟩ := h i 2 (by decide)
    have hfirst := congrFun heq (0 : Fin 2)
    have hsecond := congrFun heq (1 : Fin 2)
    change x (i + 0) = y (i + 0) at hfirst
    change x (i + 1) = y (i + 1) at hsecond
    rw [add_zero] at hfirst
    rw [hfirst, hsecond]
    exact hy.1 i
  · intro i n hn
    obtain ⟨y, hy, heq⟩ := h i n hn
    change windowCondition (show 0 < n by omega) (blockAt x i n)
    rw [heq]
    exact hy.2 i n hn

private theorem translate_mem (x : ℤ → Alphabet) (hx : x ∈ shift) (k : ℤ) :
    (fun i : ℤ => x (k + i)) ∈ shift := by
  constructor
  · intro i
    simpa only [add_assoc] using hx.1 (k + i)
  · intro i n hn
    have hblock : blockAt (fun j => x (k + j)) i n = blockAt x (k + i) n := by
      funext j
      exact congrArg x (add_assoc k i (j.val : ℤ)).symm
    change windowCondition (show 0 < n by omega) (blockAt (fun j => x (k + j)) i n)
    rw [hblock]
    exact hx.2 (k + i) n hn

def mechanical (i : ℤ) : Bool :=
  decide (⌊((i + 1 : ℤ) : ℝ) * alpha⌋ - ⌊(i : ℝ) * alpha⌋ = (1 : ℤ))

private theorem mechanical_window_eq (i : ℤ) (n : ℕ) :
    (fun j : Fin n => mechanical (i + (j.val : ℤ))) =
      mechanicalWindow alpha ((i : ℝ) * alpha) 0 n := by
  funext j
  have h₀ : ((i + (j.val : ℤ) : ℤ) : ℝ) * alpha =
      (i : ℝ) * alpha + (j.val : ℝ) * alpha := by
    push_cast
    ring
  have h₁ : ((i + (j.val : ℤ) + 1 : ℤ) : ℝ) * alpha =
      (i : ℝ) * alpha + ((j.val + 1 : ℕ) : ℝ) * alpha := by
    push_cast
    ring
  change mechanical (i + (j.val : ℤ)) =
    lowerMechanicalWord alpha ((i : ℝ) * alpha) (0 + j.val)
  rw [Nat.zero_add]
  have hiff : mechanical (i + (j.val : ℤ)) = true ↔
      lowerMechanicalWord alpha ((i : ℝ) * alpha) j.val = true := by
    rw [lowerMechanicalWord_eq_true_iff]
    simp only [mechanical, decide_eq_true_eq, lowerMechanicalLetter, h₀, h₁]
  cases hl : mechanical (i + (j.val : ℤ)) <;>
    cases hr : lowerMechanicalWord alpha ((i : ℝ) * alpha) j.val <;> simp_all

private theorem shift_nonempty : shift.Nonempty := by
  refine ⟨fun i => (mechanical i, (true, true)), fun _ => rfl, ?_⟩
  intro i n hn
  have hn₀ : 0 < n := by omega
  let a : Fin n → Bool := fun j => mechanical (i + (j.val : ℤ))
  have ha : a = mechanicalWindow alpha ((i : ℝ) * alpha) 0 n := mechanical_window_eq i n
  let p : EndpointResponse n true true := ⟨fun _ => true, rfl, rfl⟩
  let e := endpointWalkEquiv hn₀ true true p
  have hc : edgeCost a e.val = cost alpha a p.val := by
    rw [edgeCost_eq_response_cost hn₀ a e]
    change cost alpha a ((endpointWalkEquiv hn₀ true true).symm
      (endpointWalkEquiv hn₀ true true p)).val = _
    rw [Equiv.symm_apply_apply]
  change Nonimprovable alpha hn₀ a ∧
    ∃ s t : Bool, WalkBetween Prod.fst Prod.snd hn₀ s t (fun _ => (true, true)) ∧
      edgeCost a (fun _ => (true, true)) = endpointMinimum alpha a hn₀ s t
  refine ⟨?_, true, true, e.property, ?_⟩
  · rw [ha]
    exact mechanical_nonimprovable alpha_bounds.1 alpha_bounds.2 hn₀ 0
  · change edgeCost a e.val = endpointMinimum alpha a hn₀ true true
    rw [hc, ha]
    exact (cost_constant alpha _ true).trans
      (mechanical_endpointMinimum_diagonal alpha_bounds.1 alpha_bounds.2 hn₀ 0 true).symm

private theorem shift_has_no_positive_period {x : ℤ → Alphabet} (hx : x ∈ shift) :
    ¬ ∃ period : ℤ, 0 < period ∧ Function.Periodic x period := by
  have hbound (i : ℤ) (n : ℕ) (hn : 2 ≤ n) :
      |(∑ j ∈ Finset.range n, ((x (i + (j : ℤ))).1.toNat : ℝ)) - (n : ℝ) * alpha| ≤ 7 := by
    let a : ℕ → Bool := fun j => (x (i + (j : ℤ))).1
    have hw : Nonimprovable alpha (show 0 < n by omega) (fun j : Fin n => a j.val) :=
      (hx.2 i n hn).1
    have h := nonimprovable_abs_discrepancy_le_seven alpha_bounds.1 alpha_bounds.2 hn _ hw
    rw [discrepancy_prefix_eq_sum_range alpha a n] at h
    exact h
  rintro ⟨period, hpos, hperiod⟩
  exact BiInfinitePayoffPeriodicity.no_positive_period_of_irrational_discrepancy
    (fun i => (x i).1) alpha_irrational hbound
    ⟨period, hpos, fun i => congrArg Prod.fst (hperiod i)⟩

/-- The primitive graphs H and G with the specified real payoff give a
nonempty two-sided shift in (19) with neither a periodic point nor a finite
labelled edge presentation. -/
theorem result :
    AllPositiveLengths hVertex hVertex ∧
    AllPositiveLengths (Prod.fst : GEdge → Bool) Prod.snd ∧
    (∀ (x : ℤ → Alphabet) (k : ℤ), x ∈ shift ↔ (fun i => x (k + i)) ∈ shift) ∧
    (∀ x : ℤ → Alphabet, (∀ (i : ℤ) (n : ℕ), 2 ≤ n →
      ∃ y ∈ shift, blockAt x i n = blockAt y i n) → x ∈ shift) ∧
    shift.Nonempty ∧
    ¬ (∃ x ∈ shift, ∃ period : ℤ, 0 < period ∧ Function.Periodic x period) ∧
    (∀ (Vertex : Type u) (Edge : Type v) [Finite Vertex] [Finite Edge]
      (source target : Edge → Vertex) (label : Edge → Alphabet),
      ¬ (∀ x : ℤ → Alphabet, x ∈ shift ↔
        ∃ walk : ℤ → Edge, (∀ i : ℤ, target (walk i) = source (walk (i + 1))) ∧
          ∀ i : ℤ, label (walk i) = x i)) := by
  have htranslate (x : ℤ → Alphabet) (k : ℤ) :
      x ∈ shift ↔ (fun i : ℤ => x (k + i)) ∈ shift := by
    refine ⟨fun hx => translate_mem x hx k, ?_⟩
    intro hx
    have h := translate_mem (fun i => x (k + i)) hx (-k)
    simpa only [← add_assoc, add_neg_cancel, zero_add] using h
  have hperiodic : ¬ (∃ x ∈ shift, ∃ period : ℤ, 0 < period ∧ Function.Periodic x period) := by
    rintro ⟨x, hx, h⟩
    exact shift_has_no_positive_period hx h
  refine ⟨h_allPositiveLengths, g_allPositiveLengths, htranslate, mem_of_all_windows_realized,
    shift_nonempty, hperiodic, ?_⟩
  intro Vertex Edge _ _ source target label hpresentation
  exact hperiodic (BiInfinitePayoffPeriodicity.exists_periodic_point_of_finite_edge_presentation
    source target label shift hpresentation shift_nonempty)

/-- The minimum in Section 4, expressed directly on G edge walks. -/
def IsEdgeMinimum {n : ℕ} (hn : 0 < n) (a : Fin n → Bool) (s t : Bool) (m : ℝ) : Prop :=
  (∃ edges, WalkBetween Prod.fst Prod.snd hn s t edges ∧ edgeCost a edges = m) ∧
    ∀ edges, WalkBetween Prod.fst Prod.snd hn s t edges → m ≤ edgeCost a edges

theorem edgeMinimum_iff {n : ℕ} (hn : 0 < n) (a : Fin n → Bool) (s t : Bool) (m : ℝ) :
    IsEdgeMinimum hn a s t m ↔ m = endpointMinimum alpha a hn s t := by
  obtain ⟨p, hp, hleast⟩ := endpointMinimum_spec alpha a hn s t
  let q := endpointWalkEquiv hn s t p
  have hq : edgeCost a q.val = endpointMinimum alpha a hn s t := by
    rw [edgeCost_eq_response_cost hn a q]
    simpa only [q, Equiv.symm_apply_apply] using hp
  have hqmin (edges : Fin n → GEdge) (hw : WalkBetween Prod.fst Prod.snd hn s t edges) :
      endpointMinimum alpha a hn s t ≤ edgeCost a edges := by
    rw [edgeCost_eq_response_cost hn a ⟨edges, hw⟩]
    exact hleast _
  constructor
  · rintro ⟨⟨edges, hw, heq⟩, hmin⟩
    exact le_antisymm ((hmin q.val q.property).trans_eq hq)
      ((hqmin edges hw).trans_eq heq)
  · rintro rfl
    exact ⟨⟨q.val, q.property, hq⟩, hqmin⟩

/-- The paper's nonimprovable H walks and the union of minimizing G responses
over all G vertex endpoint pairs, stated using edge walks. -/
def equation19Window {n : ℕ} (hn : 0 < n) (block : Fin n → Alphabet) : Prop :=
  let a : Fin n → Bool := fun j => (block j).1
  let edges : Fin n → GEdge := fun j => (block j).2
  (¬ ∃ v : Fin n → Bool,
    WalkBetween hVertex hVertex hn (hVertex (a (firstEdge hn))) (hVertex (a (lastEdge hn))) v ∧
      ∀ s t : Bool, ∃ old new : ℝ,
        IsEdgeMinimum hn a s t old ∧ IsEdgeMinimum hn v s t new ∧ old < new) ∧
    ∃ s t : Bool, WalkBetween Prod.fst Prod.snd hn s t edges ∧
      IsEdgeMinimum hn a s t (edgeCost a edges)

theorem windowCondition_iff_equation19Window {n : ℕ} (hn : 0 < n)
    (block : Fin n → Alphabet) :
    windowCondition hn block ↔ equation19Window hn block := by
  let a : Fin n → Bool := fun j => (block j).1
  have hstrict (v : Fin n → Bool) :
      StrictlyImproves alpha hn a v ↔
        ∀ s t : Bool, ∃ old new : ℝ,
          IsEdgeMinimum hn a s t old ∧ IsEdgeMinimum hn v s t new ∧ old < new := by
    constructor
    · intro h s t
      exact ⟨_, _, (edgeMinimum_iff hn a s t _).mpr rfl,
        (edgeMinimum_iff hn v s t _).mpr rfl, h s t⟩
    · intro h s t
      obtain ⟨old, new, hold, hnew, hlt⟩ := h s t
      rwa [(edgeMinimum_iff hn a s t old).mp hold, (edgeMinimum_iff hn v s t new).mp hnew] at hlt
  constructor
  · rintro ⟨hnon, s, t, hw, heq⟩
    refine ⟨?_, s, t, hw, (edgeMinimum_iff hn a s t _).mpr heq⟩
    rintro ⟨v, _, hv⟩
    exact hnon v ((hstrict v).mpr hv)
  · rintro ⟨hnon, s, t, hw, hmin⟩
    refine ⟨?_, s, t, hw, (edgeMinimum_iff hn a s t _).mp hmin⟩
    intro v hv
    exact hnon ⟨v, ⟨rfl, rfl, fun _ _ _ => rfl⟩, (hstrict v).mp hv⟩

/-- Equation (19) uses the inclusive interval with endpoints `m < n`. -/
def equation19 : Set (ℤ → Alphabet) :=
  {x | (∀ i : ℤ, hVertex (x i).1 = hVertex (x (i + 1)).1) ∧
    (∀ i : ℤ, (x i).2.2 = (x (i + 1)).2.1) ∧
    ∀ (m n : ℤ) (hmn : m < n),
      equation19Window (show 0 < (n - m + 1).toNat by omega)
        (blockAt x m (n - m + 1).toNat)}

theorem shift_iff_equation19 (x : ℤ → Alphabet) : x ∈ shift ↔ x ∈ equation19 := by
  constructor
  · intro hx
    refine ⟨fun _ => rfl, hx.1, ?_⟩
    intro m n hmn
    exact (windowCondition_iff_equation19Window _ _).mp
      (hx.2 m (n - m + 1).toNat (by omega))
  · rintro ⟨_, hwalk, hwindow⟩
    refine ⟨hwalk, ?_⟩
    intro i n hn
    let r : ℤ := i + (n : ℤ) - 1
    have hir : i < r := by dsimp [r]; omega
    have hlen : (r - i + 1).toNat = n := by dsimp [r]; omega
    have alignLength (length : ℕ) (heq : length = n) (hpos : 0 < length) :
        equation19Window hpos (blockAt x i length) →
          windowCondition (show 0 < n by omega) (blockAt x i n) := by
      subst length
      exact (windowCondition_iff_equation19Window _ _).mpr
    exact alignLength _ hlen _ (hwindow i r hir)

end

end MeyerovitchYoungQ62
