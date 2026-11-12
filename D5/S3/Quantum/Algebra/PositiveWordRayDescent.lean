/- GID: D5/S3/Quantum/Algebra/PositiveWordRayDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PositiveWordRayDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=structural
   digest: Sequential ready return controls all positive-word prediction fibers. -/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-! Full supremum prediction rows for chronological positive eleven-address words. -/

@[expose] public section

namespace D5.S3.Quantum.Algebra.PositiveWordRayDescent

open Set Filter Topology
noncomputable section

abbrev Word := List (Fin 11)
abbrev Coordinate := Option Word
instance : TopologicalSpace Coordinate := ⊥
instance : DiscreteTopology Coordinate := ⟨rfl⟩
abbrev Row := Coordinate →ᵇ ℝ

structure Law where
  probability : Word → ℝ
  bounds : ∀ a, probability a ∈ Icc (0 : ℝ) 1

def Law.value (L : Law) (a : Word) : Coordinate → ℝ
  | none => 1
  | some f => L.probability (a ++ f)

private theorem value_bounds (L : Law) (a : Word) (i : Coordinate) :
    L.value a i ∈ Icc (0 : ℝ) 1 := by
  cases i with
  | none => exact ⟨by norm_num [Law.value], by simp [Law.value]⟩
  | some f => exact L.bounds (a ++ f)

def Law.row (L : Law) (a : Word) : Row :=
  BoundedContinuousFunction.mkOfDiscrete (L.value a) 1 (by
    intro i j
    rw [Real.dist_eq, abs_sub_le_iff]
    have hi := value_bounds L a i
    have hj := value_bounds L a j
    constructor <;> linarith [hi.1, hi.2, hj.1, hj.2])

def Law.closedSpan (L : Law) : Submodule ℝ Row :=
  (Submodule.span ℝ (range L.row)).topologicalClosure

def Law.R10 (L : Law) : Prop :=
  ∀ (a : Word) (j : Fin 11) (f : Word),
    L.probability (a ++ List.replicate 10 j ++ f) = L.probability (a ++ f)

/-- Reverse chronological order, with nine positive copies of each address. -/
def inverseWord : Word → Word
  | [] => []
  | j :: b => inverseWord b ++ List.replicate 9 j

private theorem cancel_statistics (L : Law) (h : L.R10) (a b f : Word) :
    L.probability (a ++ b ++ inverseWord b ++ f) = L.probability (a ++ f) := by
  induction b generalizing a f with
  | nil => simp [inverseWord]
  | cons j b ih =>
    calc
      _ = L.probability ((a ++ [j]) ++ b ++ inverseWord b ++
          (List.replicate 9 j ++ f)) := by simp [inverseWord, List.append_assoc]
      _ = L.probability ((a ++ [j]) ++ (List.replicate 9 j ++ f)) := ih _ _
      _ = L.probability (a ++ List.replicate 10 j ++ f) := by
        simp [List.replicate_succ, List.append_assoc]
      _ = _ := h a j f

private theorem cancel_rows (L : Law) (h : L.R10) (a b : Word) :
    L.row (a ++ b ++ inverseWord b) = L.row a := by
  apply BoundedContinuousFunction.ext
  intro i
  cases i with
  | none => rfl
  | some f => exact cancel_statistics L h a b f

private theorem row_contraction (L : Law) (a b c : Word) :
    dist (L.row (a ++ c)) (L.row (b ++ c)) ≤ dist (L.row a) (L.row b) := by
  apply (BoundedContinuousFunction.dist_le dist_nonneg).2
  intro i
  cases i with
  | none => simp [Law.row, Law.value]
  | some f =>
    simpa [Law.row, Law.value, List.append_assoc] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := L.row a) (g := L.row b)
        (some (c ++ f)))

private theorem row_isometry (L : Law) (h : L.R10) (a b c : Word) :
    dist (L.row (a ++ c)) (L.row (b ++ c)) = dist (L.row a) (L.row b) := by
  apply le_antisymm (row_contraction L a b c)
  simpa only [← List.append_assoc, cancel_rows L h] using
    row_contraction L (a ++ c) (b ++ c) (inverseWord c)

/-- Statistical periodicity supplies simultaneous positive-word transport of both rows. -/
theorem row_return_transport (L : Law) (h : L.R10) (a b : Word) :
    dist (L.row a) (L.row b) = dist (L.row (a ++ inverseWord b)) (L.row []) := by
  rw [← row_isometry L h a b (inverseWord b)]
  have hb := cancel_rows L h [] b
  simpa using hb ▸ (rfl : dist (L.row (a ++ inverseWord b))
    (L.row (b ++ inverseWord b)) = dist (L.row (a ++ inverseWord b))
      (L.row (b ++ inverseWord b)))

/-- Geometry inputs are independent of the statistical law. -/
structure Geometry (R : Type*) [MetricSpace R] where
  gate : Fin 11 → R → R
  isometry_gate : ∀ j, Isometry (gate j)
  period : ∀ j P, (gate j)^[10] P = P
  ready : R

variable {R : Type*} [MetricSpace R]

def Geometry.act (G : Geometry R) : Word → R → R
  | [], P => P
  | j :: b, P => G.act b (G.gate j P)

def Geometry.ray (G : Geometry R) (a : Word) : R := G.act a G.ready

private theorem act_append (G : Geometry R) (a b : Word) (P : R) :
    G.act (a ++ b) P = G.act b (G.act a P) := by
  induction a generalizing P with
  | nil => rfl
  | cons j a ih => exact ih _

private theorem act_isometry (G : Geometry R) (a : Word) : Isometry (G.act a) := by
  induction a with
  | nil => exact isometry_id
  | cons j a ih => exact ih.comp (G.isometry_gate j)

private theorem act_replicate (G : Geometry R) (n : ℕ) (j : Fin 11) (P : R) :
    G.act (List.replicate n j) P = (G.gate j)^[n] P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, Geometry.act, Function.iterate_succ_apply] using ih (G.gate j P)

private theorem act_cancel (G : Geometry R) (b : Word) (P : R) :
    G.act (b ++ inverseWord b) P = P := by
  induction b generalizing P with
  | nil => rfl
  | cons j b ih =>
    calc
      _ = G.act (List.replicate 9 j) (G.act (b ++ inverseWord b) (G.gate j P)) := by
        simp [inverseWord, Geometry.act, act_append]
      _ = G.act (List.replicate 9 j) (G.gate j P) := by rw [ih]
      _ = (G.gate j)^[10] P := by
        rw [act_replicate]
        rfl
      _ = P := G.period j P

private theorem ray_append (G : Geometry R) (a b : Word) :
    G.ray (a ++ b) = G.act b (G.ray a) := act_append G a b G.ready

private theorem ray_return_transport (G : Geometry R) (a b : Word) :
    dist (G.ray a) (G.ray b) = dist (G.ray (a ++ inverseWord b)) (G.ray []) := by
  have hb : G.act (inverseWord b) (G.ray b) = G.ray [] := by
    simpa [Geometry.ray, act_append, Geometry.act] using act_cancel G b G.ready
  rw [ray_append, ← hb, (act_isometry G (inverseWord b)).dist_eq]

def ReadyReturn (L : Law) (G : Geometry R) : Prop :=
  ∀ c : ℕ → Word, Tendsto (fun n => G.ray (c n)) atTop (𝓝 (G.ray [])) →
    Tendsto (fun n => L.row (c n)) atTop (𝓝 (L.row []))

private theorem ready_control (L : Law) (G : Geometry R) (hu : ReadyReturn L G)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ c, dist (G.ray c) (G.ray []) < δ → dist (L.row c) (L.row []) < ε := by
  by_contra hn
  push_neg at hn
  have hx (n : ℕ) := hn (1 / ((n : ℝ) + 1)) (by positivity)
  choose c hc he using hx
  have hc0 : Tendsto (fun n => G.ray (c n)) atTop (𝓝 (G.ray [])) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hc n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hh := (tendsto_iff_dist_tendsto_zero.1 (hu c hc0)).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hh.exists
  exact (not_lt_of_ge (he n)) hn

/-- Sequential return at one ready controls all pairs and all equal-ray word fibers. -/
theorem uniform_rows_and_fibers (L : Law) (G : Geometry R)
    (h : L.R10) (hu : ReadyReturn L G) :
    (∀ ε > 0, ∃ δ > 0, ∀ a b,
      dist (G.ray a) (G.ray b) < δ → dist (L.row a) (L.row b) < ε) ∧
    (∀ a b, G.ray a = G.ray b → L.row a = L.row b) := by
  have hp : ∀ ε > 0, ∃ δ > 0, ∀ a b,
      dist (G.ray a) (G.ray b) < δ → dist (L.row a) (L.row b) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hc⟩ := ready_control L G hu ε hε
    refine ⟨δ, hδ, fun a b hab => ?_⟩
    rw [row_return_transport L h]
    apply hc
    rwa [← ray_return_transport]
  refine ⟨hp, fun a b hab => dist_eq_zero.1 ?_⟩
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hp ε hε
  simpa using hc a b (by simpa [hab] using hδ)

end
end D5.S3.Quantum.Algebra.PositiveWordRayDescent
