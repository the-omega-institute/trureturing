/- GID: D5/S3/Quantum/Algebra/PositiveWordRayDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PositiveWordRayDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
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
open scoped BoundedContinuousFunction
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
  | succ n ih =>
    simpa [List.replicate_succ, Geometry.act, Function.iterate_succ_apply]
      using ih (G.gate j P)

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
  push Not at hn
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


/-- The full row extension, including normalization, bounds and every future. -/
def Descent (L : Law) (G : Geometry R) (Φ : C(R, L.closedSpan)) : Prop :=
  (∀ a, (Φ (G.ray a) : Row) = L.row a) ∧
  (∀ P, (Φ P : Row) none = 1) ∧
  (∀ P f, (Φ P : Row) (some f) ∈ Icc (0 : ℝ) 1) ∧
  (∀ P f, (Φ P : Row) (some f) = (Φ (G.act f P) : Row) (some []))

/-- Fiber constancy and uniform pair control are consumed before dense extension. -/
theorem continuous_descent (L : Law) (G : Geometry R) (hd : DenseRange G.ray)
    (h : L.R10) (hu : ReadyReturn L G) : ∃! Φ : C(R, L.closedSpan), Descent L G Φ := by
  classical
  obtain ⟨hp, hf⟩ := uniform_rows_and_fibers L G h hu
  let word : range G.ray → Word := fun P => Classical.choose P.property
  have hw (P : range G.ray) : G.ray (word P) = P := Classical.choose_spec P.property
  let ψ : range G.ray → Row := fun P => L.row (word P)
  have hψ : UniformContinuous ψ := by
    apply Metric.uniformContinuous_iff.2
    intro ε hε
    obtain ⟨δ, hδ, hc⟩ := hp ε hε
    refine ⟨δ, hδ, fun {P Q} hPQ => hc _ _ ?_⟩
    simpa only [hw, Subtype.dist_eq] using hPQ
  let F : R → Row := hd.extend ψ
  have hF : Continuous F := (hd.uniformContinuous_extend hψ).continuous
  have hFa (a : Word) : F (G.ray a) = L.row a := by
    change hd.extend ψ (↑(⟨G.ray a, mem_range_self a⟩ : range G.ray)) = _
    rw [hd.extend_of_ind hψ]
    exact hf _ _ (hw _)
  have hmem (P : R) : F P ∈ L.closedSpan := by
    refine hd.induction_on (p := fun P => F P ∈ L.closedSpan) P
      ((Submodule.isClosed_topologicalClosure _).preimage hF) ?_
    intro a
    rw [hFa]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self a))
  let Φ : C(R, L.closedSpan) := ⟨fun P => ⟨F P, hmem P⟩, hF.subtype_mk _⟩
  have heval (i : Coordinate) : Continuous (fun P => F P i) :=
    (BoundedContinuousFunction.evalCLM ℝ i).continuous.comp hF
  have hstar (P : R) : F P none = 1 := by
    refine hd.induction_on (p := fun P => F P none = 1) P
      (isClosed_eq (heval none) continuous_const) ?_
    intro a
    rw [hFa]
    rfl
  have hbound (P : R) (f : Word) : F P (some f) ∈ Icc (0 : ℝ) 1 := by
    refine hd.induction_on (p := fun P => F P (some f) ∈ Icc (0 : ℝ) 1) P
      (isClosed_Icc.preimage (heval (some f))) ?_
    intro a
    rw [hFa]
    exact L.bounds (a ++ f)
  have hfuture (f : Word) : (fun P => F P (some f)) =
      (fun P => F (G.act f P) (some [])) := by
    apply hd.equalizer (heval (some f))
      ((heval (some [])).comp (act_isometry G f).continuous)
    funext a
    change F (G.ray a) (some f) = F (G.act f (G.ray a)) (some [])
    rw [← ray_append, hFa, hFa]
    simp [Law.row, Law.value]
  refine ⟨Φ, ⟨hFa, hstar, hbound, fun P f => congrFun (hfuture f) P⟩, ?_⟩
  intro Ψ hΨ
  apply ContinuousMap.ext
  intro P
  apply Subtype.ext
  have heq : (fun P => (Ψ P : Row)) = F := by
    apply hd.equalizer (continuous_subtype_val.comp Ψ.continuous) hF
    funext a
    exact (hΨ.1 a).trans (hFa a).symm
  exact congrFun heq P

/-- In the backward direction the continuous representation supplies statistical R10. -/
theorem represented_statistics [CompactSpace R] (L : Law) (G : Geometry R)
    (q : C(R, Icc (0 : ℝ) 1)) (hq : ∀ a, (q (G.ray a) : ℝ) = L.probability a) :
    L.R10 ∧ ReadyReturn L G := by
  have hqc : Continuous (fun P => (q P : ℝ)) :=
    continuous_subtype_val.comp q.continuous
  have hqu := CompactSpace.uniformContinuous_of_continuous hqc
  constructor
  · intro a j f
    rw [← hq, ← hq]
    congr 2
    simp only [Geometry.ray, act_append, act_replicate, G.period]
  · intro c hc
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨δ, hδ, hδq⟩ := Metric.uniformContinuous_iff.1 hqu (ε / 2) (by positivity)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hc δ hδ
    refine ⟨N, fun n hn => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    apply (BoundedContinuousFunction.dist_le (by positivity : 0 ≤ ε / 2)).2
    intro i
    cases i with
    | none => simpa [Law.row, Law.value] using (by positivity : (0 : ℝ) ≤ ε / 2)
    | some f =>
      change dist (L.probability (c n ++ f)) (L.probability ([] ++ f)) ≤ ε / 2
      rw [← hq, ← hq, ray_append, ray_append]
      exact (hδq (by
        rw [(act_isometry G f).dist_eq]
        exact hN n hn)).le

/-- The epsilon coordinate, rather than the constant star, is the unique response. -/
theorem ready_return_iff_unique_response [CompactSpace R] (L : Law) (G : Geometry R)
    (hd : DenseRange G.ray) :
    (L.R10 ∧ ReadyReturn L G) ↔
      ∃! q : C(R, Icc (0 : ℝ) 1), ∀ a, (q (G.ray a) : ℝ) = L.probability a := by
  constructor
  · rintro ⟨h, hu⟩
    obtain ⟨Φ, hΦ, _⟩ := continuous_descent L G hd h hu
    let q : C(R, Icc (0 : ℝ) 1) := ⟨fun P => ⟨(Φ P : Row) (some []), hΦ.2.2.1 P []⟩,
      ((BoundedContinuousFunction.evalCLM ℝ (some [])).continuous.comp
        (continuous_subtype_val.comp Φ.continuous)).subtype_mk _⟩
    have hqa (a : Word) : (q (G.ray a) : ℝ) = L.probability a := by
      change (Φ (G.ray a) : Row) (some []) = _
      rw [hΦ.1]
      simp [Law.row, Law.value]
    refine ⟨q, hqa, fun r hr => ?_⟩
    apply ContinuousMap.ext
    intro P
    exact congrFun (hd.equalizer r.continuous q.continuous
      (funext fun a => Subtype.ext ((hr a).trans (hqa a).symm))) P
  · rintro ⟨q, hq, _⟩
    exact represented_statistics L G q hq

def returnErrors (L : Law) (G : Geometry R) (s : ℝ) : Set ℝ :=
  {r | ∃ c, dist (G.ray c) (G.ray []) ≤ s ∧ dist (L.row c) (L.row []) = r}

def pairErrors (L : Law) (G : Geometry R) (s : ℝ) : Set ℝ :=
  {r | ∃ a b, dist (G.ray a) (G.ray b) ≤ s ∧ dist (L.row a) (L.row b) = r}

def scalarErrors (L : Law) (G : Geometry R) (s : ℝ) : Set ℝ :=
  {r | ∃ a b, dist (G.ray a) (G.ray b) ≤ s ∧
    dist (L.probability a) (L.probability b) = r}

private theorem row_distance_le_one (L : Law) (a b : Word) :
    dist (L.row a) (L.row b) ≤ 1 := by
  apply (BoundedContinuousFunction.dist_le zero_le_one).2
  intro i
  rw [Real.dist_eq, abs_sub_le_iff]
  have hi := value_bounds L a i
  have hj := value_bounds L b i
  change L.value a i - L.value b i ≤ 1 ∧ L.value b i - L.value a i ≤ 1
  constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]

private theorem scalar_distance_le_row (L : Law) (a b : Word) :
    dist (L.probability a) (L.probability b) ≤ dist (L.row a) (L.row b) := by
  simpa [Law.row, Law.value] using
    (BoundedContinuousFunction.dist_coe_le_dist (f := L.row a) (g := L.row b) (some []))

/-- Nonattained real suprema over all words agree; no return-continuity premise is used. -/
theorem three_moduli_equal (L : Law) (G : Geometry R) (h : L.R10)
    (s : ℝ) (hs : 0 ≤ s) :
    sSup (returnErrors L G s) = sSup (pairErrors L G s) ∧
    sSup (pairErrors L G s) = sSup (scalarErrors L G s) ∧
    sSup (returnErrors L G s) ∈ Icc (0 : ℝ) 1 := by
  have hr0 : (0 : ℝ) ∈ returnErrors L G s := ⟨[], by simpa using hs, by simp⟩
  have hp0 : (0 : ℝ) ∈ pairErrors L G s := ⟨[], [], by simpa using hs, by simp⟩
  have hq0 : (0 : ℝ) ∈ scalarErrors L G s := ⟨[], [], by simpa using hs, by simp⟩
  have hrb : BddAbove (returnErrors L G s) := by
    refine ⟨1, ?_⟩
    rintro r ⟨c, _, rfl⟩
    exact row_distance_le_one L c []
  have hpb : BddAbove (pairErrors L G s) := by
    refine ⟨1, ?_⟩
    rintro r ⟨a, b, _, rfl⟩
    exact row_distance_le_one L a b
  have hqb : BddAbove (scalarErrors L G s) := by
    refine ⟨1, ?_⟩
    rintro r ⟨a, b, _, rfl⟩
    exact (scalar_distance_le_row L a b).trans (row_distance_le_one L a b)
  have hqr : 0 ≤ sSup (scalarErrors L G s) := le_csSup hqb hq0
  have hrp : sSup (returnErrors L G s) = sSup (pairErrors L G s) := by
    apply le_antisymm
    · apply csSup_le ⟨0, hr0⟩
      rintro r ⟨c, hc, rfl⟩
      exact le_csSup hpb ⟨c, [], hc, rfl⟩
    · apply csSup_le ⟨0, hp0⟩
      rintro r ⟨a, b, hab, rfl⟩
      apply le_csSup hrb
      refine ⟨a ++ inverseWord b, ?_, ?_⟩
      · rwa [← ray_return_transport]
      · exact (row_return_transport L h a b).symm
  have hpq : sSup (pairErrors L G s) = sSup (scalarErrors L G s) := by
    apply le_antisymm
    · apply csSup_le ⟨0, hp0⟩
      rintro r ⟨a, b, hab, rfl⟩
      apply (BoundedContinuousFunction.dist_le hqr).2
      intro i
      cases i with
      | none => simpa [Law.row, Law.value] using hqr
      | some f =>
        apply le_csSup hqb
        refine ⟨a ++ f, b ++ f, ?_, rfl⟩
        simpa only [ray_append, (act_isometry G f).dist_eq] using hab
    · apply csSup_le ⟨0, hq0⟩
      rintro r ⟨a, b, hab, rfl⟩
      exact (scalar_distance_le_row L a b).trans (le_csSup hpb ⟨a, b, hab, rfl⟩)
  refine ⟨hrp, hpq, le_csSup hrb hr0, csSup_le ⟨0, hr0⟩ ?_⟩
  rintro r ⟨c, _, rfl⟩
  exact row_distance_le_one L c []

end
end D5.S3.Quantum.Algebra.PositiveWordRayDescent
