/- GID: D5/S3/Combinatorics/SpectralGraph/ScalarCycleRowError
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ScalarCycleRowError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Actual weighted-tree rows obstruct positive cycle rates with sharp constant one. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! Actual generator rows, cycle obstruction, and sharp endpoint folding. -/

@[expose] public section

open scoped BigOperators NNReal
open SimpleGraph Finset

namespace D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError

/-- Positive finite tree data, with the original masses and clock. -/
structure TreeData (V : Type*) where
  graph : SimpleGraph V
  tree : graph.IsTree
  mass : V → ℝ
  mass_pos : ∀ x, 0 < mass x
  conductance : V → V → ℝ
  conductance_symm : ∀ x y, conductance x y = conductance y x
  conductance_pos : ∀ x y, graph.Adj x y → 0 < conductance x y
  killing : V → ℝ
  killing_nonneg : ∀ x, 0 ≤ killing x

/-- A killed generator is determined by its nonnegative off-diagonal rates and killing. -/
structure KilledGenerator (B : Type*) where
  rate : B → B → ℝ
  rate_nonneg : ∀ a b, a ≠ b → 0 ≤ rate a b
  killing : B → ℝ
  killing_nonneg : ∀ a, 0 ≤ killing a

noncomputable section

variable {V B : Type*} [Fintype V] [Fintype B]

/-- The backward generator, using only actual neighbors. -/
def generator (T : TreeData V) (f : V → ℝ) (x : V) : ℝ := by
  classical
  exact (∑ y, if T.graph.Adj x y then
    T.conductance x y / T.mass x * (f y - f x) else 0) - T.killing x * f x

/-- Off-label sums are taken over original vertices and actual edges. -/
def labelRate (T : TreeData V) (π : V → B) (x : V) (b : B) : ℝ := by
  classical
  exact ∑ y, if T.graph.Adj x y ∧ π y = b then T.conductance x y / T.mass x else 0

/-- The uniform off-label error; the lattice bottom gives zero for an empty maximum. -/
def delta (T : TreeData V) (π : V → B) (Q : KilledGenerator B) : ℝ := by
  classical
  exact ↑(univ.sup fun p : V × B =>
    if p.2 ≠ π p.1 then ‖labelRate T π p.1 p.2 - Q.rate (π p.1) p.2‖₊ else 0)

/-- Total original mass of a label. -/
def inducedMass (T : TreeData V) (π : V → B) (a : B) : ℝ := by
  classical
  exact ∑ x, if π x = a then T.mass x else 0

/-- Literal mass-weighted compression, including the averaged killing. -/
def compression (T : TreeData V) (π : V → B) : KilledGenerator B := by
  classical
  refine {
    rate := fun a b => (∑ x, if π x = a then T.mass x * labelRate T π x b else 0) /
      inducedMass T π a
    rate_nonneg := ?_
    killing := fun a => (∑ x, if π x = a then T.mass x * T.killing x else 0) /
      inducedMass T π a
    killing_nonneg := ?_ }
  · intro a b _
    apply div_nonneg
    · apply sum_nonneg
      intro x _
      split_ifs
      · apply mul_nonneg (T.mass_pos x).le
        apply sum_nonneg
        intro y _
        split_ifs with h
        · exact div_nonneg (T.conductance_pos x y h.1).le (T.mass_pos x).le
        · exact le_rfl
      · exact le_rfl
    · exact sum_nonneg fun x _ => by
        split_ifs
        · exact (T.mass_pos x).le
        · exact le_rfl
  · intro a
    apply div_nonneg
    · exact sum_nonneg fun x _ => by
        split_ifs
        · exact mul_nonneg (T.mass_pos x).le (T.killing_nonneg x)
        · exact le_rfl
    · exact sum_nonneg fun x _ => by
        split_ifs
        · exact (T.mass_pos x).le
        · exact le_rfl

/-- Action of a killed coarse generator; diagonal rates cancel identically. -/
def coarseAction (Q : KilledGenerator B) (f : B → ℝ) (a : B) : ℝ :=
  (∑ b, Q.rate a b * (f b - f a)) - Q.killing a * f a

private theorem generator_label_expansion (T : TreeData V) (π : V → B)
    (f : B → ℝ) (x : V) :
    generator T (f ∘ π) x =
      (∑ b, labelRate T π x b * (f b - f (π x))) - T.killing x * f (π x) := by
  classical
  unfold generator labelRate
  simp only [Function.comp_apply, sum_mul]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  by_cases h : T.graph.Adj x y
  · simp [h, eq_comm]
  · simp [h]

/-- Original mass average of a vertex function on one label class. -/
def massAverage (T : TreeData V) (π : V → B) (g : V → ℝ) (a : B) : ℝ := by
  classical
  exact (∑ x, if π x = a then T.mass x * g x else 0) / inducedMass T π a

private theorem compression_action (T : TreeData V) (π : V → B)
    (f : B → ℝ) (a : B) :
    coarseAction (compression T π) f a =
      massAverage T π (generator T (f ∘ π)) a := by
  classical
  unfold coarseAction massAverage
  dsimp only [compression]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← sub_div]
  congr 1
  simp_rw [sum_mul]
  rw [sum_comm]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  by_cases hx : π x = a
  · simp only [hx, ite_true, generator_label_expansion]
    rw [mul_sub, mul_sum]
    simp only [mul_assoc]
  · simp [hx]

/-- Conductance aggregated across actual edges of two label classes. -/
def inducedConductance (T : TreeData V) (π : V → B) (a b : B) : ℝ := by
  classical
  exact ∑ x, if π x = a then
    ∑ y, if T.graph.Adj x y ∧ π y = b then T.conductance x y else 0 else 0

omit [Fintype B] in
private theorem compression_rate (T : TreeData V) (π : V → B) (a b : B) :
    (compression T π).rate a b = inducedConductance T π a b / inducedMass T π a := by
  classical
  dsimp only [compression, inducedConductance]
  congr 1
  apply sum_congr rfl
  intro x _
  by_cases hx : π x = a
  · simp only [hx, ite_true, labelRate, mul_sum]
    apply sum_congr rfl
    intro y _
    split_ifs
    · field_simp [(T.mass_pos x).ne']
    · simp
  · simp [hx]

/-- Every direction of a simple cycle has the specified positive rate. -/
def CycleRates (Q : KilledGenerator B) (η : ℝ) : Prop :=
  ∃ (n : ℕ) (ι : Fin (n + 3) → B), Function.Injective ι ∧
    ∀ i j, (cycleGraph (n + 3)).Adj i j → η ≤ Q.rate (ι i) (ι j)

private theorem entry_le_delta (T : TreeData V) (π : V → B) (Q : KilledGenerator B)
    (x : V) (b : B) (hb : b ≠ π x) :
    |labelRate T π x b - Q.rate (π x) b| ≤ delta T π Q := by
  classical
  have h := Finset.le_sup (f := fun p : V × B =>
    if p.2 ≠ π p.1 then ‖labelRate T π p.1 p.2 - Q.rate (π p.1) p.2‖₊ else 0)
    (Finset.mem_univ (x, b))
  simpa [delta, hb, Real.norm_eq_abs] using (NNReal.coe_le_coe.mpr h)

private theorem forest_not_two_neighbors {W : Type*} [Finite W] [Nonempty W]
    (G : SimpleGraph W) (hG : G.IsAcyclic) :
    ¬ ∀ x, ∃ y z, G.Adj x y ∧ G.Adj x z ∧ y ≠ z := by
  classical
  letI := Fintype.ofFinite W
  intro hall
  let C := G.connectedComponentMk (Classical.choice (inferInstance : Nonempty W))
  let : Nonempty C := C.connected_toSimpleGraph.nonempty
  have hc : C.toSimpleGraph.IsTree := hG.isTree_connectedComponent C
  have htwo (x : C) : ∃ y z : C,
      C.toSimpleGraph.Adj x y ∧ C.toSimpleGraph.Adj x z ∧ y ≠ z := by
    obtain ⟨y, z, hy, hz, hne⟩ := hall x.val
    exact ⟨⟨y, C.mem_supp_of_adj_mem_supp x.property hy⟩,
      ⟨z, C.mem_supp_of_adj_mem_supp x.property hz⟩, hy, hz,
      fun h => hne (congrArg Subtype.val h)⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨y, z, hy, hz, hyz⟩ := htwo x
  let : Nontrivial C := ⟨⟨y, z, hyz⟩⟩
  obtain ⟨v, hv⟩ := hc.exists_vert_degree_one_of_nontrivial
  obtain ⟨u, _, hu⟩ := C.toSimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  obtain ⟨a, b, ha, hb, hab⟩ := htwo v
  exact hab ((hu a ha).trans (hu b hb).symm)

omit [Fintype B] in
private theorem missing_cycle_neighbor (T : TreeData V) (π : V → B)
    (hπ : Function.Surjective π) {n : ℕ} (ι : Fin (n + 3) → B)
    (hι : Function.Injective ι) :
    ∃ x i j, π x = ι i ∧ (cycleGraph (n + 3)).Adj i j ∧
      ∀ y, T.graph.Adj x y → π y ≠ ι j := by
  classical
  by_contra! h
  let S : Set V := {x | ∃ i, π x = ι i}
  obtain ⟨x, hx⟩ := hπ (ι 0)
  let : Nonempty S := ⟨⟨x, 0, hx⟩⟩
  apply forest_not_two_neighbors (T.graph.induce S) (T.tree.isAcyclic.induce S)
  intro x
  obtain ⟨i, hi⟩ := x.property
  have hd := cycleGraph_degree_three_le (v := i)
  have hcard : 2 ≤ ((cycleGraph (n + 3)).neighborFinset i).card := by
    simpa only [SimpleGraph.degree] using hd.ge
  obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.mp (by omega :
    1 < ((cycleGraph (n + 3)).neighborFinset i).card)
  have hj' := (mem_neighborFinset _ _ _).mp hj
  have hl' := (mem_neighborFinset _ _ _).mp hl
  obtain ⟨y, hxy, hy⟩ := h x.val i j hi hj'
  obtain ⟨z, hxz, hz⟩ := h x.val i l hi hl'
  refine ⟨⟨y, j, hy⟩, ⟨z, l, hz⟩, hxy, hxz, ?_⟩
  intro he
  apply hjl
  apply hι
  exact hy.symm.trans ((congrArg π (congrArg Subtype.val he)).trans hz)

/-- A positive bidirectional simple cycle forces an actual off-label row error at least η. -/
theorem cycle_row_error_lower_bound (T : TreeData V) (π : V → B)
    (hπ : Function.Surjective π) (Q : KilledGenerator B) (η : ℝ)
    (hη : 0 < η) (hcycle : CycleRates Q η) : η ≤ delta T π Q := by
  classical
  obtain ⟨n, ι, hι, hr⟩ := hcycle
  obtain ⟨x, i, j, hx, hij, hmiss⟩ := missing_cycle_neighbor T π hπ ι hι
  have hne : ι j ≠ π x := by
    rw [hx]
    exact fun h => hij.ne (hι h.symm)
  have hz : labelRate T π x (ι j) = 0 := by
    apply sum_eq_zero
    intro y _
    split_ifs with h
    · exact False.elim (hmiss y h.1 h.2)
    · rfl
  have hb := entry_le_delta T π Q x (ι j) hne
  rw [hz, hx, zero_sub, abs_neg, abs_of_nonneg (le_trans hη.le (hr i j hij))] at hb
  exact (hr i j hij).trans hb


/-- The k-edge path has unit masses, conductances 2η, and zero killing. -/
def sharpPath (k : ℕ) (η : ℝ) (hη : 0 < η) : TreeData (Fin (k + 1)) where
  graph := pathGraph (k + 1)
  tree := ⟨connected_pathGraph_add_one k, isAcyclic_pathGraph (k + 1)⟩
  mass := fun _ => 1
  mass_pos := fun _ => zero_lt_one
  conductance := fun _ _ => 2 * η
  conductance_symm := fun _ _ => rfl
  conductance_pos := fun _ _ _ => mul_pos (by norm_num) hη
  killing := fun _ => 0
  killing_nonneg := fun _ => le_rfl

/-- Endpoint folding: the first k vertices keep their indices and the last returns to zero. -/
def endpointFold (k : ℕ) (hk : 0 < k) (x : Fin (k + 1)) : Fin k :=
  if h : x.val < k then ⟨x.val, h⟩ else ⟨0, hk⟩

private theorem fold_castSucc (k : ℕ) (hk : 0 < k) (a : Fin k) :
    endpointFold k hk a.castSucc = a := by
  simp [endpointFold, a.isLt]

private theorem fold_last (k : ℕ) (hk : 0 < k) :
    endpointFold k hk (Fin.last k) = ⟨0, hk⟩ := by
  simp [endpointFold]

private theorem path_row_castSucc (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (a b : Fin k) :
    labelRate (sharpPath k η hη) (endpointFold k hk) a.castSucc b =
      (if (pathGraph k).Adj a b then 2 * η else 0) +
      if a.val + 1 = k ∧ b = ⟨0, hk⟩ then 2 * η else 0 := by
  classical
  unfold labelRate
  rw [Fin.sum_univ_castSucc]
  simp only [sharpPath, fold_castSucc, fold_last, div_one, pathGraph_adj,
    Fin.val_castSucc, Fin.val_last]
  rw [Finset.sum_eq_single b]
  · simp only [and_true]
    congr 1
    apply if_congr
    · constructor
      · rintro ⟨h, hb⟩
        exact ⟨by omega, hb.symm⟩
      · rintro ⟨h, hb⟩
        exact ⟨Or.inl h, hb.symm⟩
    · rfl
    · rfl
  · intro i _ hib
    simp [hib]
  · simp

private theorem path_row_last (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (b : Fin k) :
    labelRate (sharpPath k η hη) (endpointFold k hk) (Fin.last k) b =
      if b.val + 1 = k then 2 * η else 0 := by
  classical
  unfold labelRate
  rw [Fin.sum_univ_castSucc]
  have hn : ¬ (sharpPath k η hη).graph.Adj (Fin.last k) (Fin.last k) :=
    (sharpPath k η hη).graph.irrefl
  simp only [hn, false_and, ↓reduceIte, add_zero]
  simp only [sharpPath, fold_castSucc, pathGraph_adj, Fin.val_last,
    Fin.val_castSucc, div_one]
  rw [Finset.sum_eq_single b]
  · have hb : k + 1 ≠ b.val := by omega
    simp [hb]
  · intro i _ hib
    simp [hib]
  · simp

private theorem induced_path_mass (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (a : Fin k) :
    inducedMass (sharpPath k η hη) (endpointFold k hk) a =
      if a = ⟨0, hk⟩ then 2 else 1 := by
  classical
  unfold inducedMass
  rw [Fin.sum_univ_castSucc]
  simp [sharpPath, fold_castSucc, fold_last, eq_comm]
  split_ifs <;> norm_num


private theorem compression_path_rows (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (a b : Fin k) :
    (compression (sharpPath k η hη) (endpointFold k hk)).rate a b =
      (labelRate (sharpPath k η hη) (endpointFold k hk) a.castSucc b +
        if a = ⟨0, hk⟩ then
          labelRate (sharpPath k η hη) (endpointFold k hk) (Fin.last k) b else 0) /
        (if a = ⟨0, hk⟩ then 2 else 1) := by
  classical
  dsimp only [compression]
  rw [induced_path_mass]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [sharpPath, fold_castSucc, fold_last, eq_comm]

private theorem path_zero_row (k : ℕ) (hk : 3 ≤ k) (η : ℝ) (hη : 0 < η)
    (b : Fin k) :
    labelRate (sharpPath k η hη) (endpointFold k (by omega))
      (⟨0, by omega⟩ : Fin (k + 1)) b =
      if b.val = 1 then 2 * η else 0 := by
  classical
  have h := path_row_castSucc k (by omega) η hη (⟨0, by omega⟩ : Fin k) b
  have hn : ¬ (0 + 1 = k ∧ b = (⟨0, by omega⟩ : Fin k)) := by omega
  simpa [pathGraph_adj, Fin.ext_iff, show (1 : ℕ) ≠ k by omega,
    show ¬ b.val + 1 = 0 by omega, eq_comm] using h

private theorem path_compression_zero (k : ℕ) (hk : 3 ≤ k) (η : ℝ) (hη : 0 < η)
    (b : Fin k) :
    (compression (sharpPath k η hη) (endpointFold k (by omega))).rate
      ⟨0, by omega⟩ b =
      (if b.val = 1 then η else 0) + (if b.val + 1 = k then η else 0) := by
  classical
  rw [compression_path_rows]
  simp only [ite_true]
  simp only [Fin.castSucc_mk]
  rw [path_zero_row k hk, path_row_last]
  split_ifs <;> ring

private theorem path_compression_nonzero (k : ℕ) (hk : 0 < k) (η : ℝ) (hη : 0 < η)
    (a b : Fin k) (ha : a ≠ ⟨0, hk⟩) :
    (compression (sharpPath k η hη) (endpointFold k hk)).rate a b =
      labelRate (sharpPath k η hη) (endpointFold k hk) a.castSucc b := by
  rw [compression_path_rows]
  simp [ha]


private theorem path_compression_cycle (n : ℕ) (η : ℝ) (hη : 0 < η)
    (a b : Fin (n + 3)) :
    (compression (sharpPath (n + 3) η hη) (endpointFold (n + 3) (by omega))).rate a b =
      if (cycleGraph (n + 3)).Adj a b then
        (if a = 0 then η else 2 * η) else 0 := by
  classical
  have hadd (i : Fin (n + 3)) : (i.val + 1) % (n + 3) =
      if i.val + 1 = n + 3 then 0 else i.val + 1 := by
    split_ifs with h
    · rw [h, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  by_cases ha : a = 0
  · subst a
    have hz := path_compression_zero (n + 3) (by omega) η hη b
    have he : (⟨0, by omega⟩ : Fin (n + 3)) = 0 := by
      apply Fin.ext
      simp
    rw [he] at hz
    rw [hz]
    simp only [cycleGraph_adj, sub_eq_iff_eq_add', Fin.ext_iff, Fin.val_add,
      Fin.val_one, Fin.val_zero, hadd, ite_true, Nat.zero_add,
      Nat.mod_eq_of_lt (show 1 < n + 3 by omega)]
    split_ifs <;> simp_all
  · rw [path_compression_nonzero (n + 3) (by omega) η hη a b ha, path_row_castSucc]
    simp only [cycleGraph_adj, sub_eq_iff_eq_add', Fin.ext_iff, Fin.val_add,
      Fin.val_one, Fin.val_zero, hadd, pathGraph_adj, ha, ite_false]
    have ha' : a.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using ha
    split_ifs <;> simp_all <;> omega

private theorem delta_le_of_entries (T : TreeData V) (π : V → B) (Q : KilledGenerator B)
    (η : ℝ) (hη : 0 ≤ η)
    (h : ∀ x b, b ≠ π x → |labelRate T π x b - Q.rate (π x) b| ≤ η) :
    delta T π Q ≤ η := by
  classical
  change ↑(univ.sup fun p : V × B =>
      if p.2 ≠ π p.1 then ‖labelRate T π p.1 p.2 - Q.rate (π p.1) p.2‖₊ else 0) ≤
    (↑(⟨η, hη⟩ : ℝ≥0) : ℝ)
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro p _
  split_ifs with hb
  · apply NNReal.coe_le_coe.mp
    change ‖labelRate T π p.1 p.2 - Q.rate (π p.1) p.2‖ ≤ η
    simpa only [Real.norm_eq_abs] using h p.1 p.2 hb
  · exact bot_le

private theorem path_row_bound (k : ℕ) (hk : 3 ≤ k) (η : ℝ) (hη : 0 < η)
    (x : Fin (k + 1)) (b : Fin k) :
    |labelRate (sharpPath k η hη) (endpointFold k (by omega)) x b -
      (compression (sharpPath k η hη) (endpointFold k (by omega))).rate
        (endpointFold k (by omega) x) b| ≤ η := by
  classical
  induction x using Fin.lastCases with
  | last =>
    rw [fold_last, path_row_last, path_compression_zero k hk]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  | cast a =>
    rw [fold_castSucc]
    by_cases ha : a = (⟨0, by omega⟩ : Fin k)
    · subst a
      simp only [Fin.castSucc_mk]
      rw [path_zero_row k hk, path_compression_zero k hk]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    · rw [path_compression_nonzero k (by omega) η hη a b ha, sub_self, abs_zero]
      exact hη.le

/-- For every k ≥ 3 and η > 0 the literal induced compression attains constant one. -/
theorem endpoint_folding_sharpness (k : ℕ) (hk : 3 ≤ k) (η : ℝ) (hη : 0 < η) :
  let T := sharpPath k η hη
  let π := endpointFold k (by omega)
  let Q := compression T π
  Function.Surjective π ∧
  (∀ a, inducedMass T π a = if a = (⟨0, by omega⟩ : Fin k) then 2 else 1) ∧
  (∀ a b, inducedConductance T π a b = if (cycleGraph k).Adj a b then 2 * η else 0) ∧
  (∀ a b, Q.rate a b = if (cycleGraph k).Adj a b then
    (if a = (⟨0, by omega⟩ : Fin k) then η else 2 * η) else 0) ∧
  (∀ a, Q.killing a = 0) ∧
  CycleRates Q η ∧
  (∃ a b, (cycleGraph k).Adj a b ∧ Q.rate a b = η) ∧
  (∀ x b, |labelRate T π x b - Q.rate (π x) b| ≤ η) ∧
  (∀ a b, a ≠ (⟨0, by omega⟩ : Fin k) → labelRate T π a.castSucc b = Q.rate a b) ∧
  (∀ b, labelRate T π (⟨0, by omega⟩ : Fin (k + 1)) b =
    if b.val = 1 then 2 * η else 0) ∧
  (∀ b, labelRate T π (Fin.last k) b = if b.val + 1 = k then 2 * η else 0) ∧
  (∀ f a, coarseAction Q f a = massAverage T π (generator T (f ∘ π)) a) ∧
  delta T π Q = η := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  let T := sharpPath (n + 3) η hη
  let π := endpointFold (n + 3) (by omega)
  let Q := compression T π
  have hπ : Function.Surjective π := fun a => ⟨a.castSucc, fold_castSucc _ _ a⟩
  have hm (a : Fin (n + 3)) : inducedMass T π a = if a = 0 then 2 else 1 := by
    exact induced_path_mass _ _ η hη a
  have hr (a b : Fin (n + 3)) : Q.rate a b =
      if (cycleGraph (n + 3)).Adj a b then (if a = 0 then η else 2 * η) else 0 :=
    path_compression_cycle n η hη a b
  have hcycle : CycleRates Q η := by
    refine ⟨n, id, Function.injective_id, ?_⟩
    intro a b hab
    simp only [id_eq, hr, ite_eq_left hab]
    split_ifs <;> linarith
  have hatt : ∃ a b, (cycleGraph (n + 3)).Adj a b ∧ Q.rate a b = η := by
    have hadj : (cycleGraph (n + 3)).Adj 0 1 := by
      rw [cycleGraph_adj]
      exact Or.inr (by simp)
    exact ⟨0, 1, hadj, by rw [hr, ite_eq_left hadj]; simp⟩
  have hc (a b : Fin (n + 3)) : inducedConductance T π a b =
      if (cycleGraph (n + 3)).Adj a b then 2 * η else 0 := by
    have he := compression_rate T π a b
    rw [show (compression T π).rate a b = Q.rate a b from rfl, hr, hm] at he
    split_ifs at he ⊢ <;> linarith
  have hb (x : Fin (n + 3 + 1)) (b : Fin (n + 3)) :
      |labelRate T π x b - Q.rate (π x) b| ≤ η := path_row_bound _ (by omega) η hη x b
  refine ⟨hπ, hm, hc, hr, ?_, hcycle, hatt, hb, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [Q, compression, T, sharpPath]
  · intro a b ha
    exact (path_compression_nonzero _ _ η hη a b ha).symm
  · exact path_zero_row _ (by omega) η hη
  · exact path_row_last _ _ η hη
  · exact compression_action T π
  · apply le_antisymm
    · exact delta_le_of_entries T π Q η hη.le (fun x b _ => hb x b)
    · exact cycle_row_error_lower_bound T π hπ Q η hη hcycle

/-- The complete weighted-tree cycle obstruction and unrestricted induced-compression sharpness. -/
theorem cycle_row_error_and_sharpness :
    (∀ {W : Type*} {C : Type*} [Fintype W] [Fintype C]
      (T : TreeData W) (π : W → C), Function.Surjective π →
      ∀ (Q : KilledGenerator C) (η : ℝ), 0 < η → CycleRates Q η → η ≤ delta T π Q) ∧
    (∀ (k : ℕ) (hk : 3 ≤ k) (η : ℝ) (hη : 0 < η),
      let T := sharpPath k η hη
      let π := endpointFold k (by omega)
      let Q := compression T π
      Function.Surjective π ∧
      (∀ a, inducedMass T π a = if a = (⟨0, by omega⟩ : Fin k) then 2 else 1) ∧
      (∀ a b, inducedConductance T π a b = if (cycleGraph k).Adj a b then 2 * η else 0) ∧
      (∀ a b, Q.rate a b = if (cycleGraph k).Adj a b then
        (if a = (⟨0, by omega⟩ : Fin k) then η else 2 * η) else 0) ∧
      (∀ a, Q.killing a = 0) ∧
      CycleRates Q η ∧
      (∃ a b, (cycleGraph k).Adj a b ∧ Q.rate a b = η) ∧
      (∀ x b, |labelRate T π x b - Q.rate (π x) b| ≤ η) ∧
      (∀ a b, a ≠ (⟨0, by omega⟩ : Fin k) → labelRate T π a.castSucc b = Q.rate a b) ∧
      (∀ b, labelRate T π (⟨0, by omega⟩ : Fin (k + 1)) b =
        if b.val = 1 then 2 * η else 0) ∧
      (∀ b, labelRate T π (Fin.last k) b = if b.val + 1 = k then 2 * η else 0) ∧
      (∀ f a, coarseAction Q f a = massAverage T π (generator T (f ∘ π)) a) ∧
      delta T π Q = η) := by
  exact ⟨@cycle_row_error_lower_bound, endpoint_folding_sharpness⟩

end
end D5.S3.Combinatorics.SpectralGraph.ScalarCycleRowError
