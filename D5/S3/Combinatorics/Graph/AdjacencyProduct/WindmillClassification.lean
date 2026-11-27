/- GID: D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: Classification of ordinary adjacency matrix products for windmill graphs. -/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import OmegaBuild.Commands

/-! Windmill adjacency-matrix factorization (arXiv:2512.24864v1, Section 5, item 1).
The complete-graph criterion is due to Maghsoudi, Miraftab and Suda
(arXiv:2312.08615v1, Theorem 1.2). -/

compile_only_with_mathlib

namespace D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification

open SimpleGraph Matrix
open scoped BigOperators

/-- The hub is `none`. Each `some (i, j)` belongs to blade `i`. -/
def windmill (d t : ℕ) : SimpleGraph (Option (Fin d × Fin (t - 1))) where
  Adj x y :=
    match x, y with
    | none, none => False
    | none, some _ | some _, none => True
    | some x, some y => x.1 = y.1 ∧ x.2 ≠ y.2
  symm.symm := by
    rintro (_ | x) (_ | y) h
    · exact h
    · trivial
    · trivial
    · exact ⟨h.1.symm, Ne.symm h.2⟩
  loopless.irrefl := by
    rintro (_ | x) h
    · exact h
    · exact h.2 rfl

open scoped Classical

private theorem reverse_product {V : Type} [Fintype V] {A B C : SimpleGraph V}
    [DecidableRel A.Adj]
    (h : B.adjMatrix ℤ * C.adjMatrix ℤ = A.adjMatrix ℤ) :
    C.adjMatrix ℤ * B.adjMatrix ℤ = A.adjMatrix ℤ := by
  simpa only [transpose_mul, transpose_adjMatrix] using congrArg Matrix.transpose h

private theorem commute_product {V : Type} [Fintype V] {A B C : SimpleGraph V}
    [DecidableRel A.Adj]
    (h : B.adjMatrix ℤ * C.adjMatrix ℤ = A.adjMatrix ℤ) :
    B.adjMatrix ℤ * A.adjMatrix ℤ = A.adjMatrix ℤ * B.adjMatrix ℤ := by
  conv_lhs => rw [← reverse_product h]
  conv_rhs => rw [← h]
  exact (Matrix.mul_assoc _ _ _).symm

private theorem product_entry {V : Type} [Fintype V] (B C : SimpleGraph V)
    [DecidableRel B.Adj] [DecidableRel C.Adj] (x y : V) :
    (B.adjMatrix ℤ * C.adjMatrix ℤ) x y =
      ((B.neighborFinset x).filter (fun z ↦ C.Adj z y)).card := by
  rw [adjMatrix_mul_apply]
  simp only [adjMatrix_apply]
  exact (Finset.natCast_card_filter _ _).symm

private theorem hub_neighbor_in_blade {d t : ℕ}
    {B C : SimpleGraph (Option (Fin d × Fin (t - 1)))}
    (h : B.adjMatrix ℤ * C.adjMatrix ℤ = (windmill d t).adjMatrix ℤ)
    (i : Fin d) (j : Fin (t - 1)) :
    ∃ k : Fin (t - 1), B.Adj (some (i, k)) none := by
  let v : Option (Fin d × Fin (t - 1)) := some (i, j)
  have hone : (B.adjMatrix ℤ * C.adjMatrix ℤ) v none = 1 := by
    rw [h]
    rw [adjMatrix_apply]
    exact ite_eq_left trivial
  rw [product_entry] at hone
  have hcard : ((B.neighborFinset v).filter (fun z ↦ C.Adj z none)).card = 1 := by
    exact_mod_cast hone
  have hpos : 0 < ((B.neighborFinset v).filter (fun z ↦ C.Adj z none)).card := by omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  obtain ⟨hzB, hzC⟩ := Finset.mem_filter.mp hz
  cases z with
  | none => exact (C.irrefl hzC).elim
  | some z =>
    have hcomm := congrFun (congrFun (commute_product h) v) none
    rw [product_entry, product_entry] at hcomm
    have hpos : 0 < ((B.neighborFinset v).filter (fun w ↦ (windmill d t).Adj w none)).card :=
      Finset.card_pos.mpr ⟨some z, Finset.mem_filter.mpr ⟨hzB, trivial⟩⟩
    have hcast : (0 : ℤ) <
        (((B.neighborFinset v).filter (fun w ↦ (windmill d t).Adj w none)).card : ℤ) := by
      exact_mod_cast hpos
    rw [hcomm] at hcast
    have hpos' : 0 < (((windmill d t).neighborFinset v).filter (fun w ↦ B.Adj w none)).card := by
      exact_mod_cast hcast
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos'
    obtain ⟨hwW, hwB⟩ := Finset.mem_filter.mp hw
    cases w with
    | none => exact (B.irrefl hwB).elim
    | some w =>
      have hwAdj := (mem_neighborFinset _ _ _).mp hwW
      have hiw : i = w.1 := hwAdj.1
      exact ⟨w.2, by rcases w with ⟨l, k⟩; change i = l at hiw; simpa [hiw] using hwB⟩

private theorem one_blade_of_product {d t : ℕ} (hd : 1 ≤ d) (ht : 3 ≤ t)
    {B C : SimpleGraph (Option (Fin d × Fin (t - 1)))}
    (h : B.adjMatrix ℤ * C.adjMatrix ℤ = (windmill d t).adjMatrix ℤ) : d = 1 := by
  by_contra hne
  let i : Fin d := ⟨0, by omega⟩
  let l : Fin d := ⟨1, by omega⟩
  let j : Fin (t - 1) := ⟨0, by omega⟩
  have hil : i ≠ l := by intro he; have := congrArg Fin.val he; simp [i, l] at this
  obtain ⟨x, hx⟩ := hub_neighbor_in_blade h i j
  obtain ⟨y, hy⟩ := hub_neighbor_in_blade (reverse_product h) l j
  have hpos : 0 < ((B.neighborFinset (some (i, x))).filter
      (fun z ↦ C.Adj z (some (l, y)))).card :=
    Finset.card_pos.mpr
      ⟨none, Finset.mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr hx, C.adj_symm hy⟩⟩
  have hzero : (B.adjMatrix ℤ * C.adjMatrix ℤ) (some (i, x)) (some (l, y)) = 0 := by
    rw [h]
    rw [adjMatrix_apply]
    exact ite_eq_right fun hadj ↦ hil hadj.1
  rw [product_entry] at hzero
  exact (Nat.ne_of_gt hpos) (by exact_mod_cast hzero)

private theorem one_blade_complete (t : ℕ) :
    (windmill 1 t).adjMatrix ℤ = (⊤ : SimpleGraph (Option (Fin 1 × Fin (t - 1)))).adjMatrix ℤ := by
  ext x y
  simp only [adjMatrix_apply]
  cases x with
  | none => cases y <;> simp [windmill]
  | some x =>
    cases y with
    | none => simp [windmill]
    | some y =>
      rcases x with ⟨i, x⟩
      rcases y with ⟨j, y⟩
      simp [windmill, Subsingleton.elim i j]

private theorem degree_eq_of_complete_product {V : Type} [Fintype V] [DecidableEq V]
    {B C : SimpleGraph V}
    (h : B.adjMatrix ℤ * C.adjMatrix ℤ = (⊤ : SimpleGraph V).adjMatrix ℤ) (x y : V) :
    B.degree x = B.degree y := by
  have hc := commute_product h
  rw [adjMatrix_completeGraph_eq_of_one_sub_one, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.one_mul, sub_left_inj] at hc
  have he := congrFun (congrFun hc x) y
  have hcast : (B.degree x : ℤ) = B.degree y := by
    simpa [adjMatrix_mul_apply, mul_adjMatrix_apply] using he
  exact_mod_cast hcast

private theorem even_degree_of_complete_product {V : Type} [Fintype V] [DecidableEq V]
    {B C : SimpleGraph V}
    (h : B.adjMatrix ℤ * C.adjMatrix ℤ = (⊤ : SimpleGraph V).adjMatrix ℤ) (x : V) :
    Even (B.degree x) := by
  let H := C.induce (B.neighborSet x)
  have hdegree (y : B.neighborSet x) : H.degree y = 1 := by
    have hxy : x ≠ y.val := B.ne_of_adj y.property
    have hentry : (B.adjMatrix ℤ * C.adjMatrix ℤ) x y.val = 1 := by
      rw [h]
      simp [hxy]
    have hcount : ((B.neighborFinset x).filter (fun z ↦ C.Adj z y.val)).card = 1 := by
      rw [product_entry] at hentry
      exact_mod_cast hentry
    rw [← card_neighborSet_eq_degree, ← hcount]
    let e : H.neighborSet y ≃
        ((B.neighborFinset x).filter (fun z ↦ C.Adj z y.val) : Finset V) :=
      { toFun := fun z ↦ ⟨z.val.val, Finset.mem_filter.mpr
          ⟨(mem_neighborFinset _ _ _).mpr z.val.property, C.adj_symm z.property⟩⟩
        invFun := fun z ↦ ⟨⟨z.val, (mem_neighborFinset _ _ _).mp
          (Finset.mem_filter.mp z.property).1⟩,
          C.adj_symm (Finset.mem_filter.mp z.property).2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hsum := H.sum_degrees_eq_twice_card_edges
  simp only [hdegree, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    card_neighborSet_eq_degree] at hsum
  exact ⟨H.edgeFinset.card, hsum.trans (Nat.two_mul _)⟩

private theorem complete_card_mod_four {V : Type} [Fintype V] [DecidableEq V] {B C : SimpleGraph V}
    (h : B.adjMatrix ℤ * C.adjMatrix ℤ = (⊤ : SimpleGraph V).adjMatrix ℤ) (x : V) :
    Fintype.card V % 4 = 1 := by
  have hrow (z : V) : ∑ y : V, C.adjMatrix ℤ z y = (C.degree x : ℤ) := by
    simp only [adjMatrix_apply, Finset.sum_boole, ← neighborFinset_eq_filter,
      card_neighborFinset_eq_degree, degree_eq_of_complete_product (reverse_product h) z x]
  have htop : ∑ y : V, (⊤ : SimpleGraph V).adjMatrix ℤ x y = (Fintype.card V - 1 : ℕ) := by
    simp only [adjMatrix_apply, Finset.sum_boole, ← neighborFinset_eq_filter,
      card_neighborFinset_eq_degree]
    exact_mod_cast ((⊤ : SimpleGraph V).degree_eq_card_sub_one x).mpr IsUniversal.top
  have hprod : ((B.degree x : ℤ) * (C.degree x : ℤ)) = (Fintype.card V - 1 : ℕ) := by
    calc
      (B.degree x : ℤ) * (C.degree x : ℤ) =
          ∑ z ∈ B.neighborFinset x, ∑ y : V, C.adjMatrix ℤ z y := by
            simp_rw [hrow]
            simp
      _ = ∑ y : V, (B.adjMatrix ℤ * C.adjMatrix ℤ) x y := by
        simp only [adjMatrix_mul_apply]
        rw [Finset.sum_comm]
      _ = _ := by rw [h, htop]
  obtain ⟨b, hb⟩ := even_degree_of_complete_product h x
  obtain ⟨c, hc⟩ := even_degree_of_complete_product (reverse_product h) x
  have hp : B.degree x * C.degree x = Fintype.card V - 1 := by exact_mod_cast hprod
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hm : Fintype.card V - 1 = 4 * (b * c) := by rw [← hp, hb, hc]; ring
  omega

/-- The residues of the steps in the second factor are the two middle entries of
each block of four. -/
private def middleStep {k : ℕ} (a : ZMod (4 * k + 1)) : Prop :=
  a.val % 4 = 2 ∨ a.val % 4 = 3

private theorem neg_middleStep {k : ℕ} {a : ZMod (4 * k + 1)} (ha : middleStep a) :
    middleStep (-a) := by
  have hlt := ZMod.val_lt a
  have hpos : 0 < a.val := by unfold middleStep at ha; omega
  have : NeZero a := ⟨ZMod.val_pos.mp hpos⟩
  unfold middleStep at *
  rw [ZMod.val_neg_of_ne_zero]
  omega

private def unitSteps (k : ℕ) (hk : 0 < k) : SimpleGraph (ZMod (4 * k + 1)) where
  Adj x y := y - x = -1 ∨ y - x = 1
  symm.symm := by
    intro x y h
    rw [← neg_sub y x]
    rcases h with h | h
    · exact Or.inr (by rw [h, neg_neg])
    · exact Or.inl (by rw [h])
  loopless.irrefl := by
    intro x h
    change x - x = -1 ∨ x - x = 1 at h
    have : Fact (1 < 4 * k + 1) := ⟨by omega⟩
    have hval : (1 : ZMod (4 * k + 1)).val = 1 := ZMod.val_one _
    simp only [sub_self] at h
    rcases h with h | h
    · have hneg : (1 : ZMod (4 * k + 1)) = 0 := by simpa using congrArg Neg.neg h.symm
      rw [hneg, ZMod.val_zero] at hval
      omega
    · rw [← h, ZMod.val_zero] at hval
      omega

private def middleSteps (k : ℕ) : SimpleGraph (ZMod (4 * k + 1)) where
  Adj x y := middleStep (y - x)
  symm.symm := by
    intro x y h
    rw [← neg_sub y x]
    exact neg_middleStep h
  loopless.irrefl := by
    intro x h
    change middleStep (x - x) at h
    simp [middleStep] at h

private theorem step_partition {k : ℕ} (hk : 0 < k) (a : ZMod (4 * k + 1)) :
    (middleStep (a - (-1)) ↔ a.val % 4 = 1 ∨ a.val % 4 = 2) ∧
    (middleStep (a - 1) ↔ a.val % 4 = 3 ∨ (0 < a.val ∧ a.val % 4 = 0)) := by
  have : Fact (1 < 4 * k + 1) := ⟨by omega⟩
  have hlt := ZMod.val_lt a
  have hval : (1 : ZMod (4 * k + 1)).val = 1 := ZMod.val_one _
  constructor
  · rw [sub_neg_eq_add]
    by_cases h : a.val + 1 < 4 * k + 1
    · rw [middleStep, ZMod.val_add, hval, Nat.mod_eq_of_lt h]
      omega
    · have hw : a.val + 1 = 4 * k + 1 := by omega
      rw [middleStep, ZMod.val_add, hval, hw, Nat.mod_self]
      omega
  · by_cases h : a = 0
    · subst a
      have hv : (-1 : ZMod (4 * k + 1)).val = 4 * k := ZMod.val_neg_one _
      simp only [zero_sub, middleStep, hv, ZMod.val_zero]
      omega
    · have ha := ZMod.val_pos.mpr h
      rw [middleStep, ZMod.val_sub (by simpa only [hval] using Nat.succ_le_of_lt ha)]
      rw [hval]
      omega

private theorem unique_intermediate {k : ℕ} (hk : 0 < k) (a : ZMod (4 * k + 1))
    (ha : a ≠ 0) :
    ∃! s : ZMod (4 * k + 1), (s = -1 ∨ s = 1) ∧ middleStep (a - s) := by
  obtain ⟨hminus, hplus⟩ := step_partition hk a
  have hpos := ZMod.val_pos.mpr ha
  by_cases hm : middleStep (a - (-1))
  · refine ⟨-1, ⟨Or.inl rfl, hm⟩, ?_⟩
    rintro s ⟨(rfl | rfl), hs⟩
    · rfl
    · have := hminus.mp hm
      have := hplus.mp hs
      omega
  · have hp : middleStep (a - 1) := by
      have := mt hminus.mpr hm
      apply hplus.mpr
      omega
    refine ⟨1, ⟨Or.inr rfl, hp⟩, ?_⟩
    rintro s ⟨(rfl | rfl), hs⟩
    · exact (hm hs).elim
    · rfl

private theorem cycle_product {k : ℕ} (hk : 0 < k) :
    (unitSteps k hk).adjMatrix ℤ * (middleSteps k).adjMatrix ℤ =
      (⊤ : SimpleGraph (ZMod (4 * k + 1))).adjMatrix ℤ := by
  ext x y
  rw [product_entry]
  have hstep (z : ZMod (4 * k + 1)) : y - z = (y - x) - (z - x) :=
    (sub_sub_sub_cancel_right y z x).symm
  by_cases hxy : x = y
  · subst y
    have hempty : ((unitSteps k hk).neighborFinset x).filter
        (fun z ↦ (middleSteps k).Adj z x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzB, hzC⟩ := Finset.mem_filter.mp hz
      have ht : (z - x = -1 ∨ z - x = 1) := (mem_neighborFinset _ _ _).mp hzB
      change middleStep (x - z) at hzC
      rw [hstep, sub_self] at hzC
      rcases ht with hs | hs
      · have hh := (step_partition hk (0 : ZMod (4 * k + 1))).1.mp (hs ▸ hzC)
        simp at hh
      · have hh := (step_partition hk (0 : ZMod (4 * k + 1))).2.mp (hs ▸ hzC)
        simp at hh
    simp [hempty]
  · have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    obtain ⟨s, hs, hu⟩ := unique_intermediate hk (y - x) hne
    have hcard : (((unitSteps k hk).neighborFinset x).filter
        (fun z ↦ (middleSteps k).Adj z y)).card = 1 := by
      apply Finset.card_eq_one_iff_existsUnique.mpr
      refine ⟨x + s, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · apply (mem_neighborFinset _ _ _).mpr
        change (x + s) - x = -1 ∨ (x + s) - x = 1
        simpa using hs.1
      · change middleStep (y - (x + s))
        rw [hstep]
        simpa using hs.2
      · intro z hz
        obtain ⟨hzB, hzC⟩ := Finset.mem_filter.mp hz
        have hunit : (z - x = -1 ∨ z - x = 1) := (mem_neighborFinset _ _ _).mp hzB
        change middleStep (y - z) at hzC
        rw [hstep] at hzC
        exact sub_eq_iff_eq_add.mp (hu _ ⟨hunit, hzC⟩) |>.trans (add_comm _ _)
    simp [hcard, hxy]

private theorem complete_product_of_card {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card V = 4 * k + 1) :
    ∃ B C : SimpleGraph V, B.adjMatrix ℤ * C.adjMatrix ℤ = (⊤ : SimpleGraph V).adjMatrix ℤ := by
  let e : V ≃ ZMod (4 * k + 1) := Fintype.equivOfCardEq (hcard.trans (ZMod.card _).symm)
  let B := unitSteps k hk
  let C := middleSteps k
  have hcomap (G : SimpleGraph (ZMod (4 * k + 1))) [DecidableRel G.Adj]
      [DecidableRel (G.comap e).Adj] :
      (G.comap e).adjMatrix ℤ = (G.adjMatrix ℤ).submatrix e e := by
    ext
    simp [comap_adj]
  refine ⟨B.comap e, C.comap e, ?_⟩
  calc
    _ = (B.adjMatrix ℤ).submatrix e e * (C.adjMatrix ℤ).submatrix e e :=
      congrArg₂ (· * ·) (hcomap B) (hcomap C)
    _ = (B.adjMatrix ℤ * C.adjMatrix ℤ).submatrix e e :=
      Matrix.submatrix_mul_equiv _ _ e e e
    _ = _ := by
      rw [cycle_product hk]
      ext x y
      simp

/-- The windmill admits a factorization into two simple graph adjacency matrices
over the integers exactly for a single blade of order one modulo four. -/
theorem result (d t : ℕ) (hd : 1 ≤ d) (ht : 3 ≤ t) :
    (∃ B C : SimpleGraph (Option (Fin d × Fin (t - 1))),
      B.adjMatrix ℤ * C.adjMatrix ℤ = (windmill d t).adjMatrix ℤ) ↔
      d = 1 ∧ t % 4 = 1 := by
  have hcard : Fintype.card (Option (Fin 1 × Fin (t - 1))) = t := by
    simp [Fintype.card_option]
    omega
  constructor
  · rintro ⟨B, C, h⟩
    have h₁ := one_blade_of_product hd ht h
    subst d
    rw [one_blade_complete] at h
    have hm := complete_card_mod_four h none
    exact ⟨rfl, hcard ▸ hm⟩
  · rintro ⟨rfl, hm⟩
    rw [one_blade_complete]
    exact complete_product_of_card (t / 4) (by omega) (by rw [hcard]; omega)

end D5.S3.Combinatorics.Graph.AdjacencyProduct.WindmillClassification
