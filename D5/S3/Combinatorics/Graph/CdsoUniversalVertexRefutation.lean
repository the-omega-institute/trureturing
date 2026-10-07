/- GID: D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.claim; result=D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.result; claim=D5/S3/Combinatorics/Graph/CdsoUniversalVertexRefutation.claim
   digest: No order-seven unicyclic CDSO minimizer has a universal vertex. -/

/-
proof_shape: result: bind-only (spanning trees, finite minimization and rational normalization).
escape_witness: none
admission_basis: open-problem-resolution (#13438; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.CdsoUniversalVertexRefutation

open SimpleGraph
open scoped BigOperators
noncomputable def cdso {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift ⟨
    (fun u v => Real.sqrt ((G.degree u : ℝ)^2 + (G.degree v : ℝ)^2) /
      max (G.degree u : ℝ) (G.degree v : ℝ)),
    (fun u v => by dsimp; rw [add_comm, max_comm])⟩ e
@[reducible] private def witness : SimpleGraph (Fin 7) := fromEdgeSet
  {s(0,1), s(0,2), s(1,2), s(0,3), s(0,4), s(0,5), s(1,6)}
@[reducible] private def universalModel : SimpleGraph (Fin 7) := fromEdgeSet
  {s(0,1), s(0,2), s(0,3), s(0,4), s(0,5), s(0,6), s(1,2)}

noncomputable def cyclomaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ := by
  classical
  exact sInf {k : ℕ | ∃ s : Finset (Sym2 (Fin n)),
    s ⊆ G.edgeFinset ∧ s.card = k ∧ (G.deleteEdges s).IsAcyclic}

/-- The CDSO half of Albalahi et al.'s Conjecture 4.1. -/
def claim : Prop :=
  ∀ (n ℓ : ℕ), 1 ≤ ℓ → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → cyclomaticNumber G = ℓ →
    (∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.Connected → cyclomaticNumber H = ℓ → cdso G ≤ cdso H) →
    ∃ v : Fin n, ∀ w : Fin n, w ≠ v → G.Adj v w

/-- A finite minimizer exists, and the order-seven witness excludes a universal vertex. -/
theorem result : ¬ claim := by
  have bridge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.Connected) :
      cyclomaticNumber G + n = G.edgeFinset.card + 1 := by
    classical
    have upper : ∃ s : Finset (Sym2 (Fin n)), s ⊆ G.edgeFinset ∧
        s.card + n = G.edgeFinset.card + 1 ∧ (G.deleteEdges s).IsAcyclic := by
      obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
      refine ⟨G.edgeFinset \ T.edgeFinset, Finset.sdiff_subset, ?_, ?_⟩
      · have ht := hT.card_edgeFinset
        have hs := edgeFinset_mono hle
        have := Finset.card_le_card hs
        rw [Finset.card_sdiff_of_subset hs]
        simp only [Fintype.card_fin] at ht
        omega
      · simpa only [Finset.coe_sdiff, coe_edgeFinset,
          G.deleteEdges_sdiff_eq_of_le hle] using hT.isAcyclic
    obtain ⟨s, hs, hc, ha⟩ := upper
    have ne : {k : ℕ | ∃ s : Finset (Sym2 (Fin n)),
        s ⊆ G.edgeFinset ∧ s.card = k ∧ (G.deleteEdges s).IsAcyclic}.Nonempty :=
      ⟨s.card, s, hs, rfl, ha⟩
    have hu : cyclomaticNumber G ≤ s.card := csInf_le' ⟨s, hs, rfl, ha⟩
    have hl : G.edgeFinset.card + 1 - n ≤ cyclomaticNumber G := by
      unfold cyclomaticNumber
      apply le_csInf ne
      rintro k ⟨r, hr, rfl, hra⟩
      obtain ⟨T, hrt, _, hT⟩ :=
        hG.exists_isTree_le_of_le_of_isAcyclic (G.deleteEdges_le r) hra
      have ht := hT.card_edgeFinset
      have he := edgeFinset_mono hrt
      have hh := Finset.card_le_card he
      rw [edgeFinset_deleteEdges, Finset.card_sdiff_of_subset hr] at hh
      simp only [Fintype.card_fin] at ht
      have hle := Finset.card_le_card hr
      omega
    omega
  have iso_index {G H : SimpleGraph (Fin 7)} [DecidableRel G.Adj] [DecidableRel H.Adj]
      (f : G ≃g H) : cdso G = cdso H := by
    classical
    unfold cdso
    apply Finset.sum_bij (fun e _ => e.map f)
    · intro e he
      rw [mem_edgeFinset, f.map_mem_edgeSet_iff]
      exact mem_edgeFinset.mp he
    · intro e he e' he' hh
      exact f.toEquiv.toEmbedding.sym2Map.injective hh
    · intro e he
      refine ⟨e.map f.symm, ?_, ?_⟩
      · rw [mem_edgeFinset, f.symm.map_mem_edgeSet_iff]
        exact mem_edgeFinset.mp he
      · simp only [Sym2.map_map, Function.comp_def, f.apply_symm_apply]
        simp only [Sym2.map_id', id_eq]
    · intro e he
      induction e using Sym2.ind with
      | _ u v => simp only [Sym2.map_mk, Sym2.lift_mk, f.degree_eq]
  have witness_connected : witness.Connected := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨0, ?_⟩
    intro v
    fin_cases v
    · exact Reachable.rfl
    · exact (show witness.Adj 0 1 by decide).reachable
    · exact (show witness.Adj 0 2 by decide).reachable
    · exact (show witness.Adj 0 3 by decide).reachable
    · exact (show witness.Adj 0 4 by decide).reachable
    · exact (show witness.Adj 0 5 by decide).reachable
    · exact (show witness.Adj 0 1 by decide).reachable.trans
        (show witness.Adj 1 6 by decide).reachable
  have witness_edges : ∀ [Fintype witness.edgeSet], witness.edgeFinset =
      {s(0,1), s(0,2), s(1,2), s(0,3), s(0,4), s(0,5), s(1,6)} := by
    intro
    classical
    apply Finset.coe_injective
    simp only [coe_edgeFinset, witness, edgeSet_fromEdgeSet,
      Finset.coe_insert, Finset.coe_singleton]
    apply Disjoint.sdiff_eq_left
    simp only [Set.disjoint_left, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro e he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have witness_value : cdso witness = Real.sqrt 10/3 + Real.sqrt 29/5 + Real.sqrt 34/5 +
      Real.sqrt 13/3 + 3*Real.sqrt 26/5 := by
    have hd : ∀ i : Fin 7, witness.degree i = (if i = 0 then 5 else if i = 1 then 3 else if i = 2 then 2 else 1) := by decide
    unfold cdso
    simp only [witness_edges]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, Sym2.lift_mk, hd]
    norm_num [Fin.ext_iff]
    ring
  have model_value : cdso universalModel = Real.sqrt 2 + 2*Real.sqrt 10/3 + 2*Real.sqrt 37/3 := by
    have he : ∀ [Fintype universalModel.edgeSet], universalModel.edgeFinset =
      {s(0,1), s(0,2), s(0,3), s(0,4), s(0,5), s(0,6), s(1,2)} := by
      intro
      classical
      apply Finset.coe_injective
      simp only [coe_edgeFinset, universalModel, edgeSet_fromEdgeSet,
        Finset.coe_insert, Finset.coe_singleton]
      apply Disjoint.sdiff_eq_left
      simp only [Set.disjoint_left, Set.mem_insert_iff, Set.mem_singleton_iff]
      intro e he
      rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hd : ∀ i : Fin 7, universalModel.degree i = (if i = 0 then 6 else if i = 1 ∨ i = 2 then 2 else 1) := by decide
    unfold cdso
    simp only [he]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, Sym2.lift_mk, hd]
    norm_num [Fin.ext_iff]
    have h40 : Real.sqrt 40 = 2*Real.sqrt 10 := by
      rw [show (40:ℝ) = 2^2*10 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have h8 : Real.sqrt 8 = 2*Real.sqrt 2 := by
      rw [show (8:ℝ) = 2^2*2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [h40,h8]
    ring
  have universal_iso (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
      (hc : G.edgeFinset.card = 7) (v : Fin 7) (hv : ∀ w, w ≠ v → G.Adj v w) :
      Nonempty (universalModel ≃g G) := by
    classical
    have hd : G.degree v = 6 := by
      simpa using (G.degree_eq_card_sub_one v).mpr (by intro w hw; exact hv w hw.symm)
    have hi : (G.incidenceFinset v).card = 6 := by
      rw [card_incidenceFinset_eq_degree, hd]
    obtain ⟨e, he⟩ : ∃ e, G.edgeFinset \ G.incidenceFinset v = {e} :=
      Finset.card_eq_one.mp (by rw [Finset.card_sdiff_of_subset (G.incidenceFinset_subset v), hc, hi])
    have hm : e ∈ G.edgeFinset ∧ e ∉ G.incidenceFinset v := by
      apply Finset.mem_sdiff.mp
      rw [he]
      exact Finset.mem_singleton_self e
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := by simpa only [mem_edgeFinset, mem_edgeSet] using hm.1
      have hav : v ≠ a := by
        intro h
        exact hm.2 ((G.mem_incidenceFinset v _).mpr ((G.mk'_mem_incidenceSet_iff).mpr ⟨hab, Or.inl h⟩))
      have hbv : v ≠ b := by
        intro h
        exact hm.2 ((G.mem_incidenceFinset v _).mpr ((G.mk'_mem_incidenceSet_iff).mpr ⟨hab, Or.inr h⟩))
      have hshape (x y : Fin 7) : G.Adj x y ↔
          x ≠ y ∧ (x = v ∨ y = v ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
        constructor
        · intro hxy
          refine ⟨hxy.ne, ?_⟩
          by_cases hix : x = v
          · exact Or.inl hix
          by_cases hiy : y = v
          · exact Or.inr (Or.inl hiy)
          have hexy : s(x,y) ∈ G.edgeFinset \ G.incidenceFinset v := by
            simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, mem_incidenceFinset,
              mk'_mem_incidenceSet_iff]
            exact ⟨hxy, fun h => h.2.elim (fun hh => hix hh.symm) (fun hh => hiy hh.symm)⟩
          rw [he, Finset.mem_singleton, Sym2.eq_iff] at hexy
          exact Or.inr (Or.inr hexy)
        · rintro ⟨hne, h|h|⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
          · subst x
            exact hv y hne.symm
          · subst y
            exact (hv x hne).symm
          · exact hab
          · exact hab.symm
      have hu (x y : Fin 7) : universalModel.Adj x y ↔
          x ≠ y ∧ (x = 0 ∨ y = 0 ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1)) := by
        fin_cases x <;> fin_cases y <;> decide
      let f : Fin 3 → Fin 7 := fun i => if i = 0 then v else if i = 1 then a else b
      let g : Fin 3 → Fin 7 := fun i => ⟨i.val, by omega⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [f, hab.ne, Ne.symm]
      have hg : Function.Injective g := by
        intro i j hij
        exact Fin.ext (congrArg (fun k : Fin 7 => k.val) hij)
      obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair g f hg hf
      have h0 : σ 0 = v := hσ 0
      have h1 : σ 1 = a := hσ 1
      have h2 : σ 2 = b := hσ 2
      refine ⟨{ σ with map_rel_iff' := ?_ }⟩
      intro x y
      rw [hshape, hu]
      rw [← h0, ← h1, ← h2]
      simp only [σ.injective.eq_iff, ne_eq]
  have separation : cdso witness < cdso universalModel := by
    rw [witness_value, model_value]
    have h29 : Real.sqrt 29 ≤ 5386/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h34 : Real.sqrt 34 ≤ 5831/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h13 : Real.sqrt 13 ≤ 3606/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h26 : Real.sqrt 26 ≤ 5100/1000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h2 : (1414/1000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have h10 : (3162/1000 : ℝ) ≤ Real.sqrt 10 := Real.le_sqrt_of_sq_le (by norm_num)
    have h37 : (6082/1000 : ℝ) ≤ Real.sqrt 37 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have witness_cyclomatic : cyclomaticNumber witness = 1 := by
    have hb := bridge witness witness_connected
    simp only [witness_edges] at hb
    have hcard : ({s(0,1),s(0,2),s(1,2),s(0,3),s(0,4),s(0,5),s(1,6)} :
        Finset (Sym2 (Fin 7))).card = 7 := by decide
    rw [hcard] at hb
    omega
  classical
  let S : Set (SimpleGraph (Fin 7)) :=
    {G | G.Connected ∧ cyclomaticNumber G = 1}
  have hS : S.Nonempty := by
    refine ⟨witness, witness_connected, ?_⟩
    convert witness_cyclomatic using 1; congr 1
  obtain ⟨G, hG, hmin⟩ := Set.exists_min_image S (fun H => cdso H) (Set.toFinite S) hS
  have hGc : G.Connected ∧ cyclomaticNumber G = 1 := hG
  intro hclaim
  obtain ⟨v, hv⟩ := hclaim 7 1 (by decide) G hGc.1 hGc.2 (by
    intro H _ hHc hHl
    have Hmem : H ∈ S := ⟨hHc, by convert hHl using 1; congr 1⟩
    convert hmin H Hmem using 1 <;> congr 1)
  have hGe : G.edgeFinset.card = 7 := by
    have h := bridge G hGc.1
    rw [hGc.2] at h
    omega
  obtain ⟨f⟩ := universal_iso G hGe v hv
  have hle : cdso G ≤ cdso witness := by
    convert hmin witness (by
      refine ⟨witness_connected, ?_⟩
      convert witness_cyclomatic using 1; congr 1) using 1 <;> congr 1
  have hsep : cdso witness < cdso G := by
    rw [← iso_index f]
    exact separation
  exact hsep.not_ge hle

end D5.S3.Combinatorics.Graph.CdsoUniversalVertexRefutation
