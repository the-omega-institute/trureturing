/- GID: D5/S3/Combinatorics/Graph/ZeroForcing/ContingentThreshold
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroForcing/ContingentThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DeleteEdges, mathlib/module/Mathlib.Data.ENat.Lattice]
   utility: none
   digest: Fixed edge faults are characterized by the minimum unique-neighbour boundary. -/
import D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.ENat.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.ZeroForcing.ContingentThreshold

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThree
open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The original blue-source rule, with the target required to be white. -/
def LegalForce (G : SimpleGraph V) (B : Finset V) (u w : V) : Prop :=
  u ∈ B ∧ w ∉ B ∧ G.Adj u w ∧ ∀ x, G.Adj u x → x ≠ w → x ∈ B

/-- A finite chronological run, including its exact initial and terminal sets. -/
inductive LegalRun (G : SimpleGraph V) : Finset V → List (V × V) → Finset V → Prop
  | nil (B) : LegalRun G B [] B
  | cons {B L T u w} : LegalForce G B u w → LegalRun G (insert w B) L T →
      LegalRun G B ((u,w) :: L) T

private theorem run_sound {G : SimpleGraph V} {B T : Finset V} {L : List (V × V)}
    (h : LegalRun G B L T) : ∀ x ∈ T, Black G (B : Set V) x := by
  induction h with
  | nil B => exact fun _ hx => .init hx
  | @cons B L T u w hf hr ih =>
    intro x hx
    apply Black.bind (T := (insert w B : Finset V)) ?_ (ih x hx)
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact .force (.init hf.1) hf.2.2.1 (fun z hz hzw => .init (hf.2.2.2 z hz hzw))
    · exact .init hy

/-- Pointwise inductive closure serializes into a finite legal blue-source list. -/
theorem chronological_iff_zero_forcing (G : SimpleGraph V) (S : Finset V) :
    (∃ L, LegalRun G S L Finset.univ) ↔ IsZeroForcing G (S : Set V) := by
  constructor
  · rintro ⟨L, hL⟩ v
    exact run_sound hL v (Finset.mem_univ v)
  · intro hz
    suffices h : ∀ n (B : Finset V), Fintype.card V - B.card = n →
        IsZeroForcing G (B : Set V) → ∃ L, LegalRun G B L Finset.univ from h _ S rfl hz
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro B hn hb
      by_cases hB : B = Finset.univ
      · subst B
        exact ⟨[], .nil _⟩
      · have hv : ∃ v, v ∉ B := by
          by_contra h
          push Not at h
          exact hB (Finset.eq_univ_of_forall h)
        obtain ⟨v, hv⟩ := hv
        obtain ⟨u, w, hu, hw, huw, hall⟩ := Black.exists_initial_force (hb v) hv
        have hlt : Fintype.card V - (insert w B).card < n := by
          have hcard := Finset.card_le_univ (s := insert w B)
          rw [Finset.card_insert_of_notMem hw] at hcard ⊢
          omega
        have hb' : IsZeroForcing G ((insert w B : Finset V) : Set V) :=
          fun x => Black.mono (fun _ hx => Finset.mem_insert_of_mem hx) (hb x)
        obtain ⟨L, hL⟩ := ih _ hlt (insert w B) rfl hb'
        exact ⟨(u,w) :: L, .cons ⟨hu, hw, huw, hall⟩ hL⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Outside vertices with exactly one neighbour in the white set. -/
def boundary (W : Finset V) : Finset V :=
  Finset.univ.filter fun u => u ∉ W ∧ (finiteNeighbors G u ∩ W).card = 1

private noncomputable def target (W : Finset V) (u : {u // u ∈ boundary G W}) : V :=
  Classical.choose (Finset.card_eq_one.mp (Finset.mem_filter.mp u.property).2.2)

private theorem target_eq (W : Finset V) (u : {u // u ∈ boundary G W}) :
    finiteNeighbors G u.val ∩ W = {target G W u} :=
  Classical.choose_spec (Finset.card_eq_one.mp (Finset.mem_filter.mp u.property).2.2)

private theorem target_mem (W : Finset V) (u : {u // u ∈ boundary G W}) :
    G.Adj u.val (target G W u) ∧ target G W u ∈ W := by
  have h : target G W u ∈ finiteNeighbors G u.val ∩ W := by rw [target_eq]; simp
  simpa [finiteNeighbors] using h

/-- Exactly the mandatory crossing edges, one for each unique-neighbour outside vertex. -/
noncomputable def criticalEdges (W : Finset V) : Finset (Sym2 V) :=
  (boundary G W).attach.image fun u => s(u.val, target G W u)

private theorem critical_card (W : Finset V) :
    (criticalEdges G W).card = (boundary G W).card := by
  classical
  rw [criticalEdges, Finset.card_image_of_injOn, Finset.card_attach]
  intro u hu v hv he
  rcases Sym2.eq_iff.mp he with h | h
  · exact Subtype.ext h.1
  · exact False.elim ((Finset.mem_filter.mp u.property).2.1
      (h.1 ▸ (target_mem G W v).2))

private theorem critical_subset (W : Finset V) :
    (criticalEdges G W : Set (Sym2 V)) ⊆ G.edgeSet := by
  classical
  intro e he
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
  exact (SimpleGraph.mem_edgeSet G).mpr (target_mem G W u).1

private theorem crossing_critical (W : Finset V) {u w : V}
    (hu : u ∉ W) (hw : w ∈ W) (huw : G.Adj u w) :
    s(u,w) ∈ criticalEdges G W ↔ u ∈ boundary G W := by
  classical
  constructor
  · intro he
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp he
    rcases Sym2.eq_iff.mp he with h | h
    · simpa [← h.1] using v.property
    · exact False.elim (hu (h.2 ▸ (target_mem G W v).2))
  · intro hb
    let v : {u // u ∈ boundary G W} := ⟨u, hb⟩
    have ht : w = target G W v := by
      have hm : w ∈ finiteNeighbors G u ∩ W := by simp [finiteNeighbors, huw, hw]
      rw [target_eq G W v] at hm
      exact Finset.mem_singleton.mp hm
    exact Finset.mem_image.mpr ⟨v, Finset.mem_attach _ _, by simp [v, ht]⟩

/-- The exact critical deletion makes a fort; any deletion making that fort is at least as large. -/
theorem critical_edges_fort_minimality (W : Finset V) (hW : W.Nonempty) :
    (criticalEdges G W : Set (Sym2 V)) ⊆ G.edgeSet ∧
    (criticalEdges G W).card = (boundary G W).card ∧
    IsFort (G.deleteEdges (criticalEdges G W : Set (Sym2 V))) W ∧
    ∀ F : Finset (Sym2 V), IsFort (G.deleteEdges (F : Set (Sym2 V))) W →
      criticalEdges G W ⊆ F := by
  classical
  refine ⟨critical_subset G W, critical_card G W, ⟨hW, ?_⟩, ?_⟩
  · intro u hu
    by_cases hb : u ∈ boundary G W
    · have he : finiteNeighbors (G.deleteEdges (criticalEdges G W : Set (Sym2 V))) u ∩ W = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have h : G.Adj u w ∧ s(u,w) ∉ criticalEdges G W ∧ w ∈ W := by
          simpa [finiteNeighbors, SimpleGraph.deleteEdges_adj, and_assoc] using hw
        exact h.2.1 ((crossing_critical G W hu h.2.2 h.1).2 hb)
      simp [he]
    · have he : finiteNeighbors (G.deleteEdges (criticalEdges G W : Set (Sym2 V))) u ∩ W =
          finiteNeighbors G u ∩ W := by
        ext w
        simp only [Finset.mem_inter, finiteNeighbors, Finset.mem_filter, Finset.mem_univ,
          true_and, SimpleGraph.deleteEdges_adj]
        constructor
        · exact fun h => ⟨h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.1, fun he => hb ((crossing_critical G W hu h.2 h.1).1 he)⟩, h.2⟩
      rw [he]
      intro hc
      exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hc⟩)
  · intro F hF e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    by_contra hn
    apply hF.2 u.val (Finset.mem_filter.mp u.property).2.1
    have heq : finiteNeighbors (G.deleteEdges (F : Set (Sym2 V))) u.val ∩ W =
        {target G W u} := by
      ext w
      constructor
      · intro hw
        have ha : (G.deleteEdges (F : Set (Sym2 V))).Adj u.val w := by
          simpa only [finiteNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] using
            (Finset.mem_inter.mp hw).1
        have hm : w ∈ finiteNeighbors G u.val ∩ W := by
          exact Finset.mem_inter.mpr ⟨by simp [finiteNeighbors,
            (SimpleGraph.deleteEdges_adj.mp ha).1], (Finset.mem_inter.mp hw).2⟩
        rwa [target_eq G W u] at hm
      · intro hw
        have hwt := Finset.mem_singleton.mp hw
        subst w
        simpa [finiteNeighbors, SimpleGraph.deleteEdges_adj, and_assoc] using
          (show G.Adj u.val (target G W u) ∧ s(u.val,target G W u) ∉ F ∧
            target G W u ∈ W from ⟨(target_mem G W u).1, hn, (target_mem G W u).2⟩)
    rw [heq]
    simp

private theorem closure_complement_fort (S : Finset V)
    (hz : ¬ IsZeroForcing G (S : Set V)) :
    ∃ W : Finset V, IsFort G W ∧ Disjoint S W := by
  classical
  let W := Finset.univ.filter fun v => ¬ Black G (S : Set V) v
  have hm (v : V) : v ∈ W ↔ ¬ Black G (S : Set V) v := by simp [W]
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · by_contra hn
    apply hz
    intro v
    by_contra hv
    exact hn ⟨v, (hm v).2 hv⟩
  · intro u hu hc
    have hbu : Black G (S : Set V) u := by
      by_contra h
      exact hu ((hm u).2 h)
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
    have hwW : w ∈ W := (Finset.mem_inter.mp (by rw [hw]; simp)).2
    apply (hm w).1 hwW
    apply Black.force hbu
    · have : w ∈ finiteNeighbors G u := (Finset.mem_inter.mp (by rw [hw]; simp)).1
      simpa [finiteNeighbors] using this
    · intro x hux hxw
      by_contra hx
      have hxmem : x ∈ finiteNeighbors G u ∩ W := by simp [finiteNeighbors, hux, (hm x).2 hx]
      rw [hw] at hxmem
      exact hxw (Finset.mem_singleton.mp hxmem)
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (hm v).1 hw (.init hv)

/-- Faults are fixed throughout each run; the run may depend on the fault set. -/
def Contingent (S : Finset V) (k : ℕ) : Prop :=
  ∀ F : Finset (Sym2 V), (F : Set (Sym2 V)) ⊆ G.edgeSet → F.card ≤ k →
    ∃ L, LegalRun (G.deleteEdges (F : Set (Sym2 V))) S L Finset.univ

/-- The empty obstruction family has value infinity. -/
noncomputable def lambda (S : Finset V) : ℕ∞ :=
  ⨅ W : {W : Finset V // W.Nonempty ∧ Disjoint S W}, ((boundary G W.val).card : ℕ∞)

private theorem lambda_gt_iff (S : Finset V) (k : ℕ) :
    (k : ℕ∞) < lambda G S ↔
      ∀ W : Finset V, W.Nonempty → Disjoint S W → k < (boundary G W).card := by
  classical
  let A := {W : Finset V // W.Nonempty ∧ Disjoint S W}
  constructor
  · intro h W hw hd
    have hi : lambda G S ≤ ((boundary G W).card : ℕ∞) := iInf_le _ (⟨W,hw,hd⟩ : A)
    exact ENat.natCast_lt_natCast.mp (h.trans_le hi)
  · intro h
    cases isEmpty_or_nonempty A with
    | inl he =>
      letI := he
      simpa [lambda, A] using ENat.natCast_lt_top k
    | inr he =>
      letI := he
      obtain ⟨W, hW⟩ := ENat.exists_eq_iInf (fun W : A => ((boundary G W.val).card : ℕ∞))
      change (k : ℕ∞) < ⨅ W : A, ((boundary G W.val).card : ℕ∞)
      rw [← hW]
      exact ENat.natCast_lt_natCast.mpr (h W.val W.property.1 W.property.2)

/-- Equation (2.2), with the stronger domain of all finite graphs and natural fault budgets. -/
theorem contingent_iff_lambda_gt (S : Finset V) (k : ℕ) :
    Contingent G S k ↔ (k : ℕ∞) < lambda G S := by
  classical
  rw [lambda_gt_iff]
  constructor
  · intro hc W hw hd
    by_contra hn
    have hle : (boundary G W).card ≤ k := Nat.le_of_not_gt hn
    obtain ⟨hsub, hcard, hfort, hmin⟩ := critical_edges_fort_minimality G W hw
    obtain ⟨L, hL⟩ := hc (criticalEdges G W) hsub (hcard.trans_le hle)
    have hz := (chronological_iff_zero_forcing _ S).1 ⟨L,hL⟩
    obtain ⟨w, hw⟩ := hw
    exact IsFort.not_black_of_disjoint _ S W hfort hd hw (hz w)
  · intro hb F hF hk
    apply (chronological_iff_zero_forcing _ S).2
    by_contra hz
    obtain ⟨W, hfort, hd⟩ := closure_complement_fort (G.deleteEdges (F : Set (Sym2 V))) S hz
    obtain ⟨hsub, hcard, hcrit, hmin⟩ := critical_edges_fort_minimality G W hfort.1
    have hle : (boundary G W).card ≤ F.card := by
      rw [← hcard]
      exact Finset.card_le_card (hmin F hfort)
    exact (Nat.not_lt_of_ge (hle.trans hk)) (hb W hfort.1 hd)

#print axioms chronological_iff_zero_forcing
#print axioms critical_edges_fort_minimality
#print axioms contingent_iff_lambda_gt

end D5.S3.Combinatorics.Graph.ZeroForcing.ContingentThreshold
