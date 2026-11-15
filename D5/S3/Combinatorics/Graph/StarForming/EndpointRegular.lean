/- GID: D5/S3/Combinatorics/Graph/StarForming/EndpointRegular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/EndpointRegular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Arbitrary-degree regular order-bound extremizers with actual attainment. -/

import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity
import D5.S3.Combinatorics.Graph.StarForming.Comparison
import Mathlib.Tactic.Ring
import D5.S3.Combinatorics.Graph.StarForming.FiberConnectivity

/-! The four-part construction in REGULAR_STAR_FORMING_BOUND,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The selected parts have size d, the omitted parts size d-1.
The selected parts are joined by a matching, and each selected part is
complete to the opposite omitted part. These are the order-bound equality
graphs, distinct from the sharp positive-gap graphs of order 4d+2. -/

namespace D5.S3.Combinatorics.Graph.StarForming.EndpointRegular
open StarFormingDissociationRefutation

abbrev Side (d : ℕ) := Fin d ⊕ Fin (d - 1)
abbrev Vertex (d : ℕ) := Bool × Side d

def link {d : ℕ} : Side d → Side d → Prop
  | .inl i, .inl j => i = j
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr _, .inr _ => False

instance {d : ℕ} : DecidableRel (@link d) := fun a b => by
  cases a <;> cases b <;> unfold link <;> infer_instance

def graph (d : ℕ) : SimpleGraph (Vertex d) where
  Adj x y := x.1 ≠ y.1 ∧ link x.2 y.2
  symm := ⟨by
    rintro ⟨b,x⟩ ⟨c,y⟩ ⟨h,hl⟩
    refine ⟨Ne.symm h,?_⟩
    cases x <;> cases y <;> simpa [link,eq_comm] using hl⟩
  loopless := ⟨by simp⟩

instance (d : ℕ) : DecidableRel (graph d).Adj := fun x y =>
  inferInstanceAs (Decidable (x.1 ≠ y.1 ∧ link x.2 y.2))

private def selected (b : Bool) {d : ℕ} (i : Fin d) : Vertex d := (b,.inl i)
private def omitted (b : Bool) {d : ℕ} (i : Fin (d - 1)) : Vertex d := (b,.inr i)

private theorem selected_injective {d : ℕ} (b : Bool) :
    Function.Injective (selected b : Fin d → Vertex d) := by
  intro i j h
  simpa [selected] using h

private theorem omitted_injective {d : ℕ} (b : Bool) :
    Function.Injective (omitted b : Fin (d - 1) → Vertex d) := by
  intro i j h
  simpa [omitted] using h

/-- The displayed bipartition is an actual proper two-coloring. -/
theorem bipartite (d : ℕ) : (graph d).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v.1 then (1 : Fin 2) else 0) ?_⟩
  rintro ⟨b,x⟩ ⟨c,y⟩ h
  cases b <;> cases c <;> simp_all [graph]

private theorem selected_neighbors {d : ℕ} (b : Bool) (i : Fin d) :
    Finset.univ.filter ((graph d).Adj (selected b i)) =
      insert (selected (!b) i) (Finset.univ.image (omitted (!b))) := by
  ext ⟨c,y⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_image]
  change (b ≠ c ∧ link (.inl i) y) ↔ _
  cases b <;> cases c <;> cases y <;> simp [selected,omitted,link,eq_comm]

private theorem omitted_neighbors {d : ℕ} (b : Bool) (i : Fin (d - 1)) :
    Finset.univ.filter ((graph d).Adj (omitted b i)) =
      Finset.univ.image (selected (!b)) := by
  ext ⟨c,y⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  change (b ≠ c ∧ link (.inr i) y) ↔ _
  cases b <;> cases c <;> cases y <;> simp [selected,omitted,link]

/-- Every vertex has exactly the prescribed degree, at every positive d. -/
theorem regular (d : ℕ) (hd : 1 ≤ d) (v : Vertex d) :
    DegreeCapacity.degree (graph d) v = d := by
  rcases v with ⟨b,i | j⟩
  · change (Finset.univ.filter ((graph d).Adj (selected b i))).card=d
    rw [selected_neighbors,Finset.card_insert_of_notMem (by simp [selected,omitted]),
      Finset.card_image_of_injective _ (omitted_injective (!b))]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  · change (Finset.univ.filter ((graph d).Adj (omitted b j))).card=d
    rw [omitted_neighbors,Finset.card_image_of_injective _ (selected_injective (!b))]
    simp

def matching (d : ℕ) : Finset (Vertex d) :=
  Finset.univ.image (fun p : Bool × Fin d => (p.1,Sum.inl p.2))

private theorem mem_matching {d : ℕ} (v : Vertex d) :
    v ∈ matching d ↔ ∃ i : Fin d, v.2=Sum.inl i := by
  rcases v with ⟨b,i | j⟩ <;> simp [matching]

/-- The matching selection really attains cardinality two d. -/
theorem matching_card (d : ℕ) : (matching d).card=2*d := by
  rw [matching,Finset.card_image_of_injective]
  · simp
  · intro a b h
    have h1 : a.1=b.1 := congrArg (fun p : Vertex d => p.1) h
    have h2 : (Sum.inl a.2 : Side d)=Sum.inl b.2 :=
      congrArg (fun p : Vertex d => p.2) h
    exact Prod.ext h1 (Sum.inl.inj h2)

/-- The selected graph is a matching, so every selected vertex has at most
one selected neighbor. This is actual canonical dissociation. -/
theorem matching_independent (d : ℕ) : IsKIndependent (graph d) 2 (matching d) := by
  apply (SubQuorum.DoubleStarGrafting.independent_iff _ _).mpr
  intro v hv a ha b hb hva hvb
  obtain ⟨i,hi⟩ := mem_matching v |>.mp hv
  obtain ⟨j,hj⟩ := mem_matching a |>.mp ha
  obtain ⟨k,hk⟩ := mem_matching b |>.mp hb
  rcases v with ⟨c,x⟩; rcases a with ⟨e,y⟩; rcases b with ⟨f,z⟩
  dsimp at hi hj hk
  subst x; subst y; subst z
  cases c <;> cases e <;> cases f <;> simp_all [graph,link]

/-- Both actual finite maxima equal two d. The lower bound uses the displayed
matching, and the upper bound uses the general regular degree capacity. -/
theorem parameters (d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (Vertex d)=4*d-2 ∧
      beta (graph d) 2=2*d ∧ SF (graph d) 2=2*d := by
  have ho : Fintype.card (Vertex d)=4*d-2 := by
    simp only [Vertex,Side,Fintype.card_prod,Fintype.card_bool,Fintype.card_sum,
      Fintype.card_fin]
    omega
  have hl : 2*d ≤ beta (graph d) 2 := by
    rw [← matching_card d]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,matching_independent d⟩)
  have hc := beta_le_sf (graph d)
  have hu := DegreeCapacity.sf_regular_bound (graph d) d (by omega) (regular d (by omega))
  rw [ho] at hu
  have hm : d*(4*d-2)/(2*d-1)=2*d := by
    have hp : 0<2*d-1 := by omega
    have ht : 4*d-2=2*(2*d-1) := by omega
    rw [ht]
    calc
      d*(2*(2*d-1))/(2*d-1) = (2*d)*(2*d-1)/(2*d-1) := by congr 1; ring
      _ = 2*d := Nat.mul_div_cancel _ hp
  rw [hm] at hu
  exact ⟨ho,by omega,by omega⟩

private abbrev Avoid (d : ℕ) (z : Vertex d) := (graph d).induce {v | v ≠ z}

private theorem mate_edge {d : ℕ} (b : Bool) (i : Fin d) :
    (graph d).Adj (selected b i) (selected (!b) i) := by
  cases b <;> simp [graph,selected,link]

private theorem cross_edge {d : ℕ} (b : Bool) (i : Fin d) (j : Fin (d - 1)) :
    (graph d).Adj (selected b i) (omitted (!b) j) := by
  cases b <;> simp [graph,selected,omitted,link]

private theorem step {d : ℕ} (z a b : Vertex d)
    (ha : a ≠ z) (hb : b ≠ z) (he : (graph d).Adj a b) :
    (Avoid d z).Reachable ⟨a,ha⟩ ⟨b,hb⟩ :=
  (show (Avoid d z).Adj ⟨a,ha⟩ ⟨b,hb⟩ from he).reachable

private theorem same_selected {d : ℕ} (hd : 2 ≤ d) (z : Vertex d)
    (b : Bool) (i j : Fin d) (hi : selected b i ≠ z) (hj : selected b j ≠ z) :
    (Avoid d z).Reachable ⟨selected b i,hi⟩ ⟨selected b j,hj⟩ := by
  let o : Fin (d - 1) := ⟨0,by omega⟩
  by_cases ho : omitted (!b) o = z
  · have hoi : selected (!b) i ≠ z := by
      intro h; have he := h.trans ho.symm; simp [selected,omitted] at he
    have hoj : selected (!b) j ≠ z := by
      intro h; have he := h.trans ho.symm; simp [selected,omitted] at he
    have hob : omitted b o ≠ z := by
      intro h
      have he := congrArg Prod.fst (h.trans ho.symm)
      cases b <;> simp [omitted] at he
    exact (step z _ _ hi hoi (mate_edge b i)).trans
      ((step z _ _ hoi hob (by simpa using cross_edge (!b) i o)).trans
        ((step z _ _ hoj hob (by simpa using cross_edge (!b) j o)).symm.trans
          (step z _ _ hj hoj (mate_edge b j)).symm))
  · exact (step z _ _ hi ho (cross_edge b i o)).trans
      (step z _ _ hj ho (cross_edge b j o)).symm

private theorem opposite_selected {d : ℕ} (hd : 2 ≤ d) (z : Vertex d)
    (b : Bool) (i j : Fin d) (hi : selected b i ≠ z) (hj : selected (!b) j ≠ z) :
    (Avoid d z).Reachable ⟨selected b i,hi⟩ ⟨selected (!b) j,hj⟩ := by
  by_cases hk : selected b j = z
  · have hm : selected (!b) i ≠ z := by
      intro he
      have h := congrArg Prod.fst (he.trans hk.symm)
      cases b <;> simp [selected] at h
    exact (step z _ _ hi hm (mate_edge b i)).trans
      (same_selected hd z (!b) i j hm hj)
  · exact (same_selected hd z b i j hi hk).trans
      (step z _ _ hk hj (mate_edge b j))

private theorem all_selected {d : ℕ} (hd : 2 ≤ d) (z : Vertex d)
    (b c : Bool) (i j : Fin d) (hi : selected b i ≠ z) (hj : selected c j ≠ z) :
    (Avoid d z).Reachable ⟨selected b i,hi⟩ ⟨selected c j,hj⟩ := by
  cases b <;> cases c
  · exact same_selected hd z false i j hi hj
  · exact opposite_selected hd z false i j hi hj
  · exact opposite_selected hd z true i j hi hj
  · exact same_selected hd z true i j hi hj

/-- Each actual vertex deletion leaves the graph connected. In degree two,
if the sole omitted vertex in one piece is deleted, the other piece and
matching edges give the required detour. -/
theorem delete_preconnected (d : ℕ) (hd : 2 ≤ d) (z : Vertex d) :
    ((graph d).induce {v | v ≠ z}).Preconnected := by
  have hr (v : {v : Vertex d // v ≠ z}) : ∃ b i, ∃ hi : selected b i ≠ z,
      (Avoid d z).Reachable v ⟨selected b i,hi⟩ := by
    rcases v with ⟨⟨b,i | j⟩,hv⟩
    · exact ⟨b,i,hv,.refl _⟩
    · let i0 : Fin d := ⟨0,by omega⟩
      let i1 : Fin d := ⟨1,by omega⟩
      have hn : selected (!b) i0 ≠ selected (!b) i1 := by
        intro h
        have he := congrArg Fin.val (selected_injective (!b) h)
        simp [i0,i1] at he
      rcases FiberConnectivity.surviving_pair (selected (!b) i0) (selected (!b) i0)
        (selected (!b) i1) (selected (!b) i1) z hn hn hn hn with ⟨h,_⟩ | ⟨h,_⟩
      · exact ⟨!b,i0,h,step z _ _ hv h (by simpa only [Bool.not_not,omitted] using (cross_edge (!b) i0 j).symm)⟩
      · exact ⟨!b,i1,h,step z _ _ hv h (by simpa only [Bool.not_not,omitted] using (cross_edge (!b) i1 j).symm)⟩
  intro v w
  obtain ⟨b,i,hi,hv⟩ := hr v
  obtain ⟨c,j,hj,hw⟩ := hr w
  exact hv.trans ((all_selected hd z b c i j hi hj).trans hw.symm)

/-- The endpoint graphs are two-connected at every degree d at least two,
with graph order at least three explicitly included. -/
theorem two_connected (d : ℕ) (hd : 2 ≤ d) :
    (graph d).Connected ∧
      (∀ z : Vertex d, ((graph d).induce {v | v ≠ z}).Connected) ∧
      3 ≤ Fintype.card (Vertex d) := by
  classical
  have hc : 3 ≤ Fintype.card (Vertex d) := by rw [(parameters d (by omega)).1]; omega
  have full : (graph d).Preconnected := by
    intro a b
    have hp : ({a,b} : Finset (Vertex d)).card ≤ 2 := by
      by_cases h : a=b <;> simp [h]
    obtain ⟨z,_,hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a,b}) (t := Finset.univ) (by simp only [Finset.card_univ]; omega)
    have hza : a≠z := by simpa [ne_comm] using (show z≠a from fun h => hz (by simp [h]))
    have hzb : b≠z := by simpa [ne_comm] using (show z≠b from fun h => hz (by simp [h]))
    let f : ((graph d).induce {v | v≠z}) →g graph d := ⟨fun v => v.val,fun h => h⟩
    exact ((delete_preconnected d hd z) ⟨a,hza⟩ ⟨b,hzb⟩).map f
  let i : Fin d := ⟨0,by omega⟩
  refine ⟨{preconnected := full, nonempty := ⟨selected false i⟩},?_,hc⟩
  intro z
  have hn : selected false i ≠ selected true i := by simp [selected]
  rcases FiberConnectivity.surviving_pair (selected false i) (selected false i)
    (selected true i) (selected true i) z hn hn hn hn with ⟨hv,_⟩ | ⟨hv,_⟩
  all_goals exact {preconnected := delete_preconnected d hd z,nonempty := ⟨⟨_,hv⟩⟩}

end D5.S3.Combinatorics.Graph.StarForming.EndpointRegular
