/- GID: D5/S3/Geometry/Hyperideal/ReturnCycleWords
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ReturnCycleWords
   mirror-E: none(waiver:finite-slot-return-cycle)
   anchors: []
   utility: none
   digest: Three face-pairing steps realize the low and high edge return words. -/

import D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

noncomputable section
namespace D5.S3.Geometry.Hyperideal.ReturnCycleWords

open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev edgeClass (u v : G) : Occurrence Ω → Occurrence Ω → Prop :=
  Relation.EqvGen (edgeRel (pairing u v))

/-- The three low-edge slots close with the return word `v⁻¹ * u²`. -/
private theorem low_edge_cycle (u v : G) (x : Ω) :
    edgeClass u v (x, 0) (act x v⁻¹, 3) ∧
    edgeClass u v (act x v⁻¹, 3) (act (act x v⁻¹) u, 5) ∧
    edgeClass u v (act (act x v⁻¹) u, 5)
      (act (act (act x v⁻¹) u) u, 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((x, 2), 2)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act x v⁻¹, 0), 0)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act (act x v⁻¹) u, 0), 2)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩

/-- The three high-edge slots close with the return word `v² * u`. -/
private theorem high_edge_cycle (u v : G) (x : Ω) :
    edgeClass u v (x, 1) (act x v, 2) ∧
    edgeClass u v (act x v, 2) (act (act x v) v, 4) ∧
    edgeClass u v (act (act x v) v, 4)
      (act (act (act x v) v) u, 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((x, 1), 2)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act x v, 1), 1)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩
  · exact Relation.EqvGen.rel _ _ ⟨(((act (act x v) v, 0), 1)), by
      simp [edge, faceEdge], by
      simp [J, pairing, facePair, slotMap, edge, faceEdge]⟩


/-- False is the low-edge family, and true is the high-edge family. -/
def family (j : Fin 6) : Bool := ![false, true, true, false, true, false] j

def baseEdge (high : Bool) : Fin 6 := if high then 1 else 0

def normalizeEdge (u v : G) (a : Occurrence Ω) : Ω :=
  act a.1 (![1, 1, v * u, u ^ 2, u, u] a.2)

def returnWord (u v : G) (high : Bool) : G :=
  if high then v ^ 2 * u else v⁻¹ * u ^ 2

def returnGroup (u v : G) (high : Bool) : Subgroup G :=
  Subgroup.closure ({returnWord u v high} : Set G)

private theorem base_normal (u v : G) (x : Ω) (high : Bool) :
    normalizeEdge u v (x, baseEdge high) = x := by
  cases high <;> simp [normalizeEdge, baseEdge]

private theorem normalize_path (u v : G) (a : Occurrence Ω) :
    edgeClass u v a (normalizeEdge u v a, baseEdge (family a.2)) := by
  rcases a with ⟨x,j⟩
  fin_cases j
  · simpa [normalizeEdge,baseEdge,family] using Relation.EqvGen.refl (x,0)
  · simpa [normalizeEdge,baseEdge,family] using Relation.EqvGen.refl (x,1)
  · simpa [normalizeEdge,baseEdge,family,act_mul] using
      Relation.EqvGen.trans _ _ _ (high_edge_cycle u v (act x v⁻¹)).2.1
        (high_edge_cycle u v (act x v⁻¹)).2.2
  · simpa [normalizeEdge,baseEdge,family,act_mul,pow_two] using
      Relation.EqvGen.trans _ _ _ (low_edge_cycle u v (act x v)).2.1
        (low_edge_cycle u v (act x v)).2.2
  · have h := (high_edge_cycle u v (act x (v^2)⁻¹)).2.2
    simpa [normalizeEdge,baseEdge,family,act_mul,pow_two,mul_assoc] using h
  · simpa [normalizeEdge,baseEdge,family,act_mul] using
      (low_edge_cycle u v (act (act x u⁻¹) v)).2.2

private theorem return_path (u v : G) (high : Bool) (x : Ω) :
    edgeClass u v (x,baseEdge high) (act x (returnWord u v high),baseEdge high) := by
  cases high
  · have h := low_edge_cycle u v x
    simpa [baseEdge,returnWord,act_mul,pow_two,mul_assoc] using
      Relation.EqvGen.trans _ _ _ h.1
        (Relation.EqvGen.trans _ _ _ h.2.1 h.2.2)
  · have h := high_edge_cycle u v x
    simpa [baseEdge,returnWord,act_mul,pow_two,mul_assoc] using
      Relation.EqvGen.trans _ _ _ h.1
        (Relation.EqvGen.trans _ _ _ h.2.1 h.2.2)

private theorem subgroup_path (u v : G) (high : Bool) (g : G)
    (hg : g ∈ returnGroup u v high) (x : Ω) :
    edgeClass u v (x,baseEdge high) (act x g,baseEdge high) := by
  have h : ∀ x : Ω, edgeClass u v (x,baseEdge high) (act x g,baseEdge high) := by
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      have he : g = returnWord u v high := Set.mem_singleton_iff.mp hg
      subst g
      exact return_path u v high
    | one => intro x; simpa using Relation.EqvGen.refl (x,baseEdge high)
    | mul g h hg hh ihg ihh =>
      intro x
      simpa [act_mul] using Relation.EqvGen.trans _ _ _ (ihg x) (ihh (act x g))
    | inv g hg ih =>
      intro x
      simpa [act_mul] using (ih (act x g⁻¹)).symm
  exact h x

private theorem step_invariant (u v : G) (a b : Occurrence Ω)
    (hab : edgeRel (pairing u v) a b) :
    family a.2 = family b.2 ∧
      ∃ g ∈ returnGroup u v (family a.2),
        act (normalizeEdge u v a) g = normalizeEdge u v b := by
  rcases hab with ⟨⟨⟨x,f⟩,r⟩,rfl,rfl⟩
  have mem (high : Bool) : returnWord u v high ∈ returnGroup u v high :=
    Subgroup.subset_closure (by simp)
  fin_cases f <;> fin_cases r
  all_goals simp only [edge,J,pairing,facePair,slotMap,faceEdge,family]
  all_goals refine ⟨rfl, ?_⟩
  · exact ⟨1,(returnGroup u v false).one_mem, by simp [normalizeEdge,slotMap,faceEdge,act_mul,pow_two,mul_assoc]⟩
  · exact ⟨1,(returnGroup u v true).one_mem, by simp [normalizeEdge,slotMap,faceEdge,act_mul]⟩
  · exact ⟨1,by simpa [family] using (returnGroup u v false).one_mem,
      by simp [normalizeEdge,slotMap,faceEdge,act_mul]⟩
  · exact ⟨(returnWord u v false)⁻¹,(returnGroup u v false).inv_mem (mem false), by
      simp [normalizeEdge,slotMap,faceEdge,returnWord,act_mul,mul_assoc]⟩
  · exact ⟨1,(returnGroup u v true).one_mem, by simp [normalizeEdge,slotMap,faceEdge,act_mul,pow_two,mul_assoc]⟩
  · exact ⟨returnWord u v true,mem true, by simp [normalizeEdge,slotMap,faceEdge,returnWord,act_mul,pow_two,mul_assoc]⟩
  · exact ⟨1,(returnGroup u v true).one_mem, by simp [normalizeEdge,slotMap,faceEdge,act_mul,pow_two,mul_assoc]⟩
  · exact ⟨(returnWord u v true)⁻¹,(returnGroup u v true).inv_mem (mem true), by
      simp [normalizeEdge,slotMap,faceEdge,returnWord,act_mul,pow_two,mul_assoc]⟩
  · exact ⟨returnWord u v false,mem false, by simp [normalizeEdge,slotMap,faceEdge,returnWord,act_mul,mul_assoc]⟩
  · exact ⟨1,by simpa [family] using (returnGroup u v false).one_mem,
      by simp [normalizeEdge,slotMap,faceEdge,act_mul,pow_two,mul_assoc]⟩
  · exact ⟨1,by simpa [family] using (returnGroup u v false).one_mem,
      by simp [normalizeEdge,slotMap,faceEdge,act_mul]⟩
  · exact ⟨1,by simpa [family] using (returnGroup u v false).one_mem,
      by simp [normalizeEdge,slotMap,faceEdge,act_mul]⟩

/-- The whole actual edge relation is exactly a low or high cyclic return orbit. -/
theorem actual_edge_orbit_iff (u v : G) (a b : Occurrence Ω) :
    edgeClass u v a b ↔ family a.2 = family b.2 ∧
      ∃ g ∈ returnGroup u v (family a.2),
        act (normalizeEdge u v a) g = normalizeEdge u v b := by
  constructor
  · intro h
    induction h with
    | rel a b h => exact step_invariant u v a b h
    | refl a => exact ⟨rfl,1,(returnGroup u v (family a.2)).one_mem,by simp⟩
    | symm a b h ih =>
      rcases ih with ⟨he,g,hg,ha⟩
      refine ⟨he.symm,g⁻¹,?_,?_⟩
      · rw [← he]; exact (returnGroup u v (family a.2)).inv_mem hg
      · rw [← ha,act_mul]; simp
    | trans a b c hab hbc ihab ihbc =>
      rcases ihab with ⟨he,g,hg,ha⟩
      rcases ihbc with ⟨hf,h,hh,hb⟩
      refine ⟨he.trans hf,g*h,?_,?_⟩
      · rw [← he] at hh
        exact (returnGroup u v (family a.2)).mul_mem hg hh
      · rw [← act_mul,ha,hb]
  · rintro ⟨he,g,hg,ha⟩
    have h := subgroup_path u v (family a.2) g hg (normalizeEdge u v a)
    rw [ha] at h
    have hb := (normalize_path u v b).symm
    rw [← he] at hb
    exact Relation.EqvGen.trans _ _ _ (normalize_path u v a)
      (Relation.EqvGen.trans _ _ _ h hb)

end D5.S3.Geometry.Hyperideal.ReturnCycleWords
