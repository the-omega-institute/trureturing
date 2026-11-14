/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodLift
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual Heawood binary lifts, switching transport and connectedness. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodSwitching
import D5.S3.Combinatorics.Graph.StarForming.BinaryLift

/-! The actual flag graph and two-sheet construction from
HEAWOOD_DOUBLE_COVER_GAIN at subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
All twenty-one signing coordinates are retained. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodLift
open HeawoodSwitching

abbrev Vertex := Fin 14

def point (e : Fin 21) : Vertex := ⟨(flags e).1.val,by have := (flags e).1.isLt; omega⟩
def line (e : Fin 21) : Vertex := ⟨7+(flags e).2.val,by have := (flags e).2.isLt; omega⟩

def incident (e : Fin 21) (v w : Vertex) : Prop :=
  (v=point e ∧ w=line e) ∨ (w=point e ∧ v=line e)
instance (e : Fin 21) (v w : Vertex) : Decidable (incident e v w) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))

def base : SimpleGraph Vertex where
  Adj v w := ∃ e : Fin 21, incident e v w
  symm := ⟨by intro v w ⟨e,he⟩; exact ⟨e,he.symm⟩⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel base.Adj := fun _ _ => inferInstanceAs (Decidable (∃ e : Fin 21, _))

def edgeIndex (v w : Vertex) : Fin 21 :=
  ((List.finRange 21).find? (fun e => decide (incident e v w))).getD 0

private theorem index_endpoints : ∀ v w : Vertex, base.Adj v w →
    incident (edgeIndex v w) v w := by decide +kernel
private theorem index_flag : ∀ e : Fin 21, edgeIndex (point e) (line e)=e := by decide +kernel
private theorem index_symm : ∀ v w : Vertex, edgeIndex v w=edgeIndex w v := by decide +kernel

/-- The fixed flag graph is connected, using actual paths of length at most three. -/
theorem base_preconnected : base.Preconnected := by
  have hp : ∀ v w : Vertex, v=w ∨ base.Adj v w ∨
      (∃ x : Vertex, base.Adj v x ∧ base.Adj x w) ∨
      (∃ x y : Vertex, base.Adj v x ∧ base.Adj x y ∧ base.Adj y w) := by
    decide +kernel
  intro v w
  rcases hp v w with rfl | h | ⟨x,hvx,hxw⟩ | ⟨x,y,hvx,hxy,hyw⟩
  · exact .rfl
  · exact h.reachable
  · exact hvx.reachable.trans hxw.reachable
  · exact hvx.reachable.trans (hxy.reachable.trans hyw.reachable)

def voltage (s : Signing) : BinaryLift.Voltage base where
  sign v w := s (edgeIndex v w)
  symmetric v w _ := congrArg s (index_symm v w)

abbrev graph (s : Signing) := BinaryLift.graph base (voltage s)

private theorem switching_index (t : Switches) (v w : Vertex) (h : base.Adj v w) :
    switching t (edgeIndex v w)=t v+t w := by
  change t (point (edgeIndex v w))+t (line (edgeIndex v w))=t v+t w
  rcases index_endpoints v w h with ⟨hv,hw⟩ | ⟨hw,hv⟩
  · rw [← hv,← hw]
  · rw [← hv,← hw,add_comm]

/-- The full matrix kernel is exactly the actual graph's vertex coboundaries. -/
theorem coboundary_iff (s : Signing) :
    (∃ t : Switches, ∀ v w, base.Adj v w → s (edgeIndex v w)=t v+t w) ↔ phi s=0 := by
  constructor
  · rintro ⟨t,ht⟩
    have he : s=switching t := by
      funext e
      have h := ht (point e) (line e) ⟨e,Or.inl ⟨rfl,rfl⟩⟩
      change s e=t (point e)+t (line e)
      simpa only [index_flag] using h
    rw [he,phi_switching]
  · intro hs
    have hm : s ∈ LinearMap.range switching := by
      rw [← kernel_phi_eq_switching]
      exact hs
    obtain ⟨t,ht⟩ := hm
    refine ⟨t,?_⟩
    intro v w hvw
    rw [← ht]
    exact switching_index t v w hvw

/-- Connectivity of every signing is detected by its actual matrix invariant. -/
theorem preconnected_iff (s : Signing) : (graph s).Preconnected ↔ phi s≠0 := by
  rw [BinaryLift.preconnected_iff base (voltage s) base_preconnected 0]
  exact not_congr (coboundary_iff s)

/-- Equal invariants give an actual sheet-switching graph isomorphism. -/
theorem isomorphic_of_phi_eq (s t : Signing) (h : phi s=phi t) :
    Nonempty (graph s ≃g graph t) := by
  classical
  have hzero : phi (s+t)=0 := by
    rw [map_add,h]
    ext i j
    change phi t i j+phi t i j=0
    have hc : ∀ a : F2, a+a=0 := by decide +kernel
    exact hc _
  obtain ⟨u,hu⟩ := (coboundary_iff (s+t)).mpr hzero
  have he : BinaryLift.graph base (BinaryLift.switched base (voltage s) u)=graph t := by
    apply SimpleGraph.ext
    funext v w
    apply propext
    change (base.Adj v.1 w.1 ∧ v.2+w.2=s (edgeIndex v.1 w.1)+u v.1+u w.1) ↔
      (base.Adj v.1 w.1 ∧ v.2+w.2=t (edgeIndex v.1 w.1))
    by_cases hvw : base.Adj v.1 w.1
    · have hc : ∀ a b c d : F2, a+b=c+d → a+c+d=b := by decide +kernel
      rw [hc _ _ _ _ (hu _ _ hvw)]
    · simp [hvw]
  have e := BinaryLift.switchIso base (voltage s) u
  rw [he] at e
  exact ⟨e⟩

/-- Read the actual edge voltage on the original twenty-one Fano flags. -/
def signingOfVoltage (s : BinaryLift.Voltage base) : Signing :=
  fun e => s.sign (point e) (line e)

/-- Every symmetric voltage on the actual base has exactly the original
signing representation, including both orientations of every incidence. -/
def voltageIso (s : BinaryLift.Voltage base) :
    BinaryLift.graph base s ≃g graph (signingOfVoltage s) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro x y
    have hs (v w : Vertex) (h : base.Adj v w) :
        signingOfVoltage s (edgeIndex v w)=s.sign v w := by
      change s.sign (point (edgeIndex v w)) (line (edgeIndex v w))=s.sign v w
      rcases index_endpoints v w h with ⟨hv,hw⟩ | ⟨hw,hv⟩
      · rw [← hv,← hw]
      · rw [← hv,← hw]
        exact s.symmetric w v (base.adj_symm h)
    change (base.Adj x.1 y.1 ∧ x.2+y.2=signingOfVoltage s (edgeIndex x.1 y.1)) ↔
      (base.Adj x.1 y.1 ∧ x.2+y.2=s.sign x.1 y.1)
    by_cases h : base.Adj x.1 y.1
    · rw [hs _ _ h]
    · simp [h]

end D5.S3.Combinatorics.Graph.StarForming.HeawoodLift
