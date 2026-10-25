import CFMPGenericEdgeRectangle1520Transient

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceEveryEdge1522Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate
open D5.S3.Geometry.Gluing.RawFaceEdgeBandRelation1515Candidate
open D5.S3.Geometry.Gluing.RawFaceEdgeRectangle1520Candidate
open D5.S3.Geometry.Gluing.RawFaceInteriorTopology1460Candidate (PointQuotient)
open Topology Set

def edgeFrame (j f : Fin 4) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 j).trans (Equiv.swap ((Equiv.swap 0 j) 2) f)

theorem edgeFrame_values (j f : Fin 4) (h : f ≠ j) :
    edgeFrame j f 0 = j ∧ edgeFrame j f 2 = f := by
  fin_cases j <;> fin_cases f <;> simp [edgeFrame,Equiv.swap_apply_def] at *

theorem positive_band_parameters (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    ∃ a b δ : ℝ, 0 < a ∧ b+δ < 1 ∧ δ ≤ a ∧ b+2*δ ≤ 1 ∧
      0 < δ ∧ a < u ∧ u < b := by
  refine ⟨u/2,(1+u)/2,min u (1-u)/8,?_,?_,?_,?_,?_,?_,?_⟩
  · linarith
  · have h := min_le_right u (1-u);linarith
  · have h := min_le_left u (1-u);linarith
  · have h := min_le_right u (1-u);linarith
  · exact div_pos (lt_min hu (by linarith)) (by norm_num)
  · linarith
  · linarith

variable {T : Type*} [TopologicalSpace T] [DiscreteTopology T]

theorem every_original_edge_chart (P : RawFacePairing T) (ν : Vertex P)
    (x : Point P ν) (f : Fin 4) (hx : EdgePoint P x f) :
    ∃ U : Set (PointQuotient P ν), IsOpen U ∧
      (@Quotient.mk' _ (Relation.EqvGen.setoid (Step P (ν := ν)))) x ∈ U ∧
      ∃ a b δ : ℝ, 0 < δ ∧ Nonempty (↥U ≃ₜ ↥(rectangle a b δ)) := by
  let t := x.val.1.1
  let j := x.val.1.2
  let e := edgeFrame j f
  have he := edgeFrame_values j f hx.1
  have he0 : e 0 = j := he.1
  have he2 : e 2 = f := he.2
  have h0 : x.val.2 (e 0) = 0 := by rw [he0];exact x.property.1
  have h2 : x.val.2 (e 2) = 0 := by rw [he2];exact hx.2.1
  have positive (k : Fin 4) (hk0 : k ≠ 0) (hk2 : k ≠ 2) : 0 < x.val.2 (e k) := by
    have hne0 : e k ≠ j := by rw [← he0];exact e.injective.ne hk0
    have hne2 : e k ≠ f := by rw [← he2];exact e.injective.ne hk2
    have hnz : x.val.2 (e k) ≠ 0 := fun h => hne2 (hx.2.2 _ hne0 h)
    exact lt_of_le_of_ne (x.property.2.1 _) hnz.symm
  let u := x.val.2 (e 1)
  have hu : 0 < u := positive 1 (by decide) (by decide)
  have hv : 0 < x.val.2 (e 3) := positive 3 (by decide) (by decide)
  have hs : (∑ i, x.val.2 (e i)) = 1 :=
    (Fintype.sum_equiv e (fun i => x.val.2 (e i)) x.val.2 (fun _ => rfl)).trans x.property.2.2.1
  simp [Fin.sum_univ_succ,h0,h2] at hs
  have hu1 : u < 1 := by dsimp [u];linarith
  obtain ⟨a,b,δ,ha,hb,hδa,hbδ,hδ,hau,hub⟩ := positive_band_parameters u hu hu1
  have hc : label P (t,e 0) = ν := by rw [he0];exact x.property.2.2.2
  let p : Band a b δ := ⟨(u,0),hau,hub,le_rfl,hδ⟩
  have hp : point P ν t e hc ha hb p = x := by
    apply Subtype.ext
    apply Prod.ext
    · change (t,e 0) = x.val.1
      rw [he0]
    · change coords e (u,0) = x.val.2
      rw [← h2]
      exact coords_inverse e x.val.2 h0 x.property.2.2.1
  refine ⟨quotientBandImage P ν t e hc ha hb,
    (actual_open_edge_quotient P ν t e hc ha hb hδa hbδ).2,?_,a,b,δ,hδ,?_⟩
  · refine ⟨x,?_,rfl⟩
    exact ⟨.inl p,hp⟩
  · exact ⟨originalEdgeRectangleChart P ν t e hc ha hb hδa hbδ hδ⟩

end D5.S3.Geometry.Gluing.RawFaceEveryEdge1522Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceEveryEdge1522Candidate.edgeFrame_values,
      ``D5.S3.Geometry.Gluing.RawFaceEveryEdge1522Candidate.positive_band_parameters,
      ``D5.S3.Geometry.Gluing.RawFaceEveryEdge1522Candidate.every_original_edge_chart] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1522 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1522 disallowed {ax}"
    Lean.logInfo m!"CFMP1522 CHECKED {name} axioms={axioms}"
