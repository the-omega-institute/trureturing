import CFMPRawFaceCapSlice1053Transient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open private sigma_face sigma_inverse paired_twice from CFMPRawFaceCapSlice1053Transient
variable {T : Type*}

def Interior (P : RawFacePairing T) {ν : Vertex P} (x : Point P ν) : Prop :=
  ∀ f, f ≠ x.val.1.2 → x.val.2 f ≠ 0

def EdgePoint (P : RawFacePairing T) {ν : Vertex P}
    (x : Point P ν) (f : Fin 4) : Prop :=
  f ≠ x.val.1.2 ∧ x.val.2 f = 0 ∧
    ∀ g, g ≠ x.val.1.2 → x.val.2 g = 0 → g = f

theorem move_inverse (P : RawFacePairing T) (f : Fin 4) (x : Raw T) :
    move P (P.facePair (x.1.1,f)).2 (move P f x) = x := by
  have hp := paired_twice P (x.1.1,f)
  have hi := sigma_inverse P (x.1.1,f)
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · change (P.facePair (P.facePair (x.1.1,f))).1 = x.1.1
    rw [hp]
  · change sigma P (P.facePair (x.1.1,f)) (sigma P (x.1.1,f) x.1.2) = x.1.2
    rw [hi]
    exact Equiv.symm_apply_apply _ _
  · funext i
    change x.2 ((sigma P (x.1.1,f)).symm
      ((sigma P (P.facePair (x.1.1,f))).symm i)) = x.2 i
    rw [hi]
    simp

theorem step_symmetric (P : RawFacePairing T) {ν : Vertex P}
    {x y : Point P ν} (h : Step P x y) : Step P y x := by
  obtain ⟨f,hfj,hf,hy⟩ := h
  let g := (P.facePair (x.val.1.1,f)).2
  refine ⟨g,?_,?_,?_⟩
  · rw [hy]
    change g ≠ sigma P (x.val.1.1,f) x.val.1.2
    rw [show g = sigma P (x.val.1.1,f) f from (sigma_face P _).symm]
    exact (sigma P _).injective.ne hfj
  · rw [hy]
    change x.val.2 ((sigma P (x.val.1.1,f)).symm g) = 0
    rw [show g = sigma P (x.val.1.1,f) f from (sigma_face P _).symm,
      Equiv.symm_apply_apply]
    exact hf
  · rw [hy,move_inverse]

theorem step_unique (P : RawFacePairing T) {ν : Vertex P}
    {x y z : Point P ν} {f : Fin 4} (hx : EdgePoint P x f)
    (hy : Step P x y) (hz : Step P x z) : y = z := by
  obtain ⟨g,hgj,hg,hy⟩ := hy
  obtain ⟨k,hkj,hk,hz⟩ := hz
  apply Subtype.ext
  rw [hy,hz,hx.2.2 g hgj hg,hx.2.2 k hkj hk]

theorem step_edge (P : RawFacePairing T) {ν : Vertex P}
    {x y : Point P ν} {f : Fin 4} (hx : EdgePoint P x f)
    (hy : Step P x y) : EdgePoint P y (P.facePair (x.val.1.1,f)).2 := by
  obtain ⟨g,hgj,hg,hy⟩ := hy
  have hgf := hx.2.2 g hgj hg
  subst g
  refine ⟨?_,?_,?_⟩
  · rw [hy]
    change (P.facePair (x.val.1.1,f)).2 ≠ sigma P (x.val.1.1,f) x.val.1.2
    rw [← sigma_face P (x.val.1.1,f)]
    exact (sigma P _).injective.ne hx.1
  · rw [hy]
    change x.val.2 ((sigma P (x.val.1.1,f)).symm (P.facePair (x.val.1.1,f)).2) = 0
    rw [← sigma_face P (x.val.1.1,f),Equiv.symm_apply_apply]
    exact hx.2.1
  · intro g hgj hg
    rw [hy] at hgj hg
    change g ≠ sigma P (x.val.1.1,f) x.val.1.2 at hgj
    change x.val.2 ((sigma P (x.val.1.1,f)).symm g) = 0 at hg
    have hj : (sigma P (x.val.1.1,f)).symm g ≠ x.val.1.2 := by
      intro hh
      apply hgj
      rw [← hh,Equiv.apply_symm_apply]
    have hh := hx.2.2 _ hj hg
    calc
      g = sigma P (x.val.1.1,f) ((sigma P (x.val.1.1,f)).symm g) :=
        (Equiv.apply_symm_apply _ _).symm
      _ = sigma P (x.val.1.1,f) f := congrArg (sigma P _) hh
      _ = (P.facePair (x.val.1.1,f)).2 := sigma_face P _

theorem edge_chain_normal_form (P : RawFacePairing T) {ν : Vertex P}
    (x y : Point P ν) (f : Fin 4) (hx : EdgePoint P x f) :
    Related P x y ↔ y = x ∨ Step P x y := by
  have forward {a b : Point P ν} (hab : Step P a b)
      (ha : a = x ∨ Step P x a) : b = x ∨ Step P x b := by
    rcases ha with rfl | ha
    · exact Or.inr hab
    · exact Or.inl (step_unique P (step_edge P hx ha) hab (step_symmetric P ha))
  have invariant : ∀ {a b : Point P ν}, Related P a b →
      ((a = x ∨ Step P x a) ↔ (b = x ∨ Step P x b)) := by
    intro a b hh
    induction hh with
    | rel a b hab => exact ⟨forward hab,forward (step_symmetric P hab)⟩
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  constructor
  · intro h
    exact (invariant h).mp (Or.inl rfl)
  · rintro (rfl | h)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h

theorem interior_normal_form (P : RawFacePairing T) {ν : Vertex P}
    (x y : Point P ν) (hx : Interior P x) : Related P x y ↔ y = x := by
  have forward {a b : Point P ν} (hab : Step P a b) (ha : a = x) : b = x := by
    subst a
    obtain ⟨f,hfj,hf,_⟩ := hab
    exact False.elim (hx f hfj hf)
  have inv : ∀ {a b : Point P ν}, Related P a b → (a = x ↔ b = x) := by
    intro a b hh
    induction hh with
    | rel a b hab => exact ⟨forward hab,forward (step_symmetric P hab)⟩
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  constructor
  · intro h; exact (inv h).mp rfl
  · intro h; subst y; exact Relation.EqvGen.refl _


theorem paired_edge_distinct (P : RawFacePairing T) {ν : Vertex P}
    (x : Point P ν) (f : Fin 4) (hx : EdgePoint P x f) :
    pairedPoint P x f hx.1 ≠ x := by
  intro he
  have hs : Step P x (pairedPoint P x f hx.1) := ⟨f,hx.1,hx.2.1,rfl⟩
  have hE := step_edge P hx hs
  rw [he] at hE
  have hg : (P.facePair (x.val.1.1,f)).2 = f := hx.2.2 _ hE.1 hE.2.1
  have ht := congrArg (fun z : Point P ν => z.val.1.1) he
  exact P.pairFixedFree (x.val.1.1,f) (Prod.ext ht hg)

theorem positive_side_normal_form (P : RawFacePairing T) {ν : Vertex P}
    (x y : Point P ν) (f : Fin 4) (hx : EdgePoint P x f) :
    pairedPoint P x f hx.1 ≠ x ∧
      (Related P x y ↔ y = x ∨ y = pairedPoint P x f hx.1) := by
  refine ⟨paired_edge_distinct P x f hx,?_⟩
  rw [edge_chain_normal_form P x y f hx]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (step_unique P hx h ⟨f,hx.1,hx.2.1,rfl⟩)
  · rintro (h | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨f,hx.1,hx.2.1,rfl⟩

end D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.move_inverse,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.step_symmetric,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.step_unique,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.step_edge,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.edge_chain_normal_form,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.interior_normal_form,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.paired_edge_distinct,
      ``D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate.positive_side_normal_form] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1436 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1436 disallowed {ax}"
    Lean.logInfo m!"CFMP1436 CHECKED {name} axioms={axioms}"
