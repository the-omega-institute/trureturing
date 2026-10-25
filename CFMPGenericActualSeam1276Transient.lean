import CFMPGenericNeighborhoodCoordinates1244Transient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing outgoingFace incomingFace)
open D5.S3.Geometry.Gluing.ActualLinkCornerChains (Dart)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceEndpointCandidate
open D5.S3.Geometry.Gluing.RawFaceOccurrenceCandidate
open D5.S3.Geometry.Gluing.RawFaceCycleCandidate (Orientation)
open D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate
  (sectorCount sectorCount_pos enumeration nextIndex enumeration_next port_guards
    next_actual_dartMove next_target_ports next_sigma_positions)
open D5.S3.Geometry.Gluing.RawFaceEndpointFanCandidate
  (Neighborhood strict_chain_reflection)
open D5.S3.Geometry.Gluing.RawFaceSectorCoordinatesCandidate
  (beta beta_actual_values beta_actual_simplex)
open D5.S3.Geometry.Gluing.ActualLinkAffineFan (Sector swap seam)
open private port_exhaust from CFMPOrderedEndpointCycle1210Transient
open private move_inverse from CFMPGenericEndpointFan1191Transient
variable {T : Type*} [Fintype T]

-- Temporary exact-check candidate; no compilation or canonical admission is claimed.
instance sectorCount_neZero (P : RawFacePairing T) (d0 : OrderedEnd T) :
    NeZero (sectorCount P d0) := ⟨Nat.ne_of_gt (sectorCount_pos P d0)⟩

private theorem swap_swap (p : Sector) : swap (swap p) = p :=
  Subtype.ext (Prod.ext rfl rfl)

theorem nextIndex_eq_add_one (P : RawFacePairing T) (d0 : OrderedEnd T)
    (i : Fin (sectorCount P d0)) : nextIndex P d0 i = i+1 := by
  apply Fin.ext
  change (i.val+1) % sectorCount P d0 = (i+1).val
  simp only [Fin.val_add,Fin.val_one',Nat.add_mod_mod]

theorem enumeration_next_add (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (i : Fin (sectorCount P d0)) :
    D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR
        (enumeration P s d0 hNR i) = enumeration P s d0 hNR (i+1) :=
  (enumeration_next P s d0 hNR i).trans
    (congrArg (enumeration P s d0 hNR) (nextIndex_eq_add_one P d0 i))

def componentRaw (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (d : Component P d0) (p : Sector) : Raw T :=
  D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate.rawPhi
    P s.reversed d0 (d,p)

/-- This is an equality of original arrays; a legal Step also needs a zero guard. -/
theorem component_affine_forward (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (d : Component P d0) (p : Sector) :
    move P (outgoingFace s.reversed (occ d.val.val)) (componentRaw P s d0 d p) =
      componentRaw P s d0
        (D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR d)
        (swap p) := by
  let e := D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR d
  let q := sigma P (d.val.val.1.1,outgoingFace s.reversed (occ d.val.val))
  have hm := next_actual_dartMove P s d0 hNR d
  have hpos := next_sigma_positions P s d0 hNR d
  change q d.val.val.1.2 = e.val.val.1.2 ∧ q d.val.val.2 = e.val.val.2 ∧
    q (outgoingFace s.reversed (occ d.val.val)) =
      incomingFace s.reversed (occ e.val.val) ∧
    q (incomingFace s.reversed (occ d.val.val)) =
      outgoingFace s.reversed (occ e.val.val) at hpos
  have hd := beta_actual_values s.reversed d.val p.val
  have he := beta_actual_values s.reversed e.val (swap p).val
  apply Prod.ext
  · exact (congrArg (fun a : Dart T => a.1) hm).symm
  · funext l
    obtain ⟨a,rfl⟩ := q.surjective l
    change beta s.reversed d.val p.val (q.symm (q a)) =
      beta s.reversed e.val (swap p).val (q a)
    rw [Equiv.symm_apply_apply]
    rcases port_exhaust s.reversed d.val a with rfl | rfl | rfl | rfl
    · rw [hpos.1,hd.1,he.1]
    · rw [hpos.2.1,hd.2.1,he.2.1]
      change 1-(p.val.1+p.val.2)/2 = 1-(p.val.2+p.val.1)/2
      ring
    · rw [hpos.2.2.2,hd.2.2.1,he.2.2.2] <;> rfl
    · rw [hpos.2.2.1,hd.2.2.2,he.2.2.1] <;> rfl

/-- The inverse uses the same original paired target face, not an abstract inverse. -/
theorem component_affine_backward (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (d : Component P d0) (p : Sector) :
    move P (incomingFace s.reversed (occ d.val.val)) (componentRaw P s d0 d p) =
      componentRaw P s d0
        ((D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR).symm d)
        (swap p) := by
  let e := (D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR).symm d
  have hed : D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR e = d :=
    (D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR).apply_symm_apply d
  have hf0 := component_affine_forward P s d0 hNR e (swap p)
  have hf : move P (outgoingFace s.reversed (occ e.val.val))
      (componentRaw P s d0 e (swap p)) = componentRaw P s d0 d p := by
    simpa only [hed,swap_swap] using hf0
  have ht := congrArg Prod.snd (next_target_ports P s d0 hNR e).1
  change (P.facePair (e.val.val.1.1,outgoingFace s.reversed (occ e.val.val))).2 =
    incomingFace s.reversed (occ
      (D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR e).val.val) at ht
  have ht' : (P.facePair (e.val.val.1.1,outgoingFace s.reversed (occ e.val.val))).2 =
      incomingFace s.reversed (occ d.val.val) := by
    simpa only [hed] using ht
  calc
    move P (incomingFace s.reversed (occ d.val.val)) (componentRaw P s d0 d p) =
      move P (P.facePair (e.val.val.1.1,outgoingFace s.reversed (occ e.val.val))).2
        (componentRaw P s d0 d p) :=
      congrArg (fun f : Fin 4 => move P f (componentRaw P s d0 d p)) ht'.symm
    _ = move P (P.facePair (e.val.val.1.1,outgoingFace s.reversed (occ e.val.val))).2
        (move P (outgoingFace s.reversed (occ e.val.val))
          (componentRaw P s d0 e (swap p))) :=
      congrArg (move P (P.facePair
        (e.val.val.1.1,outgoingFace s.reversed (occ e.val.val))).2) hf.symm
    _ = componentRaw P s d0 e (swap p) := move_inverse P _ _

def rawPhi (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) (z : Fin (sectorCount P d0) × Sector) : Raw T :=
  componentRaw P s d0 (enumeration P s d0 hNR z.1) z.2

def Phi (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) (z : Fin (sectorCount P d0) × Sector) :
    ↥(Neighborhood P (ν := label P d0.val.1) d0.val) :=
  D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate.Phi
    P s.reversed d0 (enumeration P s d0 hNR z.1,z.2)

def indexedEquiv (P : RawFacePairing T) (s : Orientation P) (d0 : OrderedEnd T)
    (hNR : LocalNoEdgeReversal P d0) :
    (Fin (sectorCount P d0) × Sector) ≃
      ↥(Neighborhood P (ν := label P d0.val.1) d0.val) :=
  (Equiv.prodCongr (enumeration P s d0 hNR) (Equiv.refl Sector)).trans
    (D5.S3.Geometry.Gluing.RawFaceNeighborhoodCoordinatesCandidate.coordinateEquiv
      P s.reversed d0)

theorem actual_indexed_coordinates (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0) :
    Function.Bijective (Phi P s d0 hNR) := (indexedEquiv P s d0 hNR).bijective

theorem indexed_affine_forward (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (i : Fin (sectorCount P d0)) (p : Sector) :
    move P (outgoingFace s.reversed (occ (enumeration P s d0 hNR i).val.val))
      (rawPhi P s d0 hNR (i,p)) = rawPhi P s d0 hNR (i+1,swap p) :=
  (component_affine_forward P s d0 hNR _ p).trans
    (congrArg (fun d : Component P d0 => componentRaw P s d0 d (swap p))
      (enumeration_next_add P s d0 hNR i))

theorem indexed_affine_backward (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (i : Fin (sectorCount P d0)) (p : Sector) :
    move P (incomingFace s.reversed (occ (enumeration P s d0 hNR i).val.val))
      (rawPhi P s d0 hNR (i,p)) = rawPhi P s d0 hNR (i-1,swap p) := by
  have hnext : D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR
      (enumeration P s d0 hNR (i-1)) = enumeration P s d0 hNR i := by
    simpa only [sub_add_cancel] using enumeration_next_add P s d0 hNR (i-1)
  have hprev :
      (D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR).symm
        (enumeration P s d0 hNR i) = enumeration P s d0 hNR (i-1) := by
    apply (D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR).injective
    have hcancel :=
      (D5.S3.Geometry.Gluing.RawFaceOrderedCycleCandidate.next P s d0 hNR).apply_symm_apply
        (enumeration P s d0 hNR i)
    exact hcancel.trans hnext.symm
  exact (component_affine_backward P s d0 hNR _ p).trans
    (congrArg (fun d : Component P d0 => componentRaw P s d0 d (swap p)) hprev)

private theorem backward_seam {n : ℕ} [NeZero n] (i : Fin n) (p : Sector)
    (w : Fin n × Sector) : seam w (i,p) ↔ p.val.1 = 0 ∧ w = (i-1,swap p) := by
  constructor
  · rintro ⟨hz,he⟩
    have hi := congrArg Prod.fst he
    have hq := congrArg (fun a => a.2.val) he
    refine ⟨?_,Prod.ext ?_ (Subtype.ext ?_)⟩
    · exact (congrArg Prod.fst hq).trans hz
    · dsimp at hi ⊢
      rw [hi,add_sub_cancel_right]
    · exact Prod.ext (congrArg Prod.snd hq).symm (congrArg Prod.fst hq).symm
  · rintro ⟨ha,rfl⟩
    exact ⟨ha,Prod.ext (by simp) (Subtype.ext (Prod.ext rfl rfl))⟩

/-- Original guarded Step, with its literal face and zero guard, is exactly a seam. -/
theorem actual_step_iff (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (z w : Fin (sectorCount P d0) × Sector) :
    Step P (Phi P s d0 hNR z).val (Phi P s d0 hNR w).val ↔
      seam z w ∨ seam w z := by
  rcases z with ⟨i,p⟩
  let d := enumeration P s d0 hNR i
  have hn := indexed_affine_forward P s d0 hNR i p
  have hp := indexed_affine_backward P s d0 hNR i p
  have inj := (actual_indexed_coordinates P s d0 hNR).1
  rw [backward_seam i p w]
  constructor
  · rintro ⟨f,hfj,hzero,he⟩
    change f ≠ d.val.val.1.2 at hfj
    change beta s.reversed d.val p.val f = 0 at hzero
    change rawPhi P s d0 hNR w = move P f (rawPhi P s d0 hNR (i,p)) at he
    have hfk : f ≠ d.val.val.2 := by
      intro hfk
      have hd := (beta_actual_simplex s.reversed d.val p).2.2
      rw [← hfk,hzero] at hd
      norm_num at hd
    have hf : f = outgoingFace s.reversed (occ d.val.val) ∨
        f = incomingFace s.reversed (occ d.val.val) := by
      rcases port_exhaust s.reversed d.val f with h | h | h | h
      · exact False.elim (hfj h)
      · exact False.elim (hfk h)
      · exact Or.inr h
      · exact Or.inl h
    rcases hf with rfl | rfl
    · have hb : p.val.2 = 0 := by
        rw [(beta_actual_values s.reversed d.val p.val).2.2.2] at hzero
        linarith
      refine Or.inl ⟨hb,inj ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact he.trans hn
    · have ha : p.val.1 = 0 := by
        rw [(beta_actual_values s.reversed d.val p.val).2.2.1] at hzero
        linarith
      refine Or.inr ⟨ha,inj ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact he.trans hp
  · rintro (⟨hb,rfl⟩ | ⟨ha,rfl⟩)
    · refine ⟨outgoingFace s.reversed (occ d.val.val),
        (port_guards s.reversed d.val).1.1,?_,hn.symm⟩
      change beta s.reversed d.val p.val (outgoingFace s.reversed (occ d.val.val)) = 0
      rw [(beta_actual_values s.reversed d.val p.val).2.2.2,hb]
      norm_num
    · refine ⟨incomingFace s.reversed (occ d.val.val),
        (port_guards s.reversed d.val).2.1.1,?_,hp.symm⟩
      change beta s.reversed d.val p.val (incomingFace s.reversed (occ d.val.val)) = 0
      rw [(beta_actual_values s.reversed d.val p.val).2.2.1,ha]
      norm_num

/-- Saturation/reflection retains every full original Point intermediate. -/
theorem actual_eqvgen_iff (P : RawFacePairing T) (s : Orientation P)
    (d0 : OrderedEnd T) (hNR : LocalNoEdgeReversal P d0)
    (z w : Fin (sectorCount P d0) × Sector) :
    Related P (Phi P s d0 hNR z).val (Phi P s d0 hNR w).val ↔
      Relation.EqvGen seam z w := by
  let e : (Fin (sectorCount P d0) × Sector) ≃
      ↥(Neighborhood P (ν := label P d0.val.1) d0.val) := indexedEquiv P s d0 hNR
  constructor
  · intro h
    have hr := (strict_chain_reflection P d0.val (Phi P s d0 hNR z)
      (Phi P s d0 hNR w)).mp h
    have lift : ∀ (a b : ↥(Neighborhood P (ν := label P d0.val.1) d0.val)),
        Relation.EqvGen (fun a b => Step P a.val b.val) a b →
          Relation.EqvGen seam (e.symm a) (e.symm b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
        have hs := actual_step_iff P s d0 hNR (e.symm a) (e.symm b)
        have ha : Phi P s d0 hNR (e.symm a) = a := e.apply_symm_apply a
        have hb : Phi P s d0 hNR (e.symm b) = b := e.apply_symm_apply b
        rw [ha,hb] at hs
        rcases hs.mp hab with hh | hh
        · exact Relation.EqvGen.rel _ _ hh
        · exact (Relation.EqvGen.rel _ _ hh).symm
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
    have hz : e.symm (Phi P s d0 hNR z) = z := e.symm_apply_apply z
    have hw : e.symm (Phi P s d0 hNR w) = w := e.symm_apply_apply w
    exact hz ▸ hw ▸ lift _ _ hr
  · intro h
    induction h with
    | rel a b hab =>
      exact Relation.EqvGen.rel _ _ ((actual_step_iff P s d0 hNR a b).mpr (Or.inl hab))
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
end D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.nextIndex_eq_add_one,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.enumeration_next_add,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.component_affine_forward,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.component_affine_backward,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.actual_indexed_coordinates,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.indexed_affine_forward,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.indexed_affine_backward,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.actual_step_iff,
      ``D5.S3.Geometry.Gluing.RawFaceActualSeamCandidate.actual_eqvgen_iff] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1276 actual seam target absent: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1276 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP1276 CHECKED {name} axioms={axioms}"
