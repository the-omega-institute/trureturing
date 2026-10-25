import CFMPSection71Exact620Transient
import D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
open scoped Matrix Classical BigOperators

namespace Section71GlobalCheck629

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open Section71ExactCheck620

open private localFlagEquiv from
  D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open private angle_pi from
  D5.S3.Geometry.Hyperideal.PositiveFlatClassification

def lengths {T : Type*} (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (t : T) (j : Fin 6) : ℝ := Real.cosh (ell (p.edgeLabel t j))

def localLow (v : Fin 6 → ℝ) (h : ℝ) (f : Fin 4) : Prop :=
  ∃ m : Fin 3, v (faceEdge f m) < h

/-- Fixed original axes0,3; every local value is read from the same quotient field.
The flat axis angle is the actual six-length formula, not an independent angle vector. -/
def FixedAxisData {T : Type*} (p : RawFacePairing T)
    (ell : p.GlobalEdge → ℝ) (h : ℝ) : Prop :=
  ∀ t : T, ∃ r s : ℝ, lengths p ell t = six r h s ∧
    ((h < r ∧ h < s ∧ extendedAngle (six r h s) 0 = Real.pi) ∨
      (1 + 2 * h ≤ r ∧ Genuine (six r h s) ∧
        Real.tan (Real.arccos (cosine r h h s h h) / 2) ≤ (1 : ℝ) / 2))

def EdgeFiber {T : Type*} (p : RawFacePairing T) (e : p.GlobalEdge) :=
  {o : Occurrence T // p.edgeLabel o.1 o.2 = e}

noncomputable instance edgeFiberFintype {T : Type*} [Fintype T]
    (p : RawFacePairing T) (e : p.GlobalEdge) : Fintype (EdgeFiber p e) := by
  classical
  unfold EdgeFiber
  infer_instance

def GenuineFiber {T : Type*} (p : RawFacePairing T)
    (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) :=
  {o : EdgeFiber p e // Genuine (lengths p ell o.val.1)}

noncomputable instance genuineFiberFintype {T : Type*} [Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) :
    Fintype (GenuineFiber p ell e) := by
  classical
  unfold GenuineFiber
  infer_instance

def actualAngle {T : Type*} (p : RawFacePairing T)
    (ell : p.GlobalEdge → ℝ) (o : Occurrence T) : ℝ :=
  extendedAngle (lengths p ell o.1) o.2

private theorem flat_no_low (r h s : ℝ) (hr : h < r) (hs : h < s)
    (f : Fin 4) : ¬ localLow (six r h s) h f := by
  rintro ⟨m,hm⟩
  fin_cases f <;> fin_cases m <;>
    norm_num [six, faceEdge] at hm <;> linarith

private theorem genuine_low_faces (r h s : ℝ) (hr : h < r) (hs : s < h)
    (f : Fin 4) : localLow (six r h s) h f ↔ f = 0 ∨ f = 1 := by
  constructor
  · rintro ⟨m,hm⟩
    fin_cases f <;> fin_cases m
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | (norm_num [six, faceEdge] at hm <;> linarith)
  · rintro (rfl | rfl)
    · exact ⟨0, by simpa [six, faceEdge] using hs⟩
    · exact ⟨2, by simpa [six, faceEdge] using hs⟩

/-- The original private incidence equivalence supplies the actual chosen flag.
The unique low side is a finite specialization of that same incidence table. -/
private theorem unique_low_slot (j : Fin 6) (hj0 : j ≠ 0) (hj3 : j ≠ 3) :
    ∃! z : Fin 4 × Fin 3, faceEdge z.1 z.2 = j ∧ (z.1 = 0 ∨ z.1 = 1) := by
  refine ⟨localFlagEquiv.symm (j,false), ?_, ?_⟩
  · fin_cases j <;> first | contradiction | decide
  · have htable : ∀ (k : Fin 6) (z : Fin 4 × Fin 3),
        k ≠ 0 → k ≠ 3 →
        (faceEdge z.1 z.2 = k ∧ (z.1 = 0 ∨ z.1 = 1)) →
          z = localFlagEquiv.symm (k,false) := by decide
    intro z hz
    exact htable j z hj0 hj3 hz

/-- All role and angle facts here are derived from the full raw six-length data. -/
private theorem local_dichotomy {T : Type*}
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (h : ℝ)
    (hpos : ∀ e, 0 < ell e) (hh : 1 < h) (data : FixedAxisData p ell h)
    (t : T) :
    (¬ Genuine (lengths p ell t) ∧
      (∀ f, ¬ localLow (lengths p ell t) h f) ∧
      (∀ j, lengths p ell t j = h → actualAngle p ell (t,j) = 0)) ∨
    (Genuine (lengths p ell t) ∧
      (∀ f, localLow (lengths p ell t) h f ↔ f = 0 ∨ f = 1) ∧
      (∀ j, lengths p ell t j = h → j ≠ 0 ∧ j ≠ 3 ∧
        Real.pi / 3 < actualAngle p ell (t,j) ∧
        actualAngle p ell (t,j) < Real.pi / 2)) := by
  obtain ⟨r,s,hshape,hkind⟩ := data t
  have hpositive : ∀ j, 1 < (six r h s) j := by
    intro j
    rw [← hshape]
    exact Real.one_lt_cosh.mpr (ne_of_gt (hpos _))
  rcases hkind with hflat | hgen
  · rcases hflat with ⟨hr,hs,hpi⟩
    have hsector : Sector (six r h s) 0 :=
      (angle_pi (six r h s) 0).mp hpi
    have hnG : ¬ Genuine (six r h s) := by
      intro hg
      have hc := (hg 0).1
      have hf : rawCos (six r h s) 0 ≤ -1 := hsector
      linarith
    left
    refine ⟨?_, ?_, ?_⟩
    · intro hg
      apply hnG
      simpa only [hshape] using hg
    · intro f
      rw [hshape]
      exact flat_no_low r h s hr hs f
    · intro j hj
      have hv : (six r h s) j = h := by simpa only [hshape] using hj
      have hj0 : j ≠ 0 := by
        intro heq
        subst j
        have heq' : r = h := by simpa [six] using hv
        linarith
      have hj3 : j ≠ 3 := by
        intro heq
        subst j
        have heq' : s = h := by simpa [six] using hv
        linarith
      have hpattern :=
        (((positive_classification (six r h s) hpositive).2.2 (0 : Fin 3)).2).mp
          hsector j
      change extendedAngle (six r h s) j =
        (if j = 0 ∨ j = 3 then Real.pi else 0) at hpattern
      change extendedAngle (lengths p ell t) j = 0
      rw [hshape]
      simpa only [if_neg (not_or.mpr ⟨hj0,hj3⟩)] using hpattern
  · rcases hgen with ⟨hrh,hg,htan⟩
    have hs : 1 < s := by simpa [six] using hpositive 3
    have hlocal := literal_local_bridge r h s hh hs hrh hg htan
    dsimp only at hlocal
    have hshort : s < h := hlocal.2.1
    have hlong : h < r := by linarith
    right
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hshape] using hg
    · intro f
      rw [hshape]
      exact genuine_low_faces r h s hlong hshort f
    · intro j hj
      have hv : (six r h s) j = h := by simpa only [hshape] using hj
      have hj0 : j ≠ 0 := by
        intro heq
        subst j
        have heq' : r = h := by simpa [six] using hv
        linarith
      have hj3 : j ≠ 3 := by
        intro heq
        subst j
        have heq' : s = h := by simpa [six] using hv
        linarith
      refine ⟨hj0,hj3,?_⟩
      simpa only [actualAngle, hshape] using (hlocal.2.2.2 j hj0 hj3).2

/-- Forgetting the actual low face-slot gives the actual genuine occurrence.
No support bijection or independently supplied partner appears among the inputs. -/
def actual_low_slot_equiv {T : Type*} [Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (h : ℝ)
    (hpos : ∀ e, 0 < ell e) (hh : 1 < h) (data : FixedAxisData p ell h)
    (e : p.GlobalEdge) (he : Real.cosh (ell e) = h) :
    lowFiber p (fun e => Real.cosh (ell e)) h e ≃ GenuineFiber p ell e := by
  classical
  have hrole := local_dichotomy p ell h hpos hh data
  have hlow_genuine (d : lowFiber p (fun e => Real.cosh (ell e)) h e) :
      Genuine (lengths p ell d.val.1) := by
    rcases hrole d.val.1 with hflat | hgen
    · exact False.elim (hflat.2.1 d.val.2.1 d.property.1)
    · exact hgen.1
  let forget : lowFiber p (fun e => Real.cosh (ell e)) h e →
      GenuineFiber p ell e := fun d =>
    ⟨⟨(d.val.1,faceEdge d.val.2.1 d.val.2.2),d.property.2⟩,hlow_genuine d⟩
  have hinjective : Function.Injective forget := by
    rintro ⟨⟨ta,⟨fa,na⟩⟩,ha⟩ ⟨⟨tb,⟨fb,nb⟩⟩,hb⟩ hab
    have hocc := congrArg (fun z : GenuineFiber p ell e => z.val.val) hab
    change (ta,faceEdge fa na) = (tb,faceEdge fb nb) at hocc
    have ht : ta = tb := congrArg Prod.fst hocc
    subst tb
    have hj : faceEdge fa na = faceEdge fb nb := congrArg Prod.snd hocc
    have hvalue : lengths p ell ta (faceEdge fa na) = h := by
      change Real.cosh (ell (p.edgeLabel ta (faceEdge fa na))) = h
      rw [ha.2]
      exact he
    rcases hrole ta with hflat | hgen
    · exact False.elim (hflat.2.1 fa ha.1)
    · have hmid := hgen.2.2 (faceEdge fa na) hvalue
      obtain ⟨z,hz,hunique⟩ := unique_low_slot (faceEdge fa na) hmid.1 hmid.2.1
      have haLow : fa = 0 ∨ fa = 1 := (hgen.2.1 fa).mp ha.1
      have hbLow : fb = 0 ∨ fb = 1 := (hgen.2.1 fb).mp hb.1
      have haz : (fa,na) = z := hunique (fa,na) ⟨rfl,haLow⟩
      have hbz : (fb,nb) = z := hunique (fb,nb) ⟨hj.symm,hbLow⟩
      apply Subtype.ext
      exact Prod.ext rfl (haz.trans hbz.symm)
  have hsurjective : Function.Surjective forget := by
    rintro ⟨⟨⟨t,j⟩,hjLabel⟩,hg⟩
    have hvalue : lengths p ell t j = h := by
      change Real.cosh (ell (p.edgeLabel t j)) = h
      rw [hjLabel]
      exact he
    rcases hrole t with hflat | hgen
    · exact False.elim (hflat.1 hg)
    · have hmid := hgen.2.2 j hvalue
      obtain ⟨⟨f,n⟩,hslot,hunique⟩ := unique_low_slot j hmid.1 hmid.2.1
      have hlow : localLow (lengths p ell t) h f := (hgen.2.1 f).mpr hslot.2
      have hlabel : p.edgeLabel t (faceEdge f n) = e := by
        rw [hslot.1]
        exact hjLabel
      refine ⟨⟨(t,(f,n)),hlow,hlabel⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change (t,faceEdge f n) = (t,j)
      exact Prod.ext rfl hslot.1
  exact Equiv.ofBijective forget ⟨hinjective,hsurjective⟩

/-- Exact support parity and actual full angle-sum obstruction for one original edge. -/
theorem fixed_axes_edge_obstruction {T : Type*} [Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (h : ℝ)
    (hpos : ∀ e, 0 < ell e) (hh : 1 < h) (data : FixedAxisData p ell h)
    (e : p.GlobalEdge) (he : Real.cosh (ell e) = h) :
    Even (Fintype.card (GenuineFiber p ell e)) ∧
      (∑ o : EdgeFiber p e, actualAngle p ell o.val) ≠ 2 * Real.pi := by
  classical
  let E := actual_low_slot_equiv p ell h hpos hh data e he
  have hcard := Fintype.card_congr E
  have hlow := actual_low_flag_count_even p (fun e => Real.cosh (ell e)) h e
  have heven : Even (Fintype.card (GenuineFiber p ell e)) := by
    rw [← hcard]
    exact hlow
  have hrole := local_dichotomy p ell h hpos hh data
  have hrange (o : GenuineFiber p ell e) :
      Real.pi / 3 < actualAngle p ell o.val.val ∧
        actualAngle p ell o.val.val < Real.pi / 2 := by
    have hvalue : lengths p ell o.val.val.1 o.val.val.2 = h := by
      change Real.cosh (ell (p.edgeLabel o.val.val.1 o.val.val.2)) = h
      rw [o.val.property]
      exact he
    rcases hrole o.val.val.1 with hflat | hgen
    · exact False.elim (hflat.1 o.property)
    · exact (hgen.2.2 o.val.val.2 hvalue).2.2
  have hmiddle_ne : (∑ o : GenuineFiber p ell e, actualAngle p ell o.val.val) ≠
      2 * Real.pi :=
    D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction.even_middle_angle_sum_ne_two_pi
      (fun o : GenuineFiber p ell e => actualAngle p ell o.val.val) heven hrange
  have hzero (o : {o : EdgeFiber p e // ¬ Genuine (lengths p ell o.val.1)}) :
      actualAngle p ell o.val.val = 0 := by
    have hvalue : lengths p ell o.val.val.1 o.val.val.2 = h := by
      change Real.cosh (ell (p.edgeLabel o.val.val.1 o.val.val.2)) = h
      rw [o.val.property]
      exact he
    rcases hrole o.val.val.1 with hflat | hgen
    · exact hflat.2.2 o.val.val.2 hvalue
    · exact False.elim (o.property hgen.1)
  have hzero_sum :
      (∑ o : {o : EdgeFiber p e // ¬ Genuine (lengths p ell o.val.1)},
        actualAngle p ell o.val.val) = 0 := by
    apply Finset.sum_eq_zero
    intro o ho
    exact hzero o
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (p := fun o : EdgeFiber p e => Genuine (lengths p ell o.val.1))
    (f := fun o : EdgeFiber p e => actualAngle p ell o.val)
  have hsum : (∑ o : GenuineFiber p ell e, actualAngle p ell o.val.val) =
      ∑ o : EdgeFiber p e, actualAngle p ell o.val := by
    simpa only [GenuineFiber, hzero_sum, add_zero] using hsplit
  refine ⟨heven,?_⟩
  intro hclosed
  apply hmiddle_ne
  rw [hsum]
  exact hclosed

/-- Nonemptiness supplies a middle occurrence without requiring distinct edge labels. -/
theorem fixed_axes_no_closed_angle_sum {T : Type*} [Fintype T] [Nonempty T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (h : ℝ)
    (hpos : ∀ e, 0 < ell e) (hh : 1 < h) (data : FixedAxisData p ell h) :
    ¬ (∀ e : p.GlobalEdge,
      (∑ o : EdgeFiber p e, actualAngle p ell o.val) = 2 * Real.pi) := by
  intro hclosed
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  obtain ⟨r,s,hshape,hkind⟩ := data t
  let e : p.GlobalEdge := p.edgeLabel t 1
  have he : Real.cosh (ell e) = h := by
    change lengths p ell t 1 = h
    rw [hshape]
    rfl
  exact (fixed_axes_edge_obstruction p ell h hpos hh data e he).2 (hclosed e)

end Section71GlobalCheck629

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``Section71GlobalCheck629.actual_low_slot_equiv,
      ``Section71GlobalCheck629.fixed_axes_edge_obstruction,
      ``Section71GlobalCheck629.fixed_axes_no_closed_angle_sum] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"Section71-629 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"Section71-629 disallowed axiom {ax} for {name}"
    Lean.logInfo m!"Section71-629 CHECKED {name} axioms={axioms}"
