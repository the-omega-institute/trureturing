/-
TEMPORARY EXACT-CHECK CANDIDATE -- UNCOMPILED.

Global consumption of the full-six-coordinate local neighborhood from685.
The new low-slot/occurrence correspondence uses interval membership, never
equality of four middle lengths. All labels belong to the same original
RawFacePairing quotient; numerical equality creates no new identification.

Required transient staging modules are listed in the imports. Existing
private unique_low_slot is called directly, not copied or reproved. A
canonical consumer must use the original visibility/publicization workflow.
No kernel acceptance, completed axiom audit or new-content admission is
asserted for this temporary source.
-/

import CFMPSection71OpenNeighborhood685Transient
import CFMPSection71Relabel648Transient
import CFMPSection71Exact620Transient
import CFMPSection71Global629Transient
import D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction
import Batteries.Tactic.OpenPrivate
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Classical

namespace Section71GlobalNeighborhood694Temporary

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification (Genuine)
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (extendedAngle rawCos)
open D5.S3.Geometry.Hyperideal.EvenAngleSumObstruction
open Section71OpenNeighborhood685Temporary
open Section71Relabel648 (P4 edgePerm relabel field globalEdges values values_transport
  Fiber GenuineFiber angle angle_sum_transport genuineFiberEquiv)
open Section71ExactCheck620 (lowFiber lowFlag actual_low_flag_count_even)

open private unique_low_slot from CFMPSection71Global629Transient

def Medium (z : ℝ) : Prop := 9 < z ∧ z < 11
def Short (z : ℝ) : Prop := 1 < z ∧ z < 2

def StableBlocks {T : Type*} (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) : Prop :=
  ∀ t, FlatStable (values p ell t) ∨ GenuineStable (values p ell t)

def localLow (v : Coordinates) (f : Fin 4) : Prop :=
  Section71Relabel648.localLow v 9 f

theorem flat_above_nine (v : Coordinates) (hv : FlatProfile v) (j : Fin 6) :
    9 < v j := by
  have hlo : (9 : ℝ) ≤ flatLower j := by
    unfold flatLower
    split_ifs <;> norm_num
  exact lt_of_le_of_lt hlo (hv j).1

theorem flat_medium_is_middle (v : Coordinates) (hv : FlatProfile v)
    (j : Fin 6) (hj : Medium (v j)) : Middle j := by
  constructor
  · intro h0
    subst j
    have h := (hv 0).1
    norm_num [flatLower] at h
    exact (by unfold Medium at hj; linarith)
  · intro h3
    subst j
    have h := (hv 3).1
    norm_num [flatLower] at h
    exact (by unfold Medium at hj; linarith)

theorem genuine_below_nine_iff (v : Coordinates) (hv : GenuineProfile v)
    (j : Fin 6) : v j < 9 ↔ j = 3 := by
  constructor
  · intro hj
    by_contra h3
    by_cases h0 : j = 0
    · subst j
      have h := (hv 0).1
      norm_num [genuineLower] at h
      linarith
    · have h := (hv j).1
      simp only [genuineLower, if_neg h0, if_neg h3] at h
      linarith
  · rintro rfl
    have h := (hv 3).2
    norm_num [genuineUpper] at h
    linarith

theorem genuine_medium_is_middle (v : Coordinates) (hv : GenuineProfile v)
    (j : Fin 6) (hj : Medium (v j)) : Middle j := by
  constructor
  · intro h0
    subst j
    have h := (hv 0).1
    norm_num [genuineLower] at h
    exact (by unfold Medium at hj; linarith)
  · intro h3
    subst j
    have h := (hv 3).2
    norm_num [genuineUpper] at h
    exact (by unfold Medium at hj; linarith)

theorem flat_no_low (v : Coordinates) (hv : FlatProfile v) (f : Fin 4) :
    ¬ localLow v f := by
  rintro ⟨m, hm⟩
  have h := flat_above_nine v hv (faceEdge f m)
  linarith

theorem genuine_low_faces (v : Coordinates) (hv : GenuineProfile v) (f : Fin 4) :
    localLow v f ↔ f = 0 ∨ f = 1 := by
  constructor
  · rintro ⟨m, hm⟩
    have hedge : faceEdge f m = 3 :=
      (genuine_below_nine_iff v hv (faceEdge f m)).mp hm
    fin_cases f <;> fin_cases m <;> simp_all [faceEdge]
  · rintro (rfl | rfl)
    · refine ⟨0, ?_⟩
      have h := (genuine_below_nine_iff v hv 3).mpr rfl
      simpa [faceEdge] using h
    · refine ⟨2, ?_⟩
      have h := (genuine_below_nine_iff v hv 3).mpr rfl
      simpa [faceEdge] using h

/- Below9 is not a replacement geometric assumption: on these profiles it
   is exactly the actual short interval I_S=(1,2). -/
theorem stable_below_nine_iff_short {T : Type*}
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (data : StableBlocks p ell) (t : T) (j : Fin 6) :
    values p ell t j < 9 ↔ Short (values p ell t j) := by
  rcases data t with hf | hg
  · have h := flat_above_nine _ hf.1 j
    constructor
    · intro hbad
      linarith
    · intro hbad
      unfold Short at hbad
      linarith
  · constructor
    · intro hlow
      have hj : j = 3 := (genuine_below_nine_iff _ hg.1 j).mp hlow
      subst j
      have h := hg.1 3
      simpa [Short, genuineLower, genuineUpper] using h
    · intro hs
      unfold Short at hs
      linarith

theorem actual_low_flag_iff_short {T : Type*}
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (data : StableBlocks p ell) (d : T × (Fin 4 × Fin 3)) :
    lowFlag p (fun e => Real.cosh (ell e)) 9 d ↔
      ∃ m : Fin 3, Short (values p ell d.1 (faceEdge d.2.1 m)) := by
  change (∃ m : Fin 3, values p ell d.1 (faceEdge d.2.1 m) < 9) ↔ _
  exact exists_congr (fun m => stable_below_nine_iff_short p ell data d.1 _)

/- All role, low-face and angle statements are consequences of685 profiles
   and actual readouts. They are not added to the perturbation hypotheses. -/
theorem local_dichotomy {T : Type*}
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (data : StableBlocks p ell) (t : T) :
    (¬ Genuine (values p ell t) ∧
      (∀ f, ¬ localLow (values p ell t) f) ∧
      (∀ j, Medium (values p ell t j) → angle p ell (t, j) = 0)) ∨
    (Genuine (values p ell t) ∧
      (∀ f, localLow (values p ell t) f ↔ f = 0 ∨ f = 1) ∧
      (∀ j, Medium (values p ell t j) → j ≠ 0 ∧ j ≠ 3 ∧
        Real.pi / 3 < angle p ell (t, j) ∧ angle p ell (t, j) < Real.pi / 2)) := by
  rcases data t with hf | hg
  · left
    refine ⟨?_, fun f => flat_no_low _ hf.1 f, ?_⟩
    · intro hgen
      have hinside := (hgen 0).1
      have houtside := hf.2.2.1
      linarith
    · intro j hj
      have hm := flat_medium_is_middle _ hf.1 j hj
      have hpattern := hf.2.2.2 j
      change extendedAngle (values p ell t) j = 0
      simpa only [if_neg (not_or.mpr hm)] using hpattern
  · right
    refine ⟨hg.2.2.1, fun f => genuine_low_faces _ hg.1 f, ?_⟩
    intro j hj
    have hm := genuine_medium_is_middle _ hg.1 j hj
    have hwindow := hg.2.2.2.2.2 j hm
    exact ⟨hm.1, hm.2, hwindow⟩

/- The only adapted correspondence: forget the ACTUAL low face-slot over
   one ACTUAL I_M quotient edge. Repeated labels remain separate occurrences.
   Its inverse uses the already existing unique-low-slot incidence table.
 -/
def actual_low_slot_equiv {T : Type*} [Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (data : StableBlocks p ell) (e : p.GlobalEdge)
    (he : Medium (Real.cosh (ell e))) :
    lowFiber p (fun e => Real.cosh (ell e)) 9 e ≃ GenuineFiber p ell e := by
  classical
  have hrole := local_dichotomy p ell data
  have hlow_genuine (d : lowFiber p (fun e => Real.cosh (ell e)) 9 e) :
      Genuine (values p ell d.val.1) := by
    rcases hrole d.val.1 with hflat | hgen
    · exact False.elim (hflat.2.1 d.val.2.1 d.property.1)
    · exact hgen.1
  let forget : lowFiber p (fun e => Real.cosh (ell e)) 9 e →
      GenuineFiber p ell e := fun d =>
    ⟨⟨(d.val.1, faceEdge d.val.2.1 d.val.2.2), d.property.2⟩, hlow_genuine d⟩
  have hinjective : Function.Injective forget := by
    rintro ⟨⟨ta, ⟨fa, na⟩⟩, ha⟩ ⟨⟨tb, ⟨fb, nb⟩⟩, hb⟩ hab
    have hocc := congrArg (fun z : GenuineFiber p ell e => z.val.val) hab
    change (ta, faceEdge fa na) = (tb, faceEdge fb nb) at hocc
    have ht : ta = tb := congrArg Prod.fst hocc
    subst tb
    have hj : faceEdge fa na = faceEdge fb nb := congrArg Prod.snd hocc
    have hvalue : Medium (values p ell ta (faceEdge fa na)) := by
      change Medium (Real.cosh (ell (p.edgeLabel ta (faceEdge fa na))))
      rw [ha.2]
      exact he
    rcases hrole ta with hflat | hgen
    · exact False.elim (hflat.2.1 fa ha.1)
    · have hmid := hgen.2.2 (faceEdge fa na) hvalue
      obtain ⟨z, hz, hunique⟩ := unique_low_slot (faceEdge fa na) hmid.1 hmid.2.1
      have haLow : fa = 0 ∨ fa = 1 := (hgen.2.1 fa).mp ha.1
      have hbLow : fb = 0 ∨ fb = 1 := (hgen.2.1 fb).mp hb.1
      have haz : (fa, na) = z := hunique (fa, na) ⟨rfl, haLow⟩
      have hbz : (fb, nb) = z := hunique (fb, nb) ⟨hj.symm, hbLow⟩
      apply Subtype.ext
      exact Prod.ext rfl (haz.trans hbz.symm)
  have hsurjective : Function.Surjective forget := by
    rintro ⟨⟨⟨t, j⟩, hjLabel⟩, hg⟩
    have hvalue : Medium (values p ell t j) := by
      change Medium (Real.cosh (ell (p.edgeLabel t j)))
      rw [hjLabel]
      exact he
    rcases hrole t with hflat | hgen
    · exact False.elim (hflat.1 hg)
    · have hmid := hgen.2.2 j hvalue
      obtain ⟨⟨f, n⟩, hslot, hunique⟩ := unique_low_slot j hmid.1 hmid.2.1
      have hlow : localLow (values p ell t) f := (hgen.2.1 f).mpr hslot.2
      have hlabel : p.edgeLabel t (faceEdge f n) = e := by
        rw [hslot.1]
        exact hjLabel
      refine ⟨⟨(t, (f, n)), hlow, hlabel⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change (t, faceEdge f n) = (t, j)
      exact Prod.ext rfl hslot.1
  exact Equiv.ofBijective forget ⟨hinjective, hsurjective⟩

/-620's parity theorem constructs and restricts the actual original crossing
   from p.facePair and p.faceMap. No new involution is supplied here. -/
theorem stable_middle_edge_obstruction {T : Type*} [Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (data : StableBlocks p ell) (e : p.GlobalEdge)
    (he : Medium (Real.cosh (ell e))) :
    Even (Fintype.card (GenuineFiber p ell e)) ∧
      (∑ o : Fiber p e, angle p ell o.val) ≠ 2 * Real.pi := by
  classical
  let E := actual_low_slot_equiv p ell data e he
  have hcard := Fintype.card_congr E
  have hlow := actual_low_flag_count_even p (fun e => Real.cosh (ell e)) 9 e
  have heven : Even (Fintype.card (GenuineFiber p ell e)) := by
    rw [← hcard]
    exact hlow
  have hrole := local_dichotomy p ell data
  have hrange (o : GenuineFiber p ell e) :
      Real.pi / 3 < angle p ell o.val.val ∧ angle p ell o.val.val < Real.pi / 2 := by
    have hvalue : Medium (values p ell o.val.val.1 o.val.val.2) := by
      change Medium (Real.cosh (ell (p.edgeLabel o.val.val.1 o.val.val.2)))
      rw [o.val.property]
      exact he
    rcases hrole o.val.val.1 with hflat | hgen
    · exact False.elim (hflat.1 o.property)
    · exact (hgen.2.2 o.val.val.2 hvalue).2.2
  have hmiddle_ne : (∑ o : GenuineFiber p ell e, angle p ell o.val.val) ≠
      2 * Real.pi :=
    even_middle_angle_sum_ne_two_pi
      (fun o : GenuineFiber p ell e => angle p ell o.val.val) heven hrange
  have hzero (o : {o : Fiber p e // ¬ Genuine (values p ell o.val.1)}) :
      angle p ell o.val.val = 0 := by
    have hvalue : Medium (values p ell o.val.val.1 o.val.val.2) := by
      change Medium (Real.cosh (ell (p.edgeLabel o.val.val.1 o.val.val.2)))
      rw [o.val.property]
      exact he
    rcases hrole o.val.val.1 with hflat | hgen
    · exact hflat.2.2 o.val.val.2 hvalue
    · exact False.elim (o.property hgen.1)
  have hzero_sum :
      (∑ o : {o : Fiber p e // ¬ Genuine (values p ell o.val.1)},
        angle p ell o.val.val) = 0 := by
    apply Finset.sum_eq_zero
    intro o ho
    exact hzero o
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (p := fun o : Fiber p e => Genuine (values p ell o.val.1))
    (f := fun o : Fiber p e => angle p ell o.val)
  have hsum : (∑ o : GenuineFiber p ell e, angle p ell o.val.val) =
      ∑ o : Fiber p e, angle p ell o.val := by
    simpa only [GenuineFiber, hzero_sum, add_zero] using hsplit
  refine ⟨heven, ?_⟩
  intro hclosed
  apply hmiddle_ne
  rw [hsum]
  exact hclosed

/- This transports the parity and obstruction to the ORIGINAL quotient,
   using the checked648/681 legal-relabel equivalences and actual angle sums.
 -/
theorem original_middle_edge_obstruction {T : Type*} [Fintype T]
    (p : RawFacePairing T) (s : T → P4) (ell : p.GlobalEdge → ℝ)
    (data : StableBlocks (relabel p s) (field p s ell))
    (e : p.GlobalEdge) (he : Medium (Real.cosh (ell e))) :
    Even (Fintype.card (GenuineFiber p ell e)) ∧
      (∑ o : Fiber p e, angle p ell o.val) ≠ 2 * Real.pi := by
  classical
  have he' : Medium
      (Real.cosh (field p s ell ((globalEdges p s).symm e))) := by
    simpa only [field, Function.comp_apply, Equiv.apply_symm_apply] using he
  have hb := stable_middle_edge_obstruction
    (relabel p s) (field p s ell) data ((globalEdges p s).symm e) he'
  have hev : Even (Fintype.card
      (GenuineFiber (relabel p s) (field p s ell) ((globalEdges p s).symm e))) := hb.1
  have hc := Fintype.card_congr (genuineFiberEquiv p s ell e)
  rw [hc] at hev
  have hne : (∑ o : Fiber (relabel p s) ((globalEdges p s).symm e),
      angle (relabel p s) (field p s ell) o.val) ≠ 2 * Real.pi := hb.2
  rw [angle_sum_transport] at hne
  exact ⟨hev, hne⟩

theorem original_no_closed_of_stable {T : Type*} [Fintype T] [Nonempty T]
    (p : RawFacePairing T) (s : T → P4) (ell : p.GlobalEdge → ℝ)
    (data : StableBlocks (relabel p s) (field p s ell)) :
    ¬ (∀ e : p.GlobalEdge, (∑ o : Fiber p e, angle p ell o.val) = 2 * Real.pi) := by
  intro hclosed
  obtain ⟨t⟩ := (inferInstance : Nonempty T)
  let e : p.GlobalEdge := p.edgeLabel t (edgePerm (s t) 1)
  have hlocal : Medium (values (relabel p s) (field p s ell) t 1) := by
    rcases data t with hf | hg
    · simpa [Medium, flatLower, flatUpper] using hf.1 1
    · simpa [Medium, genuineLower, genuineUpper] using hg.1 1
  have he : Medium (Real.cosh (ell e)) := by
    rw [values_transport] at hlocal
    exact hlocal
  exact (original_middle_edge_obstruction p s ell data e he).2 (hclosed e)

/- Each block is independently close to one of two fixed templates AFTER
   a genuine vertex relabel. No transverse-coordinate equality is imposed.
 -/
def PerturbedBlocks {T : Type*} (p : RawFacePairing T) (s : T → P4)
    (ell : p.GlobalEdge → ℝ) (ε : ℝ) : Prop :=
  ∀ t,
    (∀ q, |(values p ell t ∘ edgePerm (s t)) q - F0 q| < ε) ∨
    (∀ q, |(values p ell t ∘ edgePerm (s t)) q - G0 q| < ε)

def RadiusSpecification (ε : ℝ) : Prop :=
  (∀ x : Coordinates, (∀ q, |x q - F0 q| < ε) → FlatStable x) ∧
  (∀ x : Coordinates, (∀ q, |x q - G0 q| < ε) → GenuineStable x)

theorem normalized_stable_blocks {T : Type*}
    (ε : ℝ) (hε : RadiusSpecification ε)
    (p : RawFacePairing T) (s : T → P4) (ell : p.GlobalEdge → ℝ)
    (data : PerturbedBlocks p s ell ε) :
    StableBlocks (relabel p s) (field p s ell) := by
  intro t
  rcases data t with hf | hg
  · left
    rw [values_transport]
    exact hε.1 _ hf
  · right
    rw [values_transport]
    exact hε.2 _ hg

universe u

/- The COMPLETE original71.3-shaped global target. The witness epsilon is
   obtained once from685 BEFORE choosing the finite nonempty block set,
   actual RawFacePairing, legal relabels, or positive common length field.
   Only coordinatewise closeness is assumed about the local six-vectors.
 -/
theorem uniform_original_no_closed_angle_sum :
    ∃ ε > 0, ∀ (T : Type u) [Fintype T] [Nonempty T]
      (p : RawFacePairing T) (s : T → P4) (ell : p.GlobalEdge → ℝ),
      (∀ e, 0 < ell e) → PerturbedBlocks p s ell ε →
      ¬ (∀ e : p.GlobalEdge, (∑ o : Fiber p e, angle p ell o.val) = 2 * Real.pi) := by
  obtain ⟨ε, hεpos, hF, hG⟩ := uniform_full_six_coordinate_neighborhood
  refine ⟨ε, hεpos, ?_⟩
  intro T _ _ p s ell _hpos data
  have hspec : RadiusSpecification ε := ⟨hF, hG⟩
  exact original_no_closed_of_stable p s ell
    (normalized_stable_blocks ε hspec p s ell data)

#print axioms actual_low_slot_equiv
#print axioms stable_middle_edge_obstruction
#print axioms original_middle_edge_obstruction
#print axioms uniform_original_no_closed_angle_sum

end Section71GlobalNeighborhood694Temporary

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``Section71GlobalNeighborhood694Temporary.actual_low_slot_equiv,
      ``Section71GlobalNeighborhood694Temporary.stable_middle_edge_obstruction,
      ``Section71GlobalNeighborhood694Temporary.original_middle_edge_obstruction,
      ``Section71GlobalNeighborhood694Temporary.uniform_original_no_closed_angle_sum] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"Section71-704 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"Section71-704 disallowed axiom {ax} for {name}"
    Lean.logInfo m!"Section71-704 CHECKED {name} axioms={axioms}"
