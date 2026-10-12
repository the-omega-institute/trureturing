/- GID: D5/S3/Geometry/Gluing/ActualLinkAffineFan
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualLinkAffineFan
   mirror-E: none(waiver:actual-strict-affine-coordinates)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Strict affine sectors parametrize the actual ordered-corner neighborhood. -/
import D5.S3.Geometry.Gluing.ActualCornerPointPeriods
import D5.S3.Geometry.Gluing.CyclicTriangleDisk
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousMap.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators Fin.NatCast
namespace D5.S3.Geometry.Gluing.ActualLinkAffineFan
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Gluing.ActualLinkCornerChains
open D5.S3.Geometry.Gluing.ActualCornerPointPeriods
variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]
/-- The radial cutoff is strict; the cutoff boundary remains in the ambient carrier. -/
abbrev Sector := {p : ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 < 1}
/-- Incoming and outgoing face coordinates retain their source ordering. -/
def beta (c : Fin 4) (s : Fin 3) (p : ℝ × ℝ) (l : Fin 4) : ℝ :=
  if l = tip c s then 1 - (p.1 + p.2) / 2
  else if l = incoming c s then p.1 / 2
  else if l = outgoing c s then p.2 / 2 else 0
private theorem beta_values (c : Fin 4) (s : Fin 3) (p : ℝ × ℝ) :
    beta c s p (corner c s) = 0 ∧
    beta c s p (tip c s) = 1 - (p.1 + p.2) / 2 ∧
    beta c s p (incoming c s) = p.1 / 2 ∧
    beta c s p (outgoing c s) = p.2 / 2 := by
  fin_cases c <;> fin_cases s <;> simp [beta,corner,tip,incoming,outgoing]
private theorem beta_simplex (c : Fin 4) (s : Fin 3) (p : Sector) :
    (∀ l, 0 ≤ beta c s p.val l) ∧
    (∑ l, beta c s p.val l) = 1 ∧ 1 / 2 < beta c s p.val (tip c s) := by
  obtain ⟨ha,hb,hs⟩ := p.property
  have hv := beta_values c s p.val
  refine ⟨?_, ?_, by rw [hv.2.1]; linarith⟩
  · intro l
    unfold beta
    split_ifs <;> linarith
  · fin_cases c <;> fin_cases s <;>
      simp [Fin.sum_univ_succ,beta,tip,incoming,outgoing] <;> ring
private theorem dart_label (u v : G) {d e : Dart Ω} (h : DartRelated u v d e) :
    label (pairing u v) d.1 = label (pairing u v) e.1 := by
  induction h with
  | rel d e h =>
    obtain ⟨f,hfj,_,rfl⟩ := h
    let P : Point u v (label (pairing u v) d.1) :=
      ⟨(d.1,fun l => if l = d.1.2 + 1 then 1 else 0),by
        refine ⟨?_,?_,?_,rfl⟩
        · have hj : d.1.2 ≠ d.1.2 + 1 := by
            generalize d.1.2 = j
            fin_cases j <;> decide
          simp [hj]
        · intro l; dsimp; split_ifs <;> norm_num
        · simp⟩
    exact (pairedPoint u v P f hfj).property.2.2.2.symm
  | refl d => rfl
  | symm d e _ ih => exact ih.symm
  | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂
/-- The same actual corner class as the phase-zero seed. -/
def vertex (u v : G) (c : Fin 4) (x : Ω) : Vertex (pairing (Ω := Ω) u v) :=
  label (pairing u v) (encode u v c (x,0)).1
/-- The actual finite occurrence, with affine coordinates on its original face array. -/
def rawPhi (u v : G) (c : Fin 4) (x : Ω)
    (z : Fin (3 * pointPeriod u v c x) × Sector) : Raw Ω :=
  ((occurrence u v c x z.1).1,
    beta c ((tour u v c)^[z.1.val] (x,0)).2 z.2.val)
private theorem rawPhi_mem (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (z : Fin (3 * pointPeriod u v c x) × Sector) :
    rawPhi u v c x z ∈ Carrier u v (vertex u v c x) := by
  have hv := beta_values c ((tour u v c)^[z.1.val] (x,0)).2 z.2.val
  have hs := beta_simplex c ((tour u v c)^[z.1.val] (x,0)).2 z.2
  refine ⟨hv.1,hs.1,hs.2.1,?_⟩
  exact (dart_label u v (((actual_component_enumeration u v c x).2.2.1 _).mpr
    ⟨z.1,rfl⟩)).symm
/-- The constructed strict-sector map into the genuine source neighborhood. -/
def Phi (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (z : Fin (3 * pointPeriod u v c x) × Sector) :
    ↥(Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))) :=
  ⟨⟨rawPhi u v c x z, rawPhi_mem u v c x z⟩,
    (occurrence u v c x z.1).2,
    (beta_simplex c ((tour u v c)^[z.1.val] (x,0)).2 z.2).2.2,
    ((actual_component_enumeration u v c x).2.2.1 _).mpr ⟨z.1,rfl⟩⟩
private theorem dominant_unique (b : Fin 4 → ℝ) (hn : ∀ l, 0 ≤ b l)
    (hs : (∑ l, b l) = 1) {k l : Fin 4} (hk : 1 / 2 < b k) (hl : 1 / 2 < b l) :
    k = l := by
  classical
  by_contra hne
  have hp := Finset.sum_le_sum_of_subset_of_nonneg
    (f := b) (Finset.subset_univ ({k,l} : Finset (Fin 4)))
    (by intro i _ _; exact hn i)
  simp [hne,hs] at hp
  linarith
private theorem inverse_sector (c : Fin 4) (s : Fin 3) (b : Fin 4 → ℝ)
    (hj : b (corner c s) = 0) (hn : ∀ l, 0 ≤ b l)
    (hs : (∑ l, b l) = 1) (hk : 1 / 2 < b (tip c s)) :
    (0 ≤ 2*b (incoming c s) ∧ 0 ≤ 2*b (outgoing c s) ∧
      2*b (incoming c s) + 2*b (outgoing c s) < 1) ∧
    beta c s (2*b (incoming c s),2*b (outgoing c s)) = b := by
  have h0 := hn 0; have h1 := hn 1; have h2 := hn 2; have h3 := hn 3
  constructor
  · refine ⟨mul_nonneg (by norm_num) (hn _),mul_nonneg (by norm_num) (hn _),?_⟩
    fin_cases c <;> fin_cases s <;>
      simp [corner,tip,incoming,outgoing,Fin.sum_univ_succ] at * <;> linarith
  · funext l
    fin_cases c <;> fin_cases s <;> fin_cases l <;>
      simp [beta,corner,tip,incoming,outgoing,Fin.sum_univ_succ] at * <;> linarith
/-- Every strict original representative has unique actual occurrence and affine coordinates. -/
theorem actual_strict_coordinates (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    Function.Bijective (Phi u v c x) := by
  constructor
  · rintro ⟨i,p⟩ ⟨j,q⟩ h
    have hr : rawPhi u v c x (i,p) = rawPhi u v c x (j,q) :=
      congrArg (fun z => z.val.val) h
    have ht := congrArg Prod.fst hr
    have hb := congrArg Prod.snd hr
    have hpi := beta_simplex c ((tour u v c)^[i.val] (x,0)).2 p
    have hpj := beta_simplex c ((tour u v c)^[j.val] (x,0)).2 q
    have hk : (occurrence u v c x i).2 = (occurrence u v c x j).2 := by
      apply dominant_unique _ hpi.1 hpi.2.1 hpi.2.2
      change beta c ((tour u v c)^[i.val] (x,0)).2 p.val _ > 1 / 2
      change beta c ((tour u v c)^[i.val] (x,0)).2 p.val =
        beta c ((tour u v c)^[j.val] (x,0)).2 q.val at hb
      rw [hb]
      exact hpj.2.2
    have hij := (actual_component_enumeration u v c x).2.1 (Prod.ext ht hk)
    change i = j at hij
    subst j
    have hp := beta_values c ((tour u v c)^[i.val] (x,0)).2 p.val
    have hq := beta_values c ((tour u v c)^[i.val] (x,0)).2 q.val
    have ha := congrFun hb (incoming c ((tour u v c)^[i.val] (x,0)).2)
    have hb' := congrFun hb (outgoing c ((tour u v c)^[i.val] (x,0)).2)
    change beta _ _ _ _ = beta _ _ _ _ at ha hb'
    rw [hp.2.2.1,hq.2.2.1] at ha
    rw [hp.2.2.2,hq.2.2.2] at hb'
    have hpq : p = q := Subtype.ext (Prod.ext (by linarith) (by linarith))
    subst q
    rfl
  · intro y
    obtain ⟨k,hk,hd⟩ := y.property
    obtain ⟨i,hi⟩ := ((actual_component_enumeration u v c x).2.2.1 _).mp hd
    have hj := congrArg (fun d : Dart Ω => d.1.2) hi
    have ht := congrArg Prod.snd hi
    let s := ((tour u v c)^[i.val] (x,0)).2
    have hy := y.val.property
    change corner c s = y.val.val.1.2 at hj
    change tip c s = k at ht
    have hzero : y.val.val.2 (corner c s) = 0 := by rw [hj]; exact hy.1
    have hdom : 1 / 2 < y.val.val.2 (tip c s) := by rw [ht]; exact hk
    obtain ⟨hab,hbeta⟩ := inverse_sector c s y.val.val.2 hzero hy.2.1 hy.2.2.1 hdom
    let p : Sector := ⟨(2*y.val.val.2 (incoming c s),2*y.val.val.2 (outgoing c s)),hab⟩
    refine ⟨(i,p),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change rawPhi u v c x (i,p) = y.val.val
    apply Prod.ext
    · exact congrArg (fun d : Dart Ω => d.1) hi
    · exact hbeta
/-- Strict sectors use the same positive cyclic indexing as the closed fan. -/
instance sector_count_neZero (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    NeZero (3 * pointPeriod u v c x) :=
  ⟨by have h := (actual_component_enumeration u v c x).1; omega⟩
def swap (p : Sector) : Sector :=
  ⟨(p.val.2,p.val.1),p.property.2.1,p.property.1,
    by simpa only [add_comm] using p.property.2.2⟩
/-- Only the positive cyclic seam generates the fan equivalence. -/
def seam {n : ℕ} [NeZero n] (z w : Fin n × Sector) : Prop :=
  z.2.val.2 = 0 ∧ w = (z.1 + 1, swap z.2)
private theorem phase_next (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (i : Fin (3 * pointPeriod u v c x)) :
    (tour u v c)^[(i+1).val] (x,0) =
      tour u v c ((tour u v c)^[i.val] (x,0)) := by
  have hp := (actual_component_enumeration u v c x).2.2.2.2.2.1
  have hi : (i+1).val = (i.val+1) % (3 * pointPeriod u v c x) := by
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hi]
  have he := Function.iterate_mod_minimalPeriod_eq (f := tour u v c) (x := (x,0))
    (n := i.val+1)
  simpa only [hp, Function.iterate_succ_apply'] using he
private theorem phase_prev (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (i : Fin (3 * pointPeriod u v c x)) :
    (tour u v c)^[(i-1).val] (x,0) =
      (tour u v c).symm ((tour u v c)^[i.val] (x,0)) := by
  apply (tour u v c).injective
  rw [Equiv.apply_symm_apply, ← phase_next]
  simp only [sub_add_cancel]
private theorem affine_forward (u v : G) (c : Fin 4) (z : Ω × Fin 3) (p : Sector) [Finite Ω]
    (hb : p.val.2 = 0) :
    move u v (outgoing c z.2) ((encode u v c z).1,beta c z.2 p.val) =
      ((encode u v c (tour u v c z)).1,beta c (tour u v c z).2 (swap p).val) := by
  apply Prod.ext
  · have hstep : DartStep u v (encode u v c z)
        (dartMove u v (outgoing c z.2) (encode u v c z)) := by
      refine ⟨outgoing c z.2,?_,?_,rfl⟩ <;>
        change outgoing c z.2 ≠ _ <;>
        rcases z with ⟨w,s⟩ <;> fin_cases c <;> fin_cases s <;>
        simp [encode,outgoing,incoming,corner,tip]
    rcases ((actual_component_enumeration u v c z.1).2.2.2.2.1 z _).mp hstep with hh | hh
    · exact congrArg (fun d : Dart Ω => d.1) hh
    · have hbad := congrArg (fun d : Dart Ω => d.1.2) hh
      rcases z with ⟨w,s⟩
      fin_cases c <;> fin_cases s <;>
        simp [dartMove,encode,corner,outgoing,facePerm,tour] at hbad
  · rcases z with ⟨w,s⟩
    funext l
    fin_cases c <;> fin_cases s <;> fin_cases l <;>
      simp [move,beta,swap,tip,incoming,outgoing,facePerm,tour,hb]
private theorem affine_backward (u v : G) (c : Fin 4) (z : Ω × Fin 3) (p : Sector) [Finite Ω]
    (ha : p.val.1 = 0) :
    move u v (incoming c z.2) ((encode u v c z).1,beta c z.2 p.val) =
      ((encode u v c ((tour u v c).symm z)).1,
        beta c ((tour u v c).symm z).2 (swap p).val) := by
  apply Prod.ext
  · have hstep : DartStep u v (encode u v c z)
        (dartMove u v (incoming c z.2) (encode u v c z)) := by
      refine ⟨incoming c z.2,?_,?_,rfl⟩ <;>
        change incoming c z.2 ≠ _ <;>
        rcases z with ⟨w,s⟩ <;> fin_cases c <;> fin_cases s <;>
        simp [encode,outgoing,incoming,corner,tip]
    rcases ((actual_component_enumeration u v c z.1).2.2.2.2.1 z _).mp hstep with hh | hh
    · have hbad := congrArg (fun d : Dart Ω => d.1.2) hh
      rcases z with ⟨w,s⟩
      fin_cases c <;> fin_cases s <;>
        simp [dartMove,encode,corner,incoming,facePerm,tour] at hbad
    · exact congrArg (fun d : Dart Ω => d.1) hh
  · rcases z with ⟨w,s⟩
    funext l
    fin_cases c <;> fin_cases s <;> fin_cases l <;>
      simp [move,beta,swap,tip,incoming,outgoing,facePerm,tour,ha]
/-- The full guarded source generator is exactly a positive seam or its reverse.
The period is the point period, including its wrap, and the corner remains ordered. -/
theorem actual_step_iff (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (z w : Fin (3 * pointPeriod u v c x) × Sector) :
    Step u v (Phi u v c x z).val (Phi u v c x w).val ↔
      seam z w ∨ seam w z := by
  rcases z with ⟨i,p⟩
  let t := (tour u v c)^[i.val] (x,0)
  have hn (hb : p.val.2 = 0) :
      move u v (outgoing c t.2) (rawPhi u v c x (i,p)) =
        rawPhi u v c x (i+1,swap p) := by
    change move u v (outgoing c t.2) ((encode u v c t).1,beta c t.2 p.val) = _
    rw [affine_forward u v c t p hb]
    unfold rawPhi occurrence
    rw [phase_next]
  have hp (ha : p.val.1 = 0) :
      move u v (incoming c t.2) (rawPhi u v c x (i,p)) =
        rawPhi u v c x (i-1,swap p) := by
    change move u v (incoming c t.2) ((encode u v c t).1,beta c t.2 p.val) = _
    rw [affine_backward u v c t p ha]
    unfold rawPhi occurrence
    rw [phase_prev]
  have backward_seam : seam w (i,p) ↔ p.val.1 = 0 ∧ w = (i-1,swap p) := by
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
      refine ⟨ha,Prod.ext (by simp) (Subtype.ext (Prod.ext rfl rfl))⟩
  rw [backward_seam]
  constructor
  · rintro ⟨f,hfj,hzero,he⟩
    change f ≠ corner c t.2 at hfj
    change beta c t.2 p.val f = 0 at hzero
    have hfk : f ≠ tip c t.2 := by
      intro h
      have hdom := (beta_simplex c t.2 p).2.2
      rw [← h,hzero] at hdom
      norm_num at hdom
    have hf : f = outgoing c t.2 ∨ f = incoming c t.2 := by
      generalize t.2 = s at *
      fin_cases c <;> fin_cases s <;> fin_cases f <;>
        simp_all [corner,tip,outgoing,incoming]
    have inj := (actual_strict_coordinates u v c x).1
    rcases hf with rfl | rfl
    · have hb : p.val.2 = 0 := by
        rw [(beta_values c t.2 p.val).2.2.2] at hzero
        linarith
      refine Or.inl ⟨hb,inj ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact he.trans (hn hb)
    · have ha : p.val.1 = 0 := by
        rw [(beta_values c t.2 p.val).2.2.1] at hzero
        linarith
      refine Or.inr ⟨ha,inj ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact he.trans (hp ha)
  · rintro (⟨hb,rfl⟩ | ⟨ha,rfl⟩)
    · refine ⟨outgoing c t.2,?_,?_,(hn hb).symm⟩
      · change outgoing c t.2 ≠ corner c t.2
        generalize t.2 = s
        fin_cases c <;> fin_cases s <;> decide
      · change beta c t.2 p.val (outgoing c t.2) = 0
        rw [(beta_values c t.2 p.val).2.2.2,hb]; norm_num
    · refine ⟨incoming c t.2,?_,?_,(hp ha).symm⟩
      · change incoming c t.2 ≠ corner c t.2
        generalize t.2 = s
        fin_cases c <;> fin_cases s <;> decide
      · change beta c t.2 p.val (incoming c t.2) = 0
        rw [(beta_values c t.2 p.val).2.2.1,ha]; norm_num
/-- Full original chains, including all intermediate representatives, correspond
exactly to chains generated by the positive strict fan seams. -/
theorem actual_eqvgen_iff (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (z w : Fin (3 * pointPeriod u v c x) × Sector) :
    Related u v (Phi u v c x z).val (Phi u v c x w).val ↔
      Relation.EqvGen seam z w := by
  let e := Equiv.ofBijective (Phi u v c x) (actual_strict_coordinates u v c x)
  constructor
  · intro h
    have hr := ((actual_guarded_point_analysis u v _ _).2.2.2
      (encode u v c (x,0)) (Phi u v c x z).property (Phi u v c x w).property).mp h
    have lift : ∀ (a b : ↥(Neighborhood u v (ν := vertex u v c x)
        (encode u v c (x,0)))),
        Relation.EqvGen (fun a b => Step u v a.val b.val) a b →
        Relation.EqvGen seam (e.symm a) (e.symm b) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
        have hs := actual_step_iff u v c x (e.symm a) (e.symm b)
        rw [show Phi u v c x (e.symm a) = a from e.apply_symm_apply a,
          show Phi u v c x (e.symm b) = b from e.apply_symm_apply b] at hs
        rcases hs.mp hab with hh | hh
        · exact Relation.EqvGen.rel _ _ hh
        · exact (Relation.EqvGen.rel _ _ hh).symm
      | refl a => exact Relation.EqvGen.refl _
      | symm a b _ ih => exact ih.symm
      | trans a b d _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [show Phi u v c x = e from rfl, e.symm_apply_apply] using lift _ _ hr
  · intro h
    induction h with
    | rel a b hab =>
      exact Relation.EqvGen.rel _ _ ((actual_step_iff u v c x a b).mpr (Or.inl hab))
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b d _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
/-- The inverse uses the unique actual occurrence, not a chosen abstract cycle. -/
def coordinateEquiv (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :=
  Equiv.ofBijective (Phi u v c x) (actual_strict_coordinates u v c x)
private theorem inverse_index_fiber (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (y : ↥(Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))))
    (i : Fin (3 * pointPeriod u v c x)) :
    ((coordinateEquiv u v c x).symm y).1 = i ↔
      y.val.val.1 = (occurrence u v c x i).1 ∧
        1/2 < y.val.val.2 (occurrence u v c x i).2 := by
  obtain ⟨⟨j,p⟩,rfl⟩ := (actual_strict_coordinates u v c x).2 y
  change ((coordinateEquiv u v c x).symm (coordinateEquiv u v c x (j,p))).1 = i ↔ _
  rw [Equiv.symm_apply_apply]
  change j = i ↔ _
  constructor
  · rintro rfl
    exact ⟨rfl,(beta_simplex c ((tour u v c)^[j.val] (x,0)).2 p).2.2⟩
  · rintro ⟨hc,ht⟩
    have hb := beta_simplex c ((tour u v c)^[j.val] (x,0)).2 p
    have hk : (occurrence u v c x j).2 = (occurrence u v c x i).2 :=
      dominant_unique _ hb.1 hb.2.1 hb.2.2 ht
    exact (actual_component_enumeration u v c x).2.1 (Prod.ext hc hk)
def closedInput {n : ℕ} (z : Fin n × Sector) : CyclicTriangleDisk.Point n :=
  (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.1,z.2.property.2.2.le⟩)
private def strictInput {n : ℕ} (z : CyclicTriangleDisk.Point n)
    (h : CyclicTriangleDisk.radius z < 1) : Fin n × Sector :=
  (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.1,h⟩)
private theorem closed_radius_invariant {n : ℕ} [NeZero n]
    {a b : CyclicTriangleDisk.Point n} (h : CyclicTriangleDisk.Related a b) :
    CyclicTriangleDisk.radius a = CyclicTriangleDisk.radius b := by
  induction h with
  | rel a b h =>
    obtain ⟨_,rfl⟩ := h
    simp only [CyclicTriangleDisk.radius,CyclicTriangleDisk.swap,add_comm]
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b d _ _ ih₁ ih₂ => exact ih₁.trans ih₂
private theorem closed_chain_restriction {n : ℕ} [NeZero n]
    (z w : Fin n × Sector) :
    CyclicTriangleDisk.Related (closedInput z) (closedInput w) ↔
      Relation.EqvGen seam z w := by
  constructor
  · intro h
    have lift : ∀ (a b : CyclicTriangleDisk.Point n), CyclicTriangleDisk.Related a b →
        ∀ (ha : CyclicTriangleDisk.radius a < 1) (hb : CyclicTriangleDisk.radius b < 1),
        Relation.EqvGen seam (strictInput a ha) (strictInput b hb) := by
      intro a b hab
      induction hab with
      | rel a b h =>
        obtain ⟨hzero,rfl⟩ := h
        intro ha hb
        exact Relation.EqvGen.rel _ _ ⟨hzero,rfl⟩
      | refl a => exact fun _ _ => Relation.EqvGen.refl _
      | symm a b _ ih => exact fun ha hb => (ih hb ha).symm
      | trans a b d hab _ ih₁ ih₂ =>
        intro ha hd
        have hb : CyclicTriangleDisk.radius b < 1 := by
          rw [← closed_radius_invariant hab]
          exact ha
        exact Relation.EqvGen.trans _ _ _ (ih₁ ha hb) (ih₂ hb hd)
    exact lift _ _ h z.2.property.2.2 w.2.property.2.2
  · intro h
    induction h with
    | rel a b h =>
      obtain ⟨hzero,rfl⟩ := h
      exact Relation.EqvGen.rel _ _ ⟨hzero,rfl⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b d _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
/-- The full original affine relation agrees with the original closed fan
relation on strict inputs; intermediate fan representatives retain the cutoff. -/
theorem actual_full_fan_correspondence (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (z w : Fin (3 * pointPeriod u v c x) × Sector) :
    Related u v (Phi u v c x z).val (Phi u v c x w).val ↔
      CyclicTriangleDisk.Related (closedInput z) (closedInput w) := by
  rw [actual_eqvgen_iff, closed_chain_restriction]
/-- The original retained tetrahedron: all four cap bounds are retained. -/
abbrev TruncatedTetrahedron := {a : Fin 4 → ℝ //
  (∀ i, 0 ≤ a i ∧ a i ≤ 3/4) ∧ (∑ i, a i) = 1}
abbrev TruncatedPoint (Ω : Type*) := Ω × TruncatedTetrahedron
/-- The actual zero-face gluing on complete retained tetrahedra. -/
def truncatedMove (u v : G) (f : Fin 4) (a : TruncatedPoint Ω) : TruncatedPoint Ω :=
  (act a.1 (faceWord u v f), ⟨fun i => a.2.val ((facePerm f).symm i),
    (fun i => a.2.property.1 _), ((facePerm f).symm.sum_comp a.2.val).trans
      a.2.property.2⟩)
def TruncatedStep (u v : G) (a b : TruncatedPoint Ω) : Prop :=
  ∃ f : Fin 4, a.2.val f = 0 ∧ b = truncatedMove u v f a
/-- The original cap component is selected by the actual corner label. -/
def Slice (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) : Set (TruncatedPoint Ω) :=
  {a | ∃ j : Fin 4, a.2.val j = 3/4 ∧ label (pairing u v) (a.1,j) = ν}
def alpha (j : Fin 4) (b : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  (if i = j then 3/4 else 0) + b i / 4
private theorem coordinate_le_one {b : Fin 4 → ℝ} (hn : ∀ i, 0 ≤ b i)
    (hs : (∑ i, b i) = 1) (i : Fin 4) : b i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hn j)
    (Finset.mem_univ i)
  simpa only [hs] using h
private theorem alpha_mem (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (p : Point u v ν) :
    (∀ i, 0 ≤ alpha p.val.1.2 p.val.2 i ∧ alpha p.val.1.2 p.val.2 i ≤ 3/4) ∧
    (∑ i, alpha p.val.1.2 p.val.2 i) = 1 := by
  obtain ⟨hj,hn,hs,_⟩ := p.property
  constructor
  · intro i
    have hi := hn i
    have hu := coordinate_le_one hn hs i
    by_cases he : i = p.val.1.2
    · subst i; norm_num [alpha,hj]
    · simp only [alpha,if_neg he,zero_add]; constructor <;> linarith
  · simp only [alpha,Finset.sum_add_distrib]
    rw [← Finset.sum_div,hs]
    norm_num
/-- Literal affine map from the entire original corner triangle into its cap. -/
def toTruncation (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (p : Point u v ν) : TruncatedPoint Ω :=
  (p.val.1.1,⟨alpha p.val.1.2 p.val.2,alpha_mem u v p⟩)
private theorem toTruncation_mem (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (p : Point u v ν) : toTruncation u v p ∈ Slice u v ν :=
  ⟨p.val.1.2,by simp [toTruncation,alpha,p.property.1],p.property.2.2.2⟩
private theorem cap_unique (a : TruncatedPoint Ω) {j k : Fin 4}
    (hj : a.2.val j = 3/4) (hk : a.2.val k = 3/4) : j = k :=
  dominant_unique a.2.val (fun i => (a.2.property.1 i).1) a.2.property.2
    (by rw [hj]; norm_num) (by rw [hk]; norm_num)
private theorem toTruncation_injective (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)} :
    Function.Injective (toTruncation u v (ν := ν)) := by
  intro p q h
  have ht := congrArg Prod.fst h
  have ha := congrArg (fun z : TruncatedPoint Ω => z.2.val) h
  have hj : p.val.1.2 = q.val.1.2 := by
    apply cap_unique (toTruncation u v p)
      (show (toTruncation u v p).2.val p.val.1.2 = 3/4 by
        simp [toTruncation,alpha,p.property.1])
    rw [h]
    simp [toTruncation,alpha,q.property.1]
  apply Subtype.ext
  apply Prod.ext (Prod.ext ht hj)
  funext i
  have hh := congrFun ha i
  change alpha p.val.1.2 p.val.2 i = alpha q.val.1.2 q.val.2 i at hh
  simp only [alpha,hj] at hh
  linarith
private theorem cap_preimage (u v : G) (a : TruncatedPoint Ω) (j : Fin 4)
    (hj : a.2.val j = 3/4) :
    ∃ p : Point u v (label (pairing u v) (a.1,j)), toTruncation u v p = a := by
  let b : Fin 4 → ℝ := fun i => if i = j then 0 else 4 * a.2.val i
  have hb : (∑ i, b i) = 1 := by
    have hs := a.2.property.2
    fin_cases j <;> simp [b,Fin.sum_univ_succ] at * <;> linarith
  let p : Point u v (label (pairing u v) (a.1,j)) :=
    ⟨((a.1,j),b),by
      refine ⟨by simp [b],?_,hb,rfl⟩
      intro i
      dsimp only [b]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (by norm_num) (a.2.property.1 i).1⟩
  refine ⟨p,Prod.ext rfl (Subtype.ext ?_)⟩
  funext i
  change alpha j b i = a.2.val i
  by_cases hi : i = j
  · subst i; simp [alpha,b,hj]
  · simp [alpha,b,hi]
/-- Both full carriers, including every boundary tie, correspond under alpha. -/
theorem actual_slice_carriers (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Function.Bijective (fun p : Point u v ν =>
      (⟨toTruncation u v p,toTruncation_mem u v p⟩ : ↥(Slice u v ν))) := by
  constructor
  · intro p q h
    exact toTruncation_injective u v (congrArg Subtype.val h)
  · rintro ⟨a,j,hj,hν⟩
    obtain ⟨p,hp⟩ := cap_preimage u v a j hj
    subst ν
    exact ⟨p,Subtype.ext hp⟩
private theorem alpha_paired (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (p : Point u v ν) (f : Fin 4) (hf : f ≠ p.val.1.2) :
    toTruncation u v (pairedPoint u v p f hf) = truncatedMove u v f (toTruncation u v p) := by
  apply Prod.ext
  · rfl
  apply Subtype.ext
  funext i
  change alpha (facePerm f p.val.1.2) (fun k => p.val.2 ((facePerm f).symm k)) i =
    alpha p.val.1.2 p.val.2 ((facePerm f).symm i)
  simp only [alpha, Equiv.symm_apply_eq]
private theorem truncated_step_lift (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (p : Point u v ν) {a : TruncatedPoint Ω} (h : TruncatedStep u v (toTruncation u v p) a) :
    ∃ q : Point u v ν, Step u v p q ∧ toTruncation u v q = a := by
  obtain ⟨f,hf,rfl⟩ := h
  have hfj : f ≠ p.val.1.2 := by
    intro he; subst f
    change alpha _ _ _ = 0 at hf
    simp [alpha,p.property.1] at hf
  have hz : p.val.2 f = 0 := by
    change alpha _ _ _ = 0 at hf
    simp only [alpha,if_neg hfj,zero_add] at hf
    linarith
  exact ⟨pairedPoint u v p f hfj,⟨f,hfj,hz,rfl⟩,alpha_paired u v p f hfj⟩
/-- The exact guarded original face generators correspond in both directions. -/
theorem actual_slice_step_iff (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (p q : Point u v ν) :
    Step u v p q ↔ TruncatedStep u v (toTruncation u v p) (toTruncation u v q) := by
  constructor
  · rintro ⟨f,hfj,hf,hq⟩
    have he : q = pairedPoint u v p f hfj := Subtype.ext hq
    subst q
    refine ⟨f,?_,alpha_paired u v p f hfj⟩
    change alpha _ _ _ = 0
    simp [alpha,hfj,hf]
  · intro h
    obtain ⟨z,hz,he⟩ := truncated_step_lift u v p h
    exact (toTruncation_injective u v he) ▸ hz
private theorem slice_labels_unique (u v : G) {a : TruncatedPoint Ω}
    {ν μ : Vertex (pairing (Ω := Ω) u v)} (hν : a ∈ Slice u v ν) (hμ : a ∈ Slice u v μ) :
    ν = μ := by
  obtain ⟨j,hj,hν⟩ := hν
  obtain ⟨k,hk,hμ⟩ := hμ
  have he := cap_unique a hj hk
  subst k
  exact hν.symm.trans hμ
private theorem slice_step_invariant (u v : G) (ν : Vertex (pairing (Ω := Ω) u v))
    {a b : TruncatedPoint Ω} (h : TruncatedStep u v a b) :
    a ∈ Slice u v ν ↔ b ∈ Slice u v ν := by
  constructor
  · intro ha
    obtain ⟨p,hp⟩ := (actual_slice_carriers u v ν).2 ⟨a,ha⟩
    have hp' : toTruncation u v p = a := congrArg Subtype.val hp
    rw [← hp'] at h
    obtain ⟨q,_,hq⟩ := truncated_step_lift u v p h
    rw [← hq]
    exact toTruncation_mem u v q
  · intro hb
    obtain ⟨f,hf,hmove⟩ := h
    obtain ⟨j,hj,hν⟩ := hb
    have hc : a.2.val ((facePerm f).symm j) = 3/4 := by
      rw [hmove] at hj
      exact hj
    obtain ⟨p,hp⟩ := cap_preimage u v a ((facePerm f).symm j) hc
    have hh : TruncatedStep u v (toTruncation u v p) b := by
      rw [hp]; exact ⟨f,hf,hmove⟩
    obtain ⟨q,_,hq⟩ := truncated_step_lift u v p hh
    have hb' := toTruncation_mem u v q
    rw [hq] at hb'
    have he := slice_labels_unique u v hb' ⟨j,hj,hν⟩
    exact ⟨(facePerm f).symm j,hc,he⟩
private theorem slice_chain_invariant (u v : G) (ν : Vertex (pairing (Ω := Ω) u v))
    {a b : TruncatedPoint Ω} (h : Relation.EqvGen (TruncatedStep u v) a b) :
    a ∈ Slice u v ν ↔ b ∈ Slice u v ν := by
  induction h with
  | rel a b h => exact slice_step_invariant u v ν h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
/-- Reflection uses the complete ambient face closure: every intermediate
representative remains in the same original cap component. -/
theorem actual_slice_eqvgen_iff (u v : G) {ν : Vertex (pairing (Ω := Ω) u v)}
    (p q : Point u v ν) : Related u v p q ↔
    Relation.EqvGen (TruncatedStep u v) (toTruncation u v p) (toTruncation u v q) := by
  constructor
  · intro h
    induction h with
    | rel p q h => exact Relation.EqvGen.rel _ _ ((actual_slice_step_iff u v p q).mp h)
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact ih.symm
    | trans p q r _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans (r := TruncatedStep u v)
        (toTruncation u v p) (toTruncation u v q) (toTruncation u v r) ih₁ ih₂
  · intro h
    let e := Equiv.ofBijective (fun p : Point u v ν =>
      (⟨toTruncation u v p,toTruncation_mem u v p⟩ : ↥(Slice u v ν)))
      (actual_slice_carriers u v ν)
    have lift : ∀ {a b : TruncatedPoint Ω}, Relation.EqvGen (TruncatedStep u v) a b →
        ∀ (ha : a ∈ Slice u v ν) (hb : b ∈ Slice u v ν),
        Related u v (e.symm ⟨a,ha⟩) (e.symm ⟨b,hb⟩) := by
      intro a b hab
      induction hab with
      | rel a b hab =>
        intro ha hb
        apply Relation.EqvGen.rel
        apply (actual_slice_step_iff u v _ _).mpr
        have he (z : ↥(Slice u v ν)) : toTruncation u v (e.symm z) = z.val :=
          congrArg Subtype.val (e.apply_symm_apply z)
        rw [he,he]
        exact hab
      | refl a => exact fun _ _ => Relation.EqvGen.refl _
      | symm a b _ ih => exact fun ha hb => (ih hb ha).symm
      | trans a b c hab _ ih₁ ih₂ =>
        intro ha hc
        have hb := (slice_chain_invariant u v ν hab).mp ha
        exact Relation.EqvGen.trans _ _ _ (ih₁ ha hb) (ih₂ hb hc)
    have hh := lift h (toTruncation_mem u v p) (toTruncation_mem u v q)
    change Related u v (e.symm (e p)) (e.symm (e q)) at hh
    simpa only [e.symm_apply_apply] using hh
section Topology
variable [TopologicalSpace Ω] [DiscreteTopology Ω]
omit [DiscreteTopology Ω] in
private theorem continuous_phi (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    Continuous (Phi u v c x) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (rawPhi u v c x)
  apply continuous_prod_of_discrete_left.mpr
  intro i
  have hb : Continuous (fun p : Sector =>
      beta c ((tour u v c)^[i.val] (x,0)).2 p.val) := by
    apply continuous_pi
    intro l
    unfold beta
    split_ifs <;> fun_prop
  exact (continuous_const : Continuous (fun _ : Sector =>
    (occurrence u v c x i).1)).prodMk hb
private theorem continuous_inverse_index (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    Continuous (fun y => ((coordinateEquiv u v c x).symm y).1) := by
  apply continuous_discrete_rng.mpr
  intro i
  have he : (fun y => ((coordinateEquiv u v c x).symm y).1) ⁻¹' {i} =
      {y | y.val.val.1 = (occurrence u v c x i).1} ∩
      {y | 1/2 < y.val.val.2 (occurrence u v c x i).2} := by
    ext y
    exact inverse_index_fiber u v c x y i
  rw [he]
  apply IsOpen.inter
  · exact (isOpen_discrete {(occurrence u v c x i).1}).preimage
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))
  · exact isOpen_lt continuous_const
      ((continuous_apply _).comp
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)))
/-- The constructed coordinates and their inverse are continuous for the original
induced topology on the strict carrier neighborhood. -/
def coordinateHomeomorph (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    (Fin (3 * pointPeriod u v c x) × Sector) ≃ₜ
      ↥(Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))) where
  toEquiv := coordinateEquiv u v c x
  continuous_toFun := continuous_phi u v c x
  continuous_invFun := by
    have hi := continuous_inverse_index u v c x
    have ha : Continuous (fun y : ↥(Neighborhood u v (ν := vertex u v c x)
        (encode u v c (x,0))) => 2 * y.val.val.2
        (incoming c ((tour u v c)^[((coordinateEquiv u v c x).symm y).1.val] (x,0)).2)) := by
      apply continuous_const.mul
      have heval : Continuous (fun z : (Fin 4 → ℝ) × Fin 4 => z.1 z.2) :=
        continuous_prod_of_discrete_right.mpr (fun k => continuous_apply k)
      exact heval.comp
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_of_discreteTopology : Continuous
            (fun i : Fin (3 * pointPeriod u v c x) =>
              incoming c ((tour u v c)^[i.val] (x,0)).2)).comp hi))
    have hb : Continuous (fun y : ↥(Neighborhood u v (ν := vertex u v c x)
        (encode u v c (x,0))) => 2 * y.val.val.2
        (outgoing c ((tour u v c)^[((coordinateEquiv u v c x).symm y).1.val] (x,0)).2)) := by
      apply continuous_const.mul
      have heval : Continuous (fun z : (Fin 4 → ℝ) × Fin 4 => z.1 z.2) :=
        continuous_prod_of_discrete_right.mpr (fun k => continuous_apply k)
      exact heval.comp
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
          ((continuous_of_discreteTopology : Continuous
            (fun i : Fin (3 * pointPeriod u v c x) =>
              outgoing c ((tour u v c)^[i.val] (x,0)).2)).comp hi))
    apply hi.prodMk
    apply continuous_induced_rng.mpr
    convert ha.prodMk hb using 1
    funext y
    change ((coordinateEquiv u v c x).symm y).2.val =
      (2 * y.val.val.2 (incoming c
        ((tour u v c)^[((coordinateEquiv u v c x).symm y).1.val] (x,0)).2),
       2 * y.val.val.2 (outgoing c
        ((tour u v c)^[((coordinateEquiv u v c x).symm y).1.val] (x,0)).2))
    obtain ⟨⟨i,p⟩,rfl⟩ := (actual_strict_coordinates u v c x).2 y
    have he : (coordinateEquiv u v c x).symm (Phi u v c x (i,p)) = (i,p) :=
      (coordinateEquiv u v c x).symm_apply_apply (i,p)
    simp only [he]
    have hv := beta_values c ((tour u v c)^[i.val] (x,0)).2 p.val
    apply Prod.ext
    · change p.val.1 = 2 * beta c _ p.val _
      rw [hv.2.2.1]; ring
    · change p.val.2 = 2 * beta c _ p.val _
      rw [hv.2.2.2]; ring
abbrev ActualQuotient (u v : G) (c : Fin 4) (x : Ω) :=
  Quotient (Relation.EqvGen.setoid (Step u v (ν := vertex u v c x)))
/-- The image carries the subspace topology of the original full quotient. -/
def quotientNeighborhood (u v : G) (c : Fin 4) (x : Ω) :
    Set (ActualQuotient u v c x) :=
  (@Quotient.mk' _ (Relation.EqvGen.setoid (Step u v (ν := vertex u v c x)))) '' Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))
private theorem neighborhood_open (u v : G) (c : Fin 4) (x : Ω) :
    IsOpen (Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))) := by
  have he : Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0)) =
      ⋃ k : Fin 4, {y | 1/2 < y.val.2 k} ∩
        {y | DartRelated u v (encode u v c (x,0)) (y.val.1,k)} := by
    ext y
    simp only [Neighborhood,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  rw [he]
  apply isOpen_iUnion
  intro k
  apply IsOpen.inter
  · exact isOpen_lt continuous_const
      ((continuous_apply k).comp (continuous_snd.comp continuous_subtype_val))
  · exact (isOpen_discrete {d | DartRelated u v (encode u v c (x,0)) (d,k)}).preimage
      (continuous_fst.comp continuous_subtype_val)
/-- Saturation is with respect to the full original EqvGen; openness then follows
from the quotient topology, without global openness of its projection. -/
theorem actual_open_quotient_neighborhood (u v : G) (c : Fin 4) (x : Ω) :
    ((@Quotient.mk' _ (Relation.EqvGen.setoid (Step u v (ν := vertex u v c x)))) ⁻¹' quotientNeighborhood u v c x =
      Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))) ∧
    IsOpen (quotientNeighborhood u v c x) ∧
    Topology.IsQuotientMap ((quotientNeighborhood u v c x).restrictPreimage
      (@Quotient.mk' _ (Relation.EqvGen.setoid (Step u v (ν := vertex u v c x))))) := by
  have hs : (@Quotient.mk' _ (Relation.EqvGen.setoid (Step u v (ν := vertex u v c x)))) ⁻¹' quotientNeighborhood u v c x =
      Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0)) := by
    ext y
    constructor
    · rintro ⟨z,hz,he⟩
      exact ((actual_guarded_point_analysis u v z y).2.2.1 _
        (Quotient.exact he)).mp hz
    · intro hy
      exact ⟨y,hy,rfl⟩
  have ho : IsOpen (quotientNeighborhood u v c x) := by
    apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
    rw [hs]
    exact neighborhood_open u v c x
  exact ⟨hs,ho,isQuotientMap_quotient_mk'.restrictPreimage_isOpen ho⟩
/-- The strict seam quotient is homeomorphic to the open neighborhood in the
full original quotient, with its original subspace topology. -/
def actualSeamQuotientHomeomorph (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    Quotient (Relation.EqvGen.setoid
      (@seam (3 * pointPeriod u v c x) _)) ≃ₜ
      ↥(quotientNeighborhood u v c x) := by
  let q : Point u v (vertex u v c x) → ActualQuotient u v c x := (@Quotient.mk' _ (Relation.EqvGen.setoid (Step u v (ν := vertex u v c x))))
  let N := Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))
  let U := quotientNeighborhood u v c x
  have hs := (actual_open_quotient_neighborhood u v c x).1
  let e : ↥N ≃ₜ ↥(q ⁻¹' U) := Homeomorph.setCongr hs.symm
  let f : (Fin (3 * pointPeriod u v c x) × Sector) → ↥U :=
    U.restrictPreimage q ∘ e ∘ coordinateHomeomorph u v c x
  have hf : Topology.IsQuotientMap f :=
    (actual_open_quotient_neighborhood u v c x).2.2.comp
      (e.isQuotientMap.comp (coordinateHomeomorph u v c x).isQuotientMap)
  have hk : ∀ z w, Relation.EqvGen seam z w ↔ f z = f w := by
    intro z w
    rw [← closed_chain_restriction, ← actual_full_fan_correspondence u v c x z w]
    constructor
    · intro h
      apply Subtype.ext
      exact Quotient.sound h
    · intro h
      exact Quotient.exact (congrArg Subtype.val h)
  let fC : C(Fin (3 * pointPeriod u v c x) × Sector, ↥U) := ⟨f,hf.continuous⟩
  exact (Homeomorph.Quotient.congrRight hk).trans
    (Topology.IsQuotientMap.homeomorph (f := fC) hf)
/-- The actual chart target is the open unit disk in the complex plane. -/
abbrev OpenDisk := {z : ℂ // ‖z‖ < 1}
private def strictFanDiskHomeomorph {n : ℕ} [NeZero n] :
    Quotient (Relation.EqvGen.setoid (@seam n _)) ≃ₜ OpenDisk := by
  let D : Set CyclicTriangleDisk.Disk := {z | ‖z.val‖ < 1}
  let f : CyclicTriangleDisk.Point n → CyclicTriangleDisk.Disk :=
    CyclicTriangleDisk.diskRadial
  have hf : Topology.IsQuotientMap f :=
    CyclicTriangleDisk.homeomorphism.isQuotientMap.comp isQuotientMap_quotient_mk'
  have hD : IsOpen D := isOpen_lt (continuous_norm.comp continuous_subtype_val)
    continuous_const
  let e : (Fin n × Sector) ≃ₜ ↥(f ⁻¹' D) := {
    toFun := fun z => ⟨closedInput z, by
      change ‖CyclicTriangleDisk.radial (closedInput z)‖ < 1
      rw [CyclicTriangleDisk.radial_norm]
      exact z.2.property.2.2⟩
    invFun := fun z => strictInput z.val (by
      have h := z.property
      change ‖CyclicTriangleDisk.radial z.val‖ < 1 at h
      rwa [CyclicTriangleDisk.radial_norm] at h)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_fst.prodMk (continuous_snd.subtype_val.subtype_mk _)
    continuous_invFun := by
      apply Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
      exact ((continuous_subtype_val.comp continuous_snd).comp
        continuous_subtype_val).subtype_mk _ }
  let d : ↥D ≃ₜ OpenDisk := {
    toFun := fun z => ⟨z.val.val,z.property⟩
    invFun := fun z => ⟨⟨z.val,z.property.le⟩,z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let g : (Fin n × Sector) → OpenDisk := d ∘ D.restrictPreimage f ∘ e
  have hg : Topology.IsQuotientMap g :=
    d.isQuotientMap.comp ((hf.restrictPreimage_isOpen hD).comp e.isQuotientMap)
  have hk : ∀ z w : Fin n × Sector, Relation.EqvGen seam z w ↔ g z = g w := by
    intro z w
    rw [← closed_chain_restriction, ← CyclicTriangleDisk.radial_eq_iff_related]
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  let gC : C(Fin n × Sector, OpenDisk) := ⟨g,hg.continuous⟩
  exact (Homeomorph.Quotient.congrRight hk).trans
    (Topology.IsQuotientMap.homeomorph (f := gC) hg)
/-- A disk chart on the open image inside the full original quotient, with its
inherited topology. The closed fan is restricted using its original radial norm
identity; no replacement relation or topology is assumed. -/
def actualOpenDiskChart (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    ↥(quotientNeighborhood u v c x) ≃ₜ OpenDisk :=
  (actualSeamQuotientHomeomorph u v c x).symm.trans strictFanDiskHomeomorph
private theorem continuous_toTruncation (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)} : Continuous (toTruncation u v (ν := ν)) := by
  apply Continuous.prodMk (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_of_discreteTopology : Continuous
    (fun j : Fin 4 => if i = j then (3/4 : ℝ) else 0)).comp
      (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))).add
    (((continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)).div_const 4)
private theorem compact_original_carrier (u v : G)
    (ν : Vertex (pairing (Ω := Ω) u v)) [Finite Ω] : IsCompact (Carrier u v ν) := by
  have heval : Continuous (fun x : Raw Ω => x.2 x.1.2) := by
    have h : Continuous (fun z : (Fin 4 → ℝ) × Fin 4 => z.1 z.2) :=
      continuous_prod_of_discrete_right.mpr (fun k => continuous_apply k)
    exact h.comp (continuous_snd.prodMk continuous_fst.snd)
  have hclosed : IsClosed (Carrier u v ν) := by
    apply (isClosed_eq heval continuous_const).inter
    apply IsClosed.inter
    · have he : {x : Raw Ω | ∀ i : Fin 4, 0 ≤ x.2 i} =
          ⋂ i : Fin 4, {x : Raw Ω | 0 ≤ x.2 i} := by ext x; simp
      change IsClosed {x : Raw Ω | ∀ i : Fin 4, 0 ≤ x.2 i}
      rw [he]
      exact isClosed_iInter fun i => isClosed_le continuous_const
        ((continuous_apply i).comp continuous_snd)
    · apply IsClosed.inter
      · exact isClosed_eq (by fun_prop) continuous_const
      · exact (isClosed_discrete {d : Corner Ω | label (pairing u v) d = ν}).preimage
          continuous_fst
  apply (isCompact_univ.prod (isCompact_Icc :
    IsCompact (Set.Icc (fun _ : Fin 4 => (0 : ℝ)) (fun _ => 1)))).of_isClosed_subset hclosed
  intro p hp
  exact ⟨Set.mem_univ _,hp.2.1,fun i => coordinate_le_one hp.2.1 hp.2.2.1 i⟩
/-- The affine carrier equivalence uses the actual subspace topology of the
original cap inside the original retained tetrahedra. -/
def actualSliceHomeomorph (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) [Finite Ω] :
    Point u v ν ≃ₜ ↥(Slice u v ν) := by
  letI : CompactSpace (Point u v ν) :=
    isCompact_iff_compactSpace.mp (compact_original_carrier u v ν)
  let f : Point u v ν → ↥(Slice u v ν) := fun p =>
    ⟨toTruncation u v p,toTruncation_mem u v p⟩
  have hf : IsHomeomorph f := isHomeomorph_iff_continuous_bijective.mpr
    ⟨(continuous_toTruncation u v).subtype_mk _,actual_slice_carriers u v ν⟩
  exact hf.homeomorph f
abbrev TruncatedQuotient (u v : G) (Ω : Type*) [MulAction Gᵐᵒᵖ Ω] :=
  Quotient (Relation.EqvGen.setoid (TruncatedStep (Ω := Ω) u v))
/-- Image of the actual labeled cap in the full original truncated quotient. -/
def quotientSlice (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    Set (TruncatedQuotient u v Ω) :=
  (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep u v))) '' Slice u v ν
private theorem slice_closed (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :
    IsClosed (Slice u v ν) := by
  have he : Slice u v ν = ⋃ j : Fin 4,
      {a : TruncatedPoint Ω | a.2.val j = 3/4} ∩
      {a | label (pairing u v) (a.1,j) = ν} := by
    ext a
    simp only [Slice,Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff]
  rw [he]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_eq ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
    continuous_const).inter
      ((isClosed_discrete {t : Ω | label (pairing u v) (t,j) = ν}).preimage continuous_fst)
private theorem slice_quotient_restriction (u v : G)
    (ν : Vertex (pairing (Ω := Ω) u v)) :
    ((@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep u v))) ⁻¹' quotientSlice u v ν =
      Slice u v ν) ∧
    Topology.IsQuotientMap ((quotientSlice u v ν).restrictPreimage
      (@Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep u v)))) := by
  let q : TruncatedPoint Ω → TruncatedQuotient u v Ω :=
    @Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep u v))
  let U := quotientSlice u v ν
  have hs : q ⁻¹' U = Slice u v ν := by
    ext a
    constructor
    · rintro ⟨b,hb,he⟩
      exact (slice_chain_invariant u v ν (Quotient.exact he)).mp hb
    · intro ha
      exact ⟨a,ha,rfl⟩
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hU : IsClosed U := hq.isClosed_preimage.mp (by
    rw [hs]
    exact slice_closed u v ν)
  refine ⟨hs,Topology.isQuotientMap_iff_isClosed.mpr ⟨hq.surjective.restrictPreimage _,?_⟩⟩
  intro s
  rw [hU.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    ← hq.isClosed_preimage,
    (hU.preimage hq.continuous).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    Set.image_val_preimage_restrictPreimage]
/-- The original full corner quotient equals the cap image in the full original
truncated quotient, equipped with the inherited topology. No correspondence,
slice-invariance, or quotient-topology hypothesis is supplied by the caller. -/
def actualSliceQuotientHomeomorph (u v : G)
    (ν : Vertex (pairing (Ω := Ω) u v)) [Finite Ω] :
    Quotient (Relation.EqvGen.setoid (Step u v (ν := ν))) ≃ₜ ↥(quotientSlice u v ν) := by
  let q : TruncatedPoint Ω → TruncatedQuotient u v Ω :=
    @Quotient.mk' _ (Relation.EqvGen.setoid (TruncatedStep u v))
  let U := quotientSlice u v ν
  have hs := (slice_quotient_restriction u v ν).1
  let e : ↥(Slice u v ν) ≃ₜ ↥(q ⁻¹' U) := Homeomorph.setCongr hs.symm
  let f : Point u v ν → ↥U :=
    U.restrictPreimage q ∘ e ∘ actualSliceHomeomorph u v ν
  have hf : Topology.IsQuotientMap f :=
    (slice_quotient_restriction u v ν).2.comp
      (e.isQuotientMap.comp (actualSliceHomeomorph u v ν).isQuotientMap)
  have hk : ∀ p r, Related u v p r ↔ f p = f r := by
    intro p r
    rw [actual_slice_eqvgen_iff]
    constructor
    · intro h; exact Subtype.ext (Quotient.sound h)
    · intro h; exact Quotient.exact (congrArg Subtype.val h)
  let fC : C(Point u v ν, ↥U) := ⟨f,hf.continuous⟩
  exact (Homeomorph.Quotient.congrRight hk).trans
    (Topology.IsQuotientMap.homeomorph (f := fC) hf)
end Topology
end D5.S3.Geometry.Gluing.ActualLinkAffineFan
