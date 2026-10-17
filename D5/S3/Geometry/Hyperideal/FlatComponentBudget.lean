/- GID: D5/S3/Geometry/Hyperideal/FlatComponentBudget
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FlatComponentBudget
   mirror-E: none(waiver:actual-positive-length-face-quotient)
   anchors: []
   utility: none
   digest: Native flat budgets and saturated support on the actual face-generated edge quotient. -/

import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
import D5.S3.Geometry.Hyperideal.EdgeStarTransitions

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
namespace D5.S3.Geometry.Hyperideal.FlatComponentBudget

open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing faceEdge)
open D5.S3.Geometry.Hyperideal.PositiveFlatClassification
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (extendedAngle)
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)

variable {T : Type*} [Fintype T]

private noncomputable instance edgeFintype (p : RawFacePairing T) : Fintype p.GlobalEdge :=
  by
    classical
    unfold RawFacePairing.GlobalEdge
    exact Fintype.ofFinite _

private noncomputable instance edgeDecidableEq (p : RawFacePairing T) : DecidableEq p.GlobalEdge :=
  Classical.decEq _

def label (p : RawFacePairing T) (i : T × Fin 6) : p.GlobalEdge := p.edgeLabel i.1 i.2

def coordinates (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t : T) (q : Fin 6) : ℝ :=
  Real.cosh (ell (p.edgeLabel t q))

def angle (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (i : T × Fin 6) : ℝ :=
  extendedAngle (coordinates p ell i.1) i.2

def Flat (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t : T) : Prop :=
  ∃ k : Fin 3, Sector (coordinates p ell t) k

def flats (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) : Finset T := by
  classical
  exact Finset.univ.filter (Flat p ell)

def fiber (p : RawFacePairing T) (e : p.GlobalEdge) : Finset (T × Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => label p i = e)

def degree (p : RawFacePairing T) (e : p.GlobalEdge) : ℕ := (fiber p e).card

def flatOccurrences (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : Finset T) (e : p.GlobalEdge) : Finset (T × Fin 6) := by
  classical
  exact (fiber p e).filter (fun i => i.1 ∈ C)

def piOccurrences (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : Finset T) (e : p.GlobalEdge) : Finset (T × Fin 6) := by
  classical
  exact (flatOccurrences p ell C e).filter (fun i => angle p ell i = Real.pi)

def n (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (C : Finset T) (e : p.GlobalEdge) : ℕ :=
  (flatOccurrences p ell C e).card

def m (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (C : Finset T) (e : p.GlobalEdge) : ℕ :=
  (piOccurrences p ell C e).card

def AngleSums (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) : Prop :=
  ∀ e, ∑ i ∈ fiber p e, angle p ell i = 2*Real.pi

def FaceStep (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t u : T) : Prop :=
  Flat p ell t ∧ Flat p ell u ∧ ∃ f : Fin 4, (p.facePair (t,f)).1 = u

def SameFlatComponent (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t u : T) : Prop :=
  Flat p ell t ∧ Flat p ell u ∧ Relation.EqvGen (FaceStep p ell) t u

def component (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (t : T) : Finset T := by
  classical
  exact Finset.univ.filter (SameFlatComponent p ell t)

private theorem coordinates_positive (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (t : T) : ∀ q, 1 < coordinates p ell t q := by
  intro q
  exact Real.one_lt_cosh.mpr (ne_of_gt (hell _))

private theorem angle_nonnegative (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (i : T × Fin 6) : 0 ≤ angle p ell i := Real.arccos_nonneg _

private theorem genuine_positive (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (i : T × Fin 6) (hi : ¬ Flat p ell i.1) :
    0 < angle p ell i := by
  have hc := positive_classification (coordinates p ell i.1) (coordinates_positive p ell hell _)
  have hg : Genuine (coordinates p ell i.1) := by
    rcases hc.2.1 with hg | ⟨k, hk, _⟩
    · exact hg
    · exact (hi ⟨k,hk⟩).elim
  exact (hc.1.mp hg i.2).1

private theorem pi_sum (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : Finset T) (e : p.GlobalEdge) :
    ∑ i ∈ piOccurrences p ell C e, angle p ell i = (m p ell C e : ℝ)*Real.pi := by
  classical
  calc
    _ = ∑ _i ∈ piOccurrences p ell C e, Real.pi := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    _ = _ := by simp [m, nsmul_eq_mul]

theorem m_le_two (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hsum : AngleSums p ell) (C : Finset T) (e : p.GlobalEdge) : m p ell C e ≤ 2 := by
  classical
  have hsub : piOccurrences p ell C e ⊆ fiber p e :=
    fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hh : ∑ i ∈ piOccurrences p ell C e, angle p ell i ≤
      ∑ i ∈ fiber p e, angle p ell i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => angle_nonnegative p ell i)
  rw [pi_sum, hsum e] at hh
  have hh' : (m p ell C e : ℝ) ≤ 2 := by nlinarith [Real.pi_pos]
  exact_mod_cast hh'

private theorem saturated_flat (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) (e : p.GlobalEdge)
    (hm : m p ell (flats p ell) e = 2) :
    ∀ i, label p i = e → Flat p ell i.1 := by
  classical
  intro i hi
  by_contra hflat
  have hpos := genuine_positive p ell hell i hflat
  let A := piOccurrences p ell (flats p ell) e
  have hsub : A ⊆ fiber p e :=
    fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have himem : i ∈ fiber p e := by simpa [fiber] using hi
  have hinot : i ∉ A := by
    intro h
    have hmem := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
    exact hflat (by simpa [flats] using hmem)
  have hsubset : insert i A ⊆ fiber p e := Finset.insert_subset himem hsub
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun j _ _ => angle_nonnegative p ell j)
  rw [Finset.sum_insert hinot] at hh
  have hpi : ∑ j ∈ A, angle p ell j = 2*Real.pi := by
    rw [pi_sum, hm]
    norm_num
  rw [hpi, hsum e] at hh
  linarith

private theorem step_label (p : RawFacePairing T) (i j : T × Fin 6)
    (h : p.edgeStep i j) : label p i = label p j :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

private theorem saturated_chain (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) (e : p.GlobalEdge)
    (hm : m p ell (flats p ell) e = 2) (i j : T × Fin 6)
    (hi : label p i = e) (hj : label p j = e) :
    Relation.EqvGen (fun u v => p.edgeStep u v ∧ Flat p ell u.1 ∧ Flat p ell v.1) i j := by
  have h : Relation.EqvGen p.edgeStep i j := Quotient.exact (hi.trans hj.symm)
  have hs := saturated_flat p ell hell hsum e hm
  revert hi hj
  induction h with
  | rel a b hab =>
    intro hi hj
    exact Relation.EqvGen.rel _ _ ⟨hab, hs a hi, hs b ((step_label p a b hab).symm.trans hi)⟩
  | refl a => intro _ _; exact Relation.EqvGen.refl _
  | symm a b hab ih =>
    intro hi hj
    apply Relation.EqvGen.symm
    apply ih
    · exact hj
    · exact hi
  | trans a b c hab hbc ihab ihbc =>
    intro hi hj
    have hb : label p b = e :=
      (show label p a = label p b from Quotient.sound hab).symm.trans hi
    exact Relation.EqvGen.trans _ _ _ (ihab hi hb) (ihbc hb hj)

/-- Saturation restricts the actual quotient chain to flat blocks, and its
projection is actual flat/flat face connectivity. -/
theorem saturated_support (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) (e : p.GlobalEdge)
    (hm : m p ell (flats p ell) e = 2) (i j : T × Fin 6)
    (hi : label p i = e) (hj : label p j = e) :
    Relation.EqvGen (fun u v => p.edgeStep u v ∧ Flat p ell u.1 ∧ Flat p ell v.1) i j ∧
      SameFlatComponent p ell i.1 j.1 := by
  have h := saturated_chain p ell hell hsum e hm i j hi hj
  refine ⟨h, saturated_flat p ell hell hsum e hm i hi,
    saturated_flat p ell hell hsum e hm j hj, ?_⟩
  clear hi hj
  induction h with
  | rel a b hab =>
    obtain ⟨hs, ha, hb⟩ := hab
    obtain ⟨x, n, rfl, rfl⟩ := hs
    exact Relation.EqvGen.rel _ _ ⟨ha, hb, x.2, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

def weight (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) : ℝ :=
  Real.log (Real.cosh (ell e))

def correction (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ) (e : p.GlobalEdge) : ℝ :=
  Real.log (Real.cosh (ell e)/(Real.cosh (ell e)-1))

private theorem block_budget (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (t : T) (ht : Flat p ell t) :
    (Real.log 16 + 2 * ∑ q : Fin 6,
      (if angle p ell (t,q) = Real.pi then correction p ell (p.edgeLabel t q) else 0) ≤
      ∑ q : Fin 6, (3*(if angle p ell (t,q) = Real.pi then (1:ℝ) else 0)-1) *
        weight p ell (p.edgeLabel t q)) ∧
    (Real.log 16 < ∑ q : Fin 6,
      (3*(if angle p ell (t,q) = Real.pi then (1:ℝ) else 0)-1) *
        weight p ell (p.edgeLabel t q)) := by
  obtain ⟨k, hk⟩ := ht
  let x := coordinates p ell t
  have hx : ∀ q, 1 < x q := coordinates_positive p ell hell t
  have hpat := ((positive_classification x hx).2.2 k).2.mp hk
  have hflat : D5.S3.Geometry.Hyperideal.FourCycleEnvelopes.cosine
      (x (frame (k.castAdd 3) 0)) (x (frame (k.castAdd 3) 1))
      (x (frame (k.castAdd 3) 2)) (x (frame (k.castAdd 3) 3))
      (x (frame (k.castAdd 3) 4)) (x (frame (k.castAdd 3) 5)) ≤ -1 := hk
  have hb := native_flat_budget _ _ _ _ _ _ (hx _) (hx _) (hx _) (hx _) (hx _) (hx _) hflat
  have hpat' : ∀ q, angle p ell (t,q) =
      if q = k.castAdd 3 ∨ q = k.natAdd 3 then Real.pi else 0 := hpat
  have hpi : (0:ℝ) ≠ Real.pi := Real.pi_ne_zero.symm
  simp_rw [hpat']
  change _ ≤ _ ∧ _ < _
  dsimp [weight, correction]
  change _ ≤ (∑ q : Fin 6, _ * Real.log (x q)) ∧
    _ < (∑ q : Fin 6, _ * Real.log (x q))
  fin_cases k <;>
    simp only [frame, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue,
      Fin.castAdd, Fin.natAdd, Fin.sum_univ_succ, Finset.sum_empty,
      Fin.forall_fin_succ, Real.pi_ne_zero, hpi, zero_ne_one, Fin.reduceEq, Fin.ext_iff] at hb ⊢ <;>
    norm_num [hpi] at hb ⊢ <;> dsimp [x, coordinates] at hb ⊢ <;> constructor <;> linarith [hb.1, hb.2]

private theorem regroup (p : RawFacePairing T) (s : Finset (T × Fin 6))
    (w : p.GlobalEdge → ℝ) :
    ∑ e : p.GlobalEdge, ((s.filter (fun i => label p i = e)).card : ℝ)*w e =
      ∑ i ∈ s, w (label p i) := by
  classical
  simpa using Finset.sum_fiberwise' s (label p) w

private theorem regroup_n (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : Finset T) (w : p.GlobalEdge → ℝ) :
    ∑ e : p.GlobalEdge, (n p ell C e : ℝ)*w e =
      ∑ t ∈ C, ∑ q : Fin 6, w (p.edgeLabel t q) := by
  classical
  have hh : ∀ e, flatOccurrences p ell C e =
      (C.product Finset.univ).filter (fun i => label p i = e) := by
    intro e
    ext i
    simp [flatOccurrences, fiber, and_comm]
  simp_rw [n, hh]
  rw [regroup, Finset.product_eq_sprod, Finset.sum_product]
  rfl

private theorem regroup_m (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : Finset T) (w : p.GlobalEdge → ℝ) :
    ∑ e : p.GlobalEdge, (m p ell C e : ℝ)*w e =
      ∑ t ∈ C, ∑ q : Fin 6,
        if angle p ell (t,q) = Real.pi then w (p.edgeLabel t q) else 0 := by
  classical
  have hh : ∀ e, piOccurrences p ell C e =
      ((C.product Finset.univ).filter (fun i => angle p ell i = Real.pi)).filter
        (fun i => label p i = e) := by
    intro e
    ext i
    simp [piOccurrences, flatOccurrences, fiber]
    tauto
  simp_rw [m, hh]
  rw [regroup, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  rfl

private theorem regroup_budget (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : Finset T) :
    ∑ e : p.GlobalEdge, (3*(m p ell C e : ℝ)-(n p ell C e : ℝ))*weight p ell e =
      ∑ t ∈ C, ∑ q : Fin 6,
        (3*(if angle p ell (t,q) = Real.pi then (1:ℝ) else 0)-1) *
          weight p ell (p.edgeLabel t q) := by
  classical
  simp_rw [sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, regroup_m, regroup_n]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs <;> ring

/-- Every nonempty collection of actual flat blocks has the native component
budget, with all correction terms, on the same common global length field. -/
theorem native_component_budget (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (C : Finset T) (hC : ∀ t ∈ C, Flat p ell t)
    (hCne : C.Nonempty) :
    (C.card : ℝ)*Real.log 16 + 2*∑ e : p.GlobalEdge,
        (m p ell C e : ℝ)*correction p ell e ≤
      ∑ e : p.GlobalEdge, (3*(m p ell C e : ℝ)-(n p ell C e : ℝ))*weight p ell e ∧
    (C.card : ℝ)*Real.log 16 <
      ∑ e : p.GlobalEdge, (3*(m p ell C e : ℝ)-(n p ell C e : ℝ))*weight p ell e := by
  classical
  rw [regroup_m, regroup_budget]
  constructor
  · have hh := Finset.sum_le_sum (fun t ht => (block_budget p ell hell t (hC t ht)).1)
    simpa [Finset.sum_add_distrib, Finset.mul_sum, nsmul_eq_mul] using hh
  · obtain ⟨t, ht⟩ := hCne
    have hh := Finset.sum_lt_sum
      (fun u hu => (block_budget p ell hell u (hC u hu)).2.le)
      ⟨t, ht, (block_budget p ell hell t (hC t ht)).2⟩
    simpa [nsmul_eq_mul] using hh

private theorem component_subset (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (t : T) : component p ell t ⊆ flats p ell := by
  classical
  intro u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.2.1⟩

private theorem component_nonempty (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (t : T) (ht : Flat p ell t) : (component p ell t).Nonempty := by
  classical
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ht, Relation.EqvGen.refl _⟩⟩

private theorem m_mono (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C D : Finset T) (hCD : C ⊆ D) (e : p.GlobalEdge) : m p ell C e ≤ m p ell D e := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hflat,ha⟩ := Finset.mem_filter.mp hi
  obtain ⟨hf,hC⟩ := Finset.mem_filter.mp hflat
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hf,hCD hC⟩,ha⟩

private theorem saturation_localizes (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) (t : T) (e : p.GlobalEdge)
    (hm : m p ell (flats p ell) e = 2) (hpos : 0 < m p ell (component p ell t) e) :
    n p ell (component p ell t) e = degree p e ∧ m p ell (component p ell t) e = 2 := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have hifiber := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hiC := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hie : label p i = e := (Finset.mem_filter.mp hifiber).2
  have hiComp := (Finset.mem_filter.mp hiC).2
  have hall : ∀ j, label p j = e → j.1 ∈ component p ell t := by
    intro j hj
    have hs := (saturated_support p ell hell hsum e hm i j hie hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiComp.1, hs.2.1,
      Relation.EqvGen.trans _ _ _ hiComp.2.2 hs.2.2⟩
  have hflatEq : flatOccurrences p ell (component p ell t) e = fiber p e := by
    ext j
    simp only [flatOccurrences, Finset.mem_filter, and_iff_left_iff_imp]
    intro hj
    exact hall j (Finset.mem_filter.mp hj).2
  constructor
  · exact congrArg Finset.card hflatEq
  · have hglobal : flatOccurrences p ell (flats p ell) e = fiber p e := by
      ext j
      simp only [flatOccurrences, Finset.mem_filter, and_iff_left_iff_imp]
      intro hj
      exact component_subset p ell t (hall j (Finset.mem_filter.mp hj).2)
    simpa only [m, piOccurrences, hflatEq, hglobal] using hm

/-- A single flat π contribution must be supplemented by a genuine block
occurrence, on the same actual global edge and the same angle field. -/
theorem genuine_of_single_pi (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell) (e : p.GlobalEdge)
    (hm : m p ell (flats p ell) e = 1) :
    ∃ i : T × Fin 6, label p i = e ∧ ¬ Flat p ell i.1 := by
  classical
  by_contra h
  push_neg at h
  have hall : ∀ i ∈ fiber p e, Flat p ell i.1 := fun i hi => h i (Finset.mem_filter.mp hi).2
  have hsum' : ∑ i ∈ fiber p e, angle p ell i =
      ∑ i ∈ piOccurrences p ell (flats p ell) e, angle p ell i := by
    rw [piOccurrences, Finset.sum_filter, flatOccurrences, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have hiF : i.1 ∈ flats p ell := by simpa [flats] using hall i hi
    simp only [hiF, if_true]
    by_cases ha : angle p ell i = Real.pi
    · simp [ha]
    · obtain ⟨k,hk⟩ := hall i hi
      have hp := ((positive_classification (coordinates p ell i.1)
        (coordinates_positive p ell hell i.1)).2.2 k).2.mp hk i.2
      change angle p ell i = _ at hp
      split_ifs at hp with hh
      · exact (ha hp).elim
      · simp [ha, hp]
  rw [pi_sum, hm, hsum e] at hsum'
  norm_num at hsum'

/-- Each actual flat face component has a globally single π label exposed
in at most two local occurrences of that component. -/
theorem component_exposed_label (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell)
    (hdegree : ∀ e, 6 ≤ degree p e) (t : T) (ht : Flat p ell t) :
    ∃ e : p.GlobalEdge, m p ell (flats p ell) e = 1 ∧
      m p ell (component p ell t) e = 1 ∧ n p ell (component p ell t) e ≤ 2 ∧
      ∃ i : T × Fin 6, label p i = e ∧ ¬ Flat p ell i.1 := by
  classical
  let C := component p ell t
  have hCsub : C ⊆ flats p ell := component_subset p ell t
  have hCflat : ∀ u ∈ C, Flat p ell u := by
    intro u hu
    simpa [flats] using hCsub hu
  have hCne : C.Nonempty := component_nonempty p ell t ht
  have hbudget := (native_component_budget p ell hell C hCflat hCne).2
  have hsumpos : 0 < ∑ e : p.GlobalEdge,
      (3*(m p ell C e : ℝ)-(n p ell C e : ℝ))*weight p ell e := by
    have hlog : 0 < Real.log (16:ℝ) := Real.log_pos (by norm_num)
    have hcard : 0 < (C.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hCne
    exact lt_trans (mul_pos hcard hlog) hbudget
  have hsumpos' : (∑ _e : p.GlobalEdge, (0:ℝ)) < ∑ e : p.GlobalEdge,
      (3*(m p ell C e : ℝ)-(n p ell C e : ℝ))*weight p ell e := by simpa using hsumpos
  obtain ⟨e, he, hterm⟩ := Finset.exists_lt_of_sum_lt hsumpos'
  have hw : 0 < weight p ell e := Real.log_pos (Real.one_lt_cosh.mpr (ne_of_gt (hell e)))
  have hcoeff : 0 < 3*(m p ell C e : ℝ)-(n p ell C e : ℝ) := by
    by_contra h
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hw.le
    linarith
  have hmlocal := m_mono p ell C (flats p ell) hCsub e
  have hmglobal := m_le_two p ell hsum (flats p ell) e
  have hmpos : 0 < m p ell C e := by
    by_contra hh
    have hzero : m p ell C e = 0 := by omega
    rw [hzero] at hcoeff
    have hnon : (0:ℝ) ≤ (n p ell C e : ℝ) := Nat.cast_nonneg _
    norm_num only [Nat.cast_zero, mul_zero, zero_sub, neg_pos] at hcoeff
    linarith
  have hmnot : m p ell (flats p ell) e ≠ 2 := by
    intro hh
    obtain ⟨hn,hmC⟩ := saturation_localizes p ell hell hsum t e hh hmpos
    change m p ell C e = 2 at hmC
    change n p ell C e = degree p e at hn
    rw [hmC,hn] at hcoeff
    have hd : (6:ℝ) ≤ degree p e := by exact_mod_cast hdegree e
    norm_num at hcoeff
    have hdeg := hdegree e
    omega
  have hmG : m p ell (flats p ell) e = 1 := by omega
  have hmC : m p ell C e = 1 := by omega
  have hn : n p ell C e ≤ 2 := by
    rw [hmC] at hcoeff
    norm_num only [Nat.cast_one] at hcoeff
    have hh : (n p ell C e : ℝ) < 3 := by linarith
    have hh' : n p ell C e < 3 := by exact_mod_cast hh
    omega
  exact ⟨e,hmG,hmC,hn,genuine_of_single_pi p ell hell hsum e hmG⟩

private theorem sum_m (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (C : Finset T) (hC : ∀ t ∈ C, Flat p ell t) :
    ∑ e : p.GlobalEdge, m p ell C e = 2*C.card := by
  classical
  have hblock : ∀ t ∈ C, (∑ q : Fin 6,
      if angle p ell (t,q) = Real.pi then (1:ℝ) else 0) = 2 := by
    intro t ht
    obtain ⟨k,hk⟩ := hC t ht
    have hp := ((positive_classification (coordinates p ell t)
      (coordinates_positive p ell hell t)).2.2 k).2.mp hk
    have hp' : ∀ q, angle p ell (t,q) =
        if q = k.castAdd 3 ∨ q = k.natAdd 3 then Real.pi else 0 := hp
    simp only [hp']
    fin_cases k <;>
      simp only [Fin.castAdd, Fin.natAdd, Fin.addNat, Fin.sum_univ_succ,
        Finset.sum_empty, Fin.reduceFinMk, Fin.isValue] <;>
      norm_num [Real.pi_ne_zero.symm, Fin.ext_iff]
  have hh := regroup_m p ell C (fun _ => (1:ℝ))
  simp only [mul_one] at hh
  have heq : (∑ e : p.GlobalEdge, (m p ell C e : ℝ)) = (2:ℝ)*C.card := by
    rw [hh]
    calc
      _ = ∑ _t ∈ C, (2:ℝ) := Finset.sum_congr rfl hblock
      _ = _ := by simp [nsmul_eq_mul]; ring
  exact_mod_cast heq

def Endpoint (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (C : Finset T) (e : p.GlobalEdge) : Prop :=
  (∃ i : T × Fin 6, i.1 ∈ C ∧ label p i = e ∧ angle p ell i = Real.pi) ∧
    m p ell (flats p ell) e = 1 ∧
    ∃ j : T × Fin 6, label p j = e ∧ ¬ Flat p ell j.1

/-- Two distinct globally single flat π labels occur in every actual flat
face component, and each has an actual genuine-block occurrence. -/
theorem component_endpoints (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (hell : ∀ e, 0 < ell e) (hsum : AngleSums p ell)
    (hdegree : ∀ e, 6 ≤ degree p e) (t : T) (ht : Flat p ell t) :
    ∃ e₀ e₁ : p.GlobalEdge, e₀ ≠ e₁ ∧
      Endpoint p ell (component p ell t) e₀ ∧ Endpoint p ell (component p ell t) e₁ := by
  classical
  let C := component p ell t
  let A : Finset p.GlobalEdge := Finset.univ.filter (fun e => m p ell C e = 1)
  let B : Finset p.GlobalEdge := Finset.univ.filter (fun e => m p ell C e = 2)
  have hCflat : ∀ u ∈ C, Flat p ell u := by
    intro u hu
    simpa [flats] using component_subset p ell t hu
  have hcount := sum_m p ell hell C hCflat
  have hsplit : ∑ e : p.GlobalEdge, m p ell C e = A.card+2*B.card := by
    have hterm : ∀ e, m p ell C e =
        (if m p ell C e = 1 then 1 else 0)+2*(if m p ell C e = 2 then 1 else 0) := by
      intro e
      have hh := m_le_two p ell hsum C e
      split_ifs <;> omega
    calc
      _ = ∑ e : p.GlobalEdge,
          ((if m p ell C e = 1 then 1 else 0)+2*(if m p ell C e = 2 then 1 else 0)) :=
        Finset.sum_congr rfl (fun e _ => hterm e)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [A, B]
  have hAne : A.Nonempty := by
    obtain ⟨e,hmG,hmC,_,_⟩ := component_exposed_label p ell hell hsum hdegree t ht
    exact ⟨e, by simp [A, hmC, C]⟩
  have hcard : 1 < A.card := by
    have hh := Finset.card_pos.mpr hAne
    omega
  obtain ⟨e₀,he₀,e₁,he₁,hne⟩ := Finset.one_lt_card.mp hcard
  have hend : ∀ e ∈ A, Endpoint p ell C e := by
    intro e he
    have hmC : m p ell C e = 1 := (Finset.mem_filter.mp he).2
    have hmle := m_mono p ell C (flats p ell) (component_subset p ell t) e
    have hm2 := m_le_two p ell hsum (flats p ell) e
    have hn2 : m p ell (flats p ell) e ≠ 2 := by
      intro h2
      have hpos : 0 < m p ell (component p ell t) e := by
        change 0 < m p ell C e
        omega
      have hh := (saturation_localizes p ell hell hsum t e h2 hpos).2
      change m p ell C e = 2 at hh
      omega
    have hmG : m p ell (flats p ell) e = 1 := by omega
    have hpos : 0 < (piOccurrences p ell C e).card := by change 0 < m p ell C e; omega
    obtain ⟨i,hi⟩ := Finset.card_pos.mp hpos
    have ha := (Finset.mem_filter.mp hi).2
    obtain ⟨hf,hCi⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hi).1
    have hie := (Finset.mem_filter.mp hf).2
    exact ⟨⟨i,hCi,hie,ha⟩,hmG,genuine_of_single_pi p ell hell hsum e hmG⟩
  exact ⟨e₀,e₁,hne,hend e₀ he₀,hend e₁ he₁⟩

#print axioms saturated_support
#print axioms native_component_budget
#print axioms genuine_of_single_pi
#print axioms component_exposed_label
#print axioms component_endpoints

end D5.S3.Geometry.Hyperideal.FlatComponentBudget
