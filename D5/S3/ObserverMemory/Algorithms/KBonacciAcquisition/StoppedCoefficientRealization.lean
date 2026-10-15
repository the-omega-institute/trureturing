/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/StoppedCoefficientRealization
   mirror-E: none(waiver:symbolic-probability-construction)
   anchors: []
   utility: none
   digest: Stopped kernels have a common catalog law exactly at the vector and mass budget. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledRealization
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization

/-- Ordered query pairs. Natural address i denotes original prime index i+1. -/
abbrev Pair (L : ℕ) := {a : Fin L × Fin L // a.1 < a.2}
/-- Coordinate mass sums output labels, including label zero. -/
def mass {J : Type*} [Fintype J] (u : J → ℝ) : ℝ := ∑ r, u r
/-- The degree-at-most-two expansion is required at every Boolean word. -/
def polynomial {L : ℕ} {J : Type*} (c : J → ℝ) (ell : Fin L → J → ℝ)
    (Q : Pair L → J → ℝ) (b : Fin L → Bool) (r : J) : ℝ :=
  c r + (∑ i, if b i then ell i r else 0) +
    ∑ a, if b a.val.1 && b a.val.2 then Q a r else 0
/-- The negative pair demand aggregated by the first query address. -/
def outgoing {L : ℕ} {J : Type*} (Q : Pair L → J → ℝ) (i : Fin L) (r : J) : ℝ :=
  ∑ a : Pair L, if a.val.1 = i then max (-Q a r) 0 else 0
/-- The first-zero demand at each query address. -/
def rowDemand {L : ℕ} {J : Type*} (ell : Fin L → J → ℝ)
    (Q : Pair L → J → ℝ) (i : Fin L) (r : J) : ℝ := max (outgoing Q i r - ell i r) 0
/-- Total coordinatewise demand H. -/
def totalDemand {L : ℕ} {J : Type*} (ell : Fin L → J → ℝ)
    (Q : Pair L → J → ℝ) (r : J) : ℝ := ∑ i, rowDemand ell Q i r
/-- One scalar budget beta; the inner masses sum labels, the outer sum addresses. -/
def budget {L : ℕ} {J : Type*} [Fintype J] (ell : Fin L → J → ℝ)
    (Q : Pair L → J → ℝ) : ℝ :=
  ∑ i, max (mass (outgoing Q i)) (mass (rowDemand ell Q i))
/-- One common law on the existing complete stopped catalog. -/
def Realizes (L : ℕ) (p : (Fin L → Bool) → Fin (L + 1) → ℝ) : Prop :=
  ∃ w : PMF (Catalog true L), ∀ b r, (w.map (fun f => f.val b) r).toReal = p b r

private def singleWord {L : ℕ} (i : Fin L) : Fin L → Bool := fun k => decide (k = i)
private def doubleWord {L : ℕ} (a : Pair L) : Fin L → Bool :=
  fun k => decide (k = a.val.1 ∨ k = a.val.2)

private theorem pair_distinct {L : ℕ} (a : Pair L) : a.val.1 ≠ a.val.2 := ne_of_lt a.property

private theorem polynomial_zero {L : ℕ} {J : Type*} (c : J → ℝ)
    (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ) (r : J) :
    polynomial c ell Q (fun _ => false) r = c r := by simp [polynomial]

private theorem polynomial_single {L : ℕ} {J : Type*} (c : J → ℝ)
    (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ) (i : Fin L) (r : J) :
    polynomial c ell Q (singleWord i) r = c r + ell i r := by
  classical
  have hp : ∀ a : Pair L, ¬(a.val.1 = i ∧ a.val.2 = i) := by
    intro a h; exact pair_distinct a (h.1.trans h.2.symm)
  simp [polynomial, singleWord, hp]

private theorem pair_in_double {L : ℕ} (a d : Pair L) :
    ((d.val.1 = a.val.1 ∨ d.val.1 = a.val.2) ∧
      (d.val.2 = a.val.1 ∨ d.val.2 = a.val.2)) ↔ d = a := by
  constructor
  · rintro ⟨h₁,h₂⟩
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact False.elim (pair_distinct d (h₁.trans h₂.symm))
    · apply Subtype.ext; exact Prod.ext h₁ h₂
    · have hd := d.property; have ha := a.property; rw [h₁,h₂] at hd; exact False.elim (lt_asymm ha hd)
    · exact False.elim (pair_distinct d (h₁.trans h₂.symm))
  · rintro rfl; simp

private theorem polynomial_double {L : ℕ} {J : Type*} (c : J → ℝ)
    (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ) (a : Pair L) (r : J) :
    polynomial c ell Q (doubleWord a) r = c r + ell a.val.1 r + ell a.val.2 r + Q a r := by
  classical
  have hl : (∑ i : Fin L, if i = a.val.1 ∨ i = a.val.2 then ell i r else 0) =
      ell a.val.1 r + ell a.val.2 r := by
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun i : Fin L => i = a.val.1 ∨ i = a.val.2) =
        {a.val.1,a.val.2} := by ext i; simp
    rw [hf, Finset.sum_pair (pair_distinct a)]
  have hq : (∑ d : Pair L, if
      (d.val.1 = a.val.1 ∨ d.val.1 = a.val.2) ∧
      (d.val.2 = a.val.1 ∨ d.val.2 = a.val.2) then Q d r else 0) = Q a r := by
    simp_rw [pair_in_double]; simp
  simpa [polynomial, doubleWord, hl, hq, add_assoc] using congrArg
    (fun z => c r + (ell a.val.1 r + ell a.val.2 r) + z) hq

private theorem normalized {L : ℕ} {J : Type*} [Fintype J]
    (p : (Fin L → Bool) → J → ℝ) (c : J → ℝ) (ell : Fin L → J → ℝ)
    (Q : Pair L → J → ℝ) (hp : ∀ b, mass (p b) = 1)
    (hexp : ∀ b r, p b r = polynomial c ell Q b r) :
    mass c = 1 ∧ (∀ i, mass (ell i) = 0) ∧ (∀ a, mass (Q a) = 0) := by
  have hc : mass c = 1 := by
    simpa [mass, hexp, polynomial_zero] using hp (fun _ => false)
  have hl (i) : mass (ell i) = 0 := by
    have h := hp (singleWord i)
    simp_rw [mass, hexp, polynomial_single, Finset.sum_add_distrib] at h
    change mass c + mass (ell i) = 1 at h
    linarith
  refine ⟨hc,hl,?_⟩
  intro a
  have h := hp (doubleWord a)
  simp_rw [mass, hexp, polynomial_double, Finset.sum_add_distrib] at h
  change mass c + mass (ell a.val.1) + mass (ell a.val.2) + mass (Q a) = 1 at h
  rw [hc,hl,hl] at h; linarith

private theorem mass_nonneg {J : Type*} [Fintype J] (u : J → ℝ) (h : ∀ r, 0 ≤ u r) :
    0 ≤ mass u := Finset.sum_nonneg (fun r _ => h r)

private theorem mass_zero {J : Type*} [Fintype J] (u : J → ℝ) (h : ∀ r, 0 ≤ u r)
    (hm : mass u = 0) : ∀ r, u r = 0 := by
  intro r
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => h r)).mp hm r (Finset.mem_univ r)

private theorem demand_normalization {L : ℕ} {J : Type*} [Fintype J]
    (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    (hl : ∀ i, mass (ell i) = 0) :
    (∀ i, mass (outgoing Q i) ≤ mass (rowDemand ell Q i)) ∧
    budget ell Q = mass (totalDemand ell Q) := by
  have h (i) : mass (outgoing Q i) ≤ mass (rowDemand ell Q i) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ => le_max_left
      (outgoing Q i r - ell i r) 0)
    change (∑ r, (outgoing Q i r - ell i r)) ≤ mass (rowDemand ell Q i) at hs
    rw [Finset.sum_sub_distrib] at hs
    change mass (outgoing Q i) - mass (ell i) ≤ mass (rowDemand ell Q i) at hs
    simpa [hl] using hs
  refine ⟨h,?_⟩
  simp_rw [budget, max_eq_right (h _)]
  exact Finset.sum_comm


abbrev Schedule (L : ℕ) := Unit ⊕ (Fin L ⊕ Pair L)
abbrev Labels (J : Type*) := J × J × J
def label {J : Type*} (t : Labels J) (k : Fin 3) : J :=
  if k = 0 then t.1 else if k = 1 then t.2.1 else t.2.2
def cell {L : ℕ} : Schedule L → (Fin L → Bool) → Fin 3
  | .inl _, _ => 0
  | .inr (.inl i), b => if b i then 1 else 0
  | .inr (.inr a), b => if b a.val.1 then (if b a.val.2 then 2 else 1) else 0
private def addresses {L : ℕ} : Schedule L → List ℕ
  | .inl _ => []
  | .inr (.inl i) => [i.val]
  | .inr (.inr a) => [a.val.1.val, a.val.2.val]
def table {L : ℕ} (s : Schedule L) (t : Labels (Fin (L + 1))) : Catalog true L :=
  ⟨fun b => label t (cell s b), by
    refine ⟨addresses s, ?_, ?_, ?_, ?_⟩
    · cases s with
      | inl => simp [addresses]
      | inr s => cases s <;> simp [addresses]
    · intro i hi
      cases s with
      | inl => simp [addresses] at hi
      | inr s =>
        cases s with
        | inl k =>
            simp [addresses] at hi
            subst i
            exact k.isLt
        | inr a =>
          simp [addresses] at hi
          rcases hi with rfl | rfl
          · exact a.val.1.isLt
          · exact a.val.2.isLt
    · intro _
      cases s with
      | inl => simp [addresses]
      | inr s =>
        cases s with
        | inl => simp [addresses]
        | inr a => simpa [addresses] using a.property
    · intro b c h
      apply congrArg (label t)
      cases s with
      | inl => rfl
      | inr s =>
        cases s with
        | inl i =>
          have he : b i = c i := by simpa [addresses, view, lowReply] using h
          simp [cell,he]
        | inr a =>
          have hh : b a.val.1 :: (if !b a.val.1 then [] else [b a.val.2]) =
              c a.val.1 :: (if !c a.val.1 then [] else [c a.val.2]) := by
            simpa [addresses,view,lowReply] using h
          have hfirst := (List.cons.inj hh).1
          cases h₁ : b a.val.1
          · simp [cell,h₁,← hfirst]
          · have hsecond : b a.val.2 = c a.val.2 := by
              simpa [h₁,← hfirst] using (List.cons.inj hh).2
            simp [cell,h₁,← hfirst,hsecond]⟩

private theorem represented {L : ℕ} (f : Catalog true L) :
    ∃ s t, table s t = f := by
  classical
  obtain ⟨xs,hbudget,hlow,hincr,hcell⟩ := f.property
  cases xs with
  | nil =>
      refine ⟨Sum.inl (), (f.val (fun _ => false), f.val (fun _ => false),
        f.val (fun _ => false)), ?_⟩
      apply Subtype.ext; funext b
      exact (hcell b (fun _ => false) rfl).symm
  | cons i xs =>
      have hi : i < L := hlow i (by simp)
      let ii : Fin L := ⟨i,hi⟩
      cases xs with
      | nil =>
          refine ⟨Sum.inr (Sum.inl ii), (f.val (fun _ => false), f.val (singleWord ii),
            f.val (singleWord ii)), ?_⟩
          apply Subtype.ext; funext b
          change label _ (cell _ b) = f.val b
          cases hb : b ii
          · simp only [cell,hb,Bool.false_eq_true,if_false,label,ite_true]
            exact (hcell b (fun _ => false) (by simp [view,lowReply,hi,ii,← hb])).symm
          · simp only [cell,hb,if_true,label]
            exact (hcell b (singleWord ii) (by simp [view,lowReply,hi,singleWord,ii,hb])).symm
      | cons j xs =>
          have hj : j < L := hlow j (by simp)
          have hij : i < j := by simpa using (List.pairwise_cons.mp (hincr rfl)).1 j (by simp)
          cases xs with
          | cons k xs => simp at hbudget
          | nil =>
              let a : Pair L := ⟨(ii,⟨j,hj⟩),hij⟩
              refine ⟨Sum.inr (Sum.inr a), (f.val (fun _ => false),
                f.val (singleWord ii), f.val (doubleWord a)), ?_⟩
              apply Subtype.ext; funext b
              change label _ (cell _ b) = f.val b
              cases hb : b ii
              · simp only [cell,show a.val.1 = ii from rfl,hb,Bool.false_eq_true,if_false,label,ite_true]
                exact (hcell b (fun _ => false) (by simp [view,lowReply,hi,ii,← hb])).symm
              · cases hc : b ⟨j,hj⟩
                · simp [cell,label,a,hb,hc]
                  exact (hcell b (singleWord ii) (by
                    simp [view,lowReply,hi,hj,singleWord,hb,hc,ii,Ne.symm (ne_of_lt hij)])).symm
                · simp [cell,label,a,hb,hc]
                  exact (hcell b (doubleWord a) (by
                    simp [view,lowReply,hi,hj,doubleWord,hb,hc,a,ii])).symm

private def terminalLaw {L : ℕ} {J : Type*}
    (u : Schedule L → Fin 3 → J → ℝ) (b : Fin L → Bool) (r : J) : ℝ :=
  ∑ s, u s (cell s b) r

private theorem pmf_real_sum {A : Type*} [Fintype A] (w : PMF A) :
    ∑ a, (w a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => w.apply_ne_top a)]
  have hs : (∑ a, w a) = 1 := (tsum_fintype _).symm.trans w.tsum_coe
  rw [hs]; norm_num

open scoped Classical in
private theorem real_map {A B : Type*} [Fintype A] (w : PMF A) (f : A → B) (b : B) :
    (w.map f b).toReal = ∑ a, if f a = b then (w a).toReal else 0 := by
  classical
  rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _; by_cases h : f a = b
    · simp [h]
    · simp [h,Ne.symm h]
  · intro a _; split_ifs <;> simp [w.apply_ne_top]

/-- Three draws assemble all cells of one table before any query. -/
private def joint {J : Type*} (p₀ p₁ p₂ : PMF J) : PMF (Labels J) :=
  p₀.bind fun a => p₁.bind fun b => p₂.map fun c => (a,b,c)

private theorem joint_marginal {J : Type*} (p₀ p₁ p₂ : PMF J) (k : Fin 3) :
    (joint p₀ p₁ p₂).map (fun t => label t k) =
      if k = 0 then p₀ else if k = 1 then p₁ else p₂ := by
  fin_cases k <;> simp [joint,label,PMF.map,Function.comp_def]

private theorem common_table_coupling {L : ℕ}
    (u : Schedule L → Fin 3 → Fin (L + 1) → ℝ)
    (hn : ∀ s k r, 0 ≤ u s k r) (hm : ∀ s k, mass (u s k) = mass (u s 0))
    (ht : ∑ s, mass (u s 0) = 1) :
    Realizes L (terminalLaw u) := by
  classical
  let w : Schedule L → ℝ := fun s => mass (u s 0)
  have hw (s) : 0 ≤ w s := mass_nonneg _ (hn s 0)
  let schedulePMF : PMF (Schedule L) := PMF.ofFintype (fun s => ENNReal.ofReal (w s))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hw s)]; simpa [w] using congrArg ENNReal.ofReal ht)
  let v : Schedule L → Fin 3 → PMF (Fin (L + 1)) := fun s k =>
    if h : w s = 0 then PMF.pure 0 else PMF.ofFintype
      (fun r => ENNReal.ofReal (u s k r / w s)) (by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => div_nonneg (hn s k r) (hw s)),
          ← Finset.sum_div]
        change ENNReal.ofReal (mass (u s k) / w s) = 1
        rw [hm,show mass (u s 0) = w s from rfl,div_self h]; simp)
  let z : PMF (Catalog true L) := schedulePMF.bind fun s =>
    (joint (v s 0) (v s 1) (v s 2)).map (table s)
  refine ⟨z,?_⟩
  intro b r
  have marg (s) : ((joint (v s 0) (v s 1) (v s 2)).map
      (fun t => (table s t).val b)) = v s (cell s b) := by
    change (joint _ _ _).map (fun t => label t (cell s b)) = _
    rw [joint_marginal]; generalize cell s b = k
    fin_cases k <;> simp
  have law : (z.map (fun f => f.val b)) r = ∑ s,
      ENNReal.ofReal (u s (cell s b) r) := by
    simp only [z,PMF.map_bind,PMF.map_comp,Function.comp_def,marg,PMF.bind_apply,
      tsum_fintype]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : w s = 0
    · have hu : u s (cell s b) r = 0 := mass_zero _ (hn s _) (by rw [hm]; exact h) r
      simp [schedulePMF,PMF.ofFintype_apply,h,hu]
    · have hv : 0 < w s := lt_of_le_of_ne (hw s) (Ne.symm h)
      simp only [schedulePMF,PMF.ofFintype_apply,v,dif_neg h]
      rw [← ENNReal.ofReal_mul (hw s)]
      congr 1; field_simp
  rw [law, ← ENNReal.ofReal_sum_of_nonneg (fun s _ => hn s _ r), ENNReal.toReal_ofReal
    (Finset.sum_nonneg (fun s _ => hn s _ r))]
  rfl

private def representative {L : ℕ} (f : Catalog true L) :
    Schedule L × Labels (Fin (L + 1)) :=
  ((represented f).choose, (represented f).choose_spec.choose)
private theorem representative_eq {L : ℕ} (f : Catalog true L) :
    table (representative f).1 (representative f).2 = f := (represented f).choose_spec.choose_spec

private theorem catalog_terminal_vectors {L : ℕ} (p : (Fin L → Bool) → Fin (L + 1) → ℝ)
    (hp : Realizes L p) :
    ∃ u : Schedule L → Fin 3 → Fin (L + 1) → ℝ,
      (∀ s k r, 0 ≤ u s k r) ∧
      (∀ s k, mass (u s k) = mass (u s 0)) ∧
      (∑ s, mass (u s 0) = 1) ∧ ∀ b r, p b r = terminalLaw u b r := by
  classical
  obtain ⟨w,hw⟩ := hp
  let u := fun s k r => ∑ f : Catalog true L,
    if (representative f).1 = s then
      if label (representative f).2 k = r then (w f).toReal else 0 else 0
  have nonneg : ∀ s k r, 0 ≤ u s k r := by
    intro s k r; apply Finset.sum_nonneg; intro f _
    split_ifs <;> positivity
  have mass_eq (s k) : mass (u s k) = ∑ f : Catalog true L,
      if (representative f).1 = s then (w f).toReal else 0 := by
    dsimp [mass,u]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    by_cases h : (representative f).1 = s <;> simp [h]
  refine ⟨u,nonneg,(fun s k => (mass_eq s k).trans (mass_eq s 0).symm),?_,?_⟩
  · simp_rw [mass_eq]
    rw [Finset.sum_comm]
    simpa using pmf_real_sum w
  · intro b r
    rw [← hw,real_map]
    dsimp [terminalLaw,u]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    have eq : label (representative f).2 (cell (representative f).1 b) = f.val b :=
      congrArg (fun g : Catalog true L => g.val b) (representative_eq f)
    simp [eq]

private def firstRow {L : ℕ} {J : Type*} (u : Schedule L → Fin 3 → J → ℝ)
    (k : Fin 3) (i : Fin L) (r : J) : ℝ :=
  u (.inr (.inl i)) k r + ∑ a : Pair L, if a.val.1 = i then u (.inr (.inr a)) k r else 0

private theorem sum_rows {L : ℕ} (g : Pair L → ℝ) :
    (∑ i : Fin L, ∑ a : Pair L, if a.val.1 = i then g a else 0) = ∑ a, g a := by
  classical
  rw [Finset.sum_comm]; simp
private theorem sum_rows_bit {L : ℕ} (g : Pair L → ℝ) (b : Fin L → Bool) :
    (∑ i : Fin L, if b i then (∑ a : Pair L, if a.val.1 = i then g a else 0) else 0) =
      ∑ a, if b a.val.1 then g a else 0 := by
  classical
  calc
    _ = ∑ i : Fin L, ∑ a : Pair L, if a.val.1 = i then
        (if b a.val.1 then g a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hb : b i
      · simp only [hb,Bool.false_eq_true,if_false]
        symm; apply Finset.sum_eq_zero
        intro a _; by_cases ha : a.val.1 = i <;> simp [ha,hb]
      · simp only [hb,if_true]
        apply Finset.sum_congr rfl
        intro a _; by_cases ha : a.val.1 = i <;> simp [ha,hb]
    _ = _ := sum_rows _

private theorem terminal_expansion {L : ℕ} {J : Type*}
    (u : Schedule L → Fin 3 → J → ℝ) (b : Fin L → Bool) (r : J) :
    terminalLaw u b r = polynomial
      (fun r => u (.inl ()) 0 r + ∑ i, firstRow u 0 i r)
      (fun i r => firstRow u 1 i r - firstRow u 0 i r)
      (fun a r => u (.inr (.inr a)) 2 r - u (.inr (.inr a)) 1 r) b r := by
  classical
  have one (i : Fin L) :
      u (.inr (.inl i)) (cell (.inr (.inl i)) b) r =
      u (.inr (.inl i)) 0 r +
        (if b i then u (.inr (.inl i)) 1 r - u (.inr (.inl i)) 0 r else 0) := by
    cases hb : b i <;> simp [cell,hb]
  have two (a : Pair L) :
      u (.inr (.inr a)) (cell (.inr (.inr a)) b) r =
      u (.inr (.inr a)) 0 r +
      (if b a.val.1 then u (.inr (.inr a)) 1 r - u (.inr (.inr a)) 0 r else 0) +
      (if b a.val.1 && b a.val.2 then
        u (.inr (.inr a)) 2 r - u (.inr (.inr a)) 1 r else 0) := by
    cases hb : b a.val.1 <;> cases hc : b a.val.2 <;> simp [cell,hb,hc]
  simp only [terminalLaw,Fintype.sum_sum_type,Fintype.sum_unique]
  change u (.inl ()) 0 r + ((∑ i, u (.inr (.inl i)) (cell (.inr (.inl i)) b) r) +
    ∑ a, u (.inr (.inr a)) (cell (.inr (.inr a)) b) r) = _
  simp_rw [one,two,Finset.sum_add_distrib]
  simp only [polynomial,firstRow]
  rw [Finset.sum_add_distrib, sum_rows]
  have split (i : Fin L) :
      (if b i then
        u (.inr (.inl i)) 1 r + (∑ a, if a.val.1 = i then u (.inr (.inr a)) 1 r else 0) -
        (u (.inr (.inl i)) 0 r + ∑ a, if a.val.1 = i then u (.inr (.inr a)) 0 r else 0)
        else 0) =
      (if b i then u (.inr (.inl i)) 1 r - u (.inr (.inl i)) 0 r else 0) +
      (if b i then (∑ a, if a.val.1 = i then
        u (.inr (.inr a)) 1 r - u (.inr (.inr a)) 0 r else 0) else 0) := by
    have hs : (∑ a : Pair L, if a.val.1 = i then
        u (.inr (.inr a)) 1 r - u (.inr (.inr a)) 0 r else 0) =
        (∑ a : Pair L, if a.val.1 = i then u (.inr (.inr a)) 1 r else 0) -
        ∑ a : Pair L, if a.val.1 = i then u (.inr (.inr a)) 0 r else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _; by_cases h : a.val.1 = i <;> simp [h]
    rw [hs]
    cases hb : b i <;> simp [hb] <;> ring
  simp_rw [split,Finset.sum_add_distrib]
  rw [sum_rows_bit]
  ring

private theorem coefficient_unique {L : ℕ} {J : Type*}
    (c d : J → ℝ) (ell k : Fin L → J → ℝ) (Q R : Pair L → J → ℝ)
    (h : ∀ b r, polynomial c ell Q b r = polynomial d k R b r) :
    c = d ∧ ell = k ∧ Q = R := by
  have hc (r) : c r = d r := by simpa [polynomial_zero] using h (fun _ => false) r
  have hl (i r) : ell i r = k i r := by
    have hh := h (singleWord i) r
    rw [polynomial_single,polynomial_single,hc] at hh; linarith
  refine ⟨funext hc,funext (fun i => funext (hl i)),funext (fun a => funext (fun r => ?_))⟩
  have hh := h (doubleWord a) r
  rw [polynomial_double,polynomial_double,hc,hl,hl] at hh; linarith

private theorem row_mass {L : ℕ} {J : Type*} [Fintype J]
    (u : Schedule L → Fin 3 → J → ℝ) (k : Fin 3) (i : Fin L) :
    mass (firstRow u k i) = mass (u (.inr (.inl i)) k) +
      ∑ a : Pair L, if a.val.1 = i then mass (u (.inr (.inr a)) k) else 0 := by
  simp only [mass,firstRow,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _; by_cases h : a.val.1 = i <;> simp [h]

private theorem all_row_mass {L : ℕ} {J : Type*} [Fintype J]
    (u : Schedule L → Fin 3 → J → ℝ) (k : Fin 3) :
    (∑ i, mass (firstRow u k i)) =
      (∑ i, mass (u (.inr (.inl i)) k)) + ∑ a, mass (u (.inr (.inr a)) k) := by
  simp_rw [row_mass]
  rw [Finset.sum_add_distrib,sum_rows]

private theorem terminal_necessity {L : ℕ} {J : Type*} [Fintype J]
    (c : J → ℝ) (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    (u : Schedule L → Fin 3 → J → ℝ)
    (hn : ∀ s k r, 0 ≤ u s k r)
    (hm : ∀ s k, mass (u s k) = mass (u s 0))
    (ht : ∑ s, mass (u s 0) = 1)
    (heq : ∀ b r, polynomial c ell Q b r = terminalLaw u b r) :
    (∀ r, totalDemand ell Q r ≤ c r) ∧ budget ell Q ≤ 1 := by
  classical
  obtain ⟨hc,hl,hq⟩ := coefficient_unique _ _ _ _ _ _
    (fun b r => (heq b r).trans (terminal_expansion u b r))
  have hnrow (k i r) : 0 ≤ firstRow u k i r := add_nonneg (hn _ _ _)
    (Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [hn]))
  have hv (a r) : max (-Q a r) 0 ≤ u (.inr (.inr a)) 1 r := by
    rw [hq]; dsimp
    exact max_le (by linarith [hn (.inr (.inr a)) 2 r]) (hn _ _ _)
  have hV (i r) : outgoing Q i r ≤ firstRow u 1 i r := by
    have hs : outgoing Q i r ≤ ∑ a : Pair L,
        if a.val.1 = i then u (.inr (.inr a)) 1 r else 0 := by
      apply Finset.sum_le_sum; intro a _; split_ifs; exact hv a r; rfl
    exact hs.trans (le_add_of_nonneg_left (hn _ _ _))
  have hA (i r) : rowDemand ell Q i r ≤ firstRow u 0 i r := by
    rw [rowDemand,hl]; dsimp
    exact max_le (by linarith [hV i r]) (hnrow 0 i r)
  have hmass (i) : mass (firstRow u 1 i) = mass (firstRow u 0 i) := by
    rw [row_mass,row_mass,hm]
    congr 1
    apply Finset.sum_congr rfl
    intro a _; by_cases h : a.val.1 = i <;> simp [h,hm]
  have hb (i) : max (mass (outgoing Q i)) (mass (rowDemand ell Q i)) ≤
      mass (firstRow u 0 i) := by
    apply max_le
    · rw [← hmass]; exact Finset.sum_le_sum (fun r _ => hV i r)
    · exact Finset.sum_le_sum (fun r _ => hA i r)
  have total : mass (fun r => u (.inl ()) 0 r) + ∑ i, mass (firstRow u 0 i) = 1 := by
    rw [all_row_mass]
    simpa [Fintype.sum_sum_type,Fintype.sum_unique] using ht
  constructor
  · intro r
    rw [hc]; dsimp
    exact (Finset.sum_le_sum (fun i _ => hA i r)).trans (le_add_of_nonneg_left (hn _ _ _))
  · have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
    have hr := mass_nonneg (fun r => u (.inl ()) 0 r) (hn _ _)
    change budget ell Q ≤ _ at hs
    linarith

private theorem outgoing_nonneg {L : ℕ} {J : Type*} (Q : Pair L → J → ℝ) (i r) :
    0 ≤ outgoing Q i r := by
  apply Finset.sum_nonneg; intro a _; split_ifs
  · exact le_max_right _ _
  · rfl

private theorem zero_row {L : ℕ} {J : Type*} [Fintype J]
    (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    (hl : ∀ i, mass (ell i) = 0) (hq : ∀ a, mass (Q a) = 0)
    (i : Fin L) (hm : mass (rowDemand ell Q i) = 0) :
    (∀ r, rowDemand ell Q i r = 0) ∧ (∀ r, outgoing Q i r = 0) ∧
    (∀ r, ell i r = 0) ∧ (∀ a : Pair L, a.val.1 = i → ∀ r, Q a r = 0) := by
  have hh : ∀ r, rowDemand ell Q i r = 0 := mass_zero _ (fun r => le_max_right _ _) hm
  have hmv : mass (outgoing Q i) = 0 := le_antisymm
    (by simpa [hm] using (demand_normalization ell Q hl).1 i)
    (mass_nonneg _ (outgoing_nonneg Q i))
  have hv := mass_zero _ (outgoing_nonneg Q i) hmv
  have hell : ∀ r, 0 ≤ ell i r := by
    intro r
    have h := le_max_left (outgoing Q i r - ell i r) 0
    change _ ≤ rowDemand ell Q i r at h
    rw [hh r,hv r] at h; linarith
  have he := mass_zero _ hell (hl i)
  refine ⟨hh,hv,he,?_⟩
  intro a ha
  have hnon (r) : 0 ≤ Q a r := by
    have hterm : (if a.val.1 = i then max (-Q a r) 0 else 0) ≤ outgoing Q i r :=
      by
        unfold outgoing
        exact Finset.single_le_sum (f := fun d : Pair L =>
          if d.val.1 = i then max (-Q d r) 0 else 0)
          (fun d _ => by split_ifs; exact le_max_right _ _; rfl) (Finset.mem_univ a)
    rw [if_pos ha,hv] at hterm
    have hneg := le_max_left (-Q a r) 0; linarith
  exact mass_zero _ hnon (hq a)

private def allocation {L : ℕ} {J : Type*} [Fintype J]
    (c : J → ℝ) (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ) :
    Schedule L → Fin 3 → J → ℝ
  | .inl _, _, r => c r - totalDemand ell Q r
  | .inr (.inl i), k, r =>
      if k = 0 then
        (1 - mass (outgoing Q i) / mass (rowDemand ell Q i)) * rowDemand ell Q i r
      else rowDemand ell Q i r + ell i r - outgoing Q i r
  | .inr (.inr a), k, r =>
      if k = 0 then
        (mass (fun r => max (-Q a r) 0) / mass (rowDemand ell Q a.val.1)) *
          rowDemand ell Q a.val.1 r
      else if k = 1 then max (-Q a r) 0 else max (-Q a r) 0 + Q a r

private theorem outgoing_mass {L : ℕ} {J : Type*} [Fintype J]
    (Q : Pair L → J → ℝ) (i : Fin L) :
    mass (outgoing Q i) = ∑ a : Pair L,
      if a.val.1 = i then mass (fun r => max (-Q a r) 0) else 0 := by
  simp only [mass,outgoing]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _; split_ifs <;> simp [*]

private theorem allocation_rows {L : ℕ} {J : Type*} [Fintype J]
    (c : J → ℝ) (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    : (∀ i r, firstRow (allocation c ell Q) 0 i r = rowDemand ell Q i r) ∧
    (∀ i r, firstRow (allocation c ell Q) 1 i r = rowDemand ell Q i r + ell i r) := by
  have h0 (i r) : firstRow (allocation c ell Q) 0 i r = rowDemand ell Q i r := by
    have hs : (∑ a : Pair L, if a.val.1 = i then
        (mass (fun r => max (-Q a r) 0) / mass (rowDemand ell Q a.val.1)) *
          rowDemand ell Q a.val.1 r else 0) =
        (mass (outgoing Q i) / mass (rowDemand ell Q i)) * rowDemand ell Q i r := by
      rw [outgoing_mass]
      rw [Finset.sum_div,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _; split_ifs with ha <;> simp [ha]
    simp only [firstRow,allocation,ite_true,Fin.reduceEq]
    rw [hs]; ring
  refine ⟨h0,?_⟩
  intro i r
  simp [firstRow,allocation,outgoing]

private theorem allocation_masses {L : ℕ} {J : Type*} [Fintype J]
    (c : J → ℝ) (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    (hl : ∀ i, mass (ell i) = 0) (hq : ∀ a, mass (Q a) = 0) :
    (∀ i, mass (allocation c ell Q (.inr (.inl i)) 0) =
      mass (rowDemand ell Q i) - mass (outgoing Q i)) ∧
    (∀ a, mass (allocation c ell Q (.inr (.inr a)) 0) =
      mass (fun r => max (-Q a r) 0)) ∧
    (∀ s k, mass (allocation c ell Q s k) = mass (allocation c ell Q s 0)) := by
  have sing (i) : mass (allocation c ell Q (.inr (.inl i)) 0) =
      mass (rowDemand ell Q i) - mass (outgoing Q i) := by
    simp only [mass,allocation,ite_true]
    rw [← Finset.mul_sum]
    change (1 - mass (outgoing Q i) / mass (rowDemand ell Q i)) *
      mass (rowDemand ell Q i) = mass (rowDemand ell Q i) - mass (outgoing Q i)
    by_cases h : mass (rowDemand ell Q i) = 0
    · have hv := (demand_normalization ell Q hl).1 i
      have hn := mass_nonneg _ (outgoing_nonneg Q i)
      simp [h]; linarith
    · field_simp
  have pair (a) : mass (allocation c ell Q (.inr (.inr a)) 0) =
      mass (fun r => max (-Q a r) 0) := by
    simp only [mass,allocation,ite_true]
    rw [← Finset.mul_sum]
    change (mass (fun r => max (-Q a r) 0) / mass (rowDemand ell Q a.val.1)) *
      mass (rowDemand ell Q a.val.1) = mass (fun r => max (-Q a r) 0)
    by_cases h : mass (rowDemand ell Q a.val.1) = 0
    · have hz := (zero_row ell Q hl hq a.val.1 h).2.2.2 a rfl
      simp [hz,mass]
    · field_simp
  refine ⟨sing,pair,?_⟩
  intro s k
  cases s with
  | inl => rfl
  | inr s =>
      cases s with
      | inl i =>
          rw [sing]
          fin_cases k
          · exact sing i
          · simp [mass,allocation,Finset.sum_sub_distrib,Finset.sum_add_distrib]
            exact hl i
          · simp [mass,allocation,Finset.sum_sub_distrib,Finset.sum_add_distrib]
            exact hl i
      | inr a =>
          rw [pair]
          fin_cases k
          · exact pair a
          · rfl
          · simp [mass,allocation,Finset.sum_add_distrib]
            exact hq a

private theorem allocation_nonnegative {L : ℕ} {J : Type*} [Fintype J]
    (c : J → ℝ) (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    (hl : ∀ i, mass (ell i) = 0) (hc : ∀ r, totalDemand ell Q r ≤ c r) :
    ∀ s k r, 0 ≤ allocation c ell Q s k r := by
  intro s k r
  cases s with
  | inl => exact sub_nonneg.mpr (hc r)
  | inr s =>
      cases s with
      | inl i =>
          dsimp [allocation]
          split_ifs
          · apply mul_nonneg _ (le_max_right _ _)
            by_cases h : mass (rowDemand ell Q i) = 0
            · simp [h]
            · have hp : 0 < mass (rowDemand ell Q i) :=
                lt_of_le_of_ne (mass_nonneg _ (fun r => le_max_right _ _)) (Ne.symm h)
              exact sub_nonneg.mpr ((div_le_one hp).mpr ((demand_normalization ell Q hl).1 i))
          · have h := le_max_left (outgoing Q i r - ell i r) 0
            change _ ≤ rowDemand ell Q i r at h
            linarith
      | inr a =>
          dsimp [allocation]
          split_ifs
          · exact mul_nonneg (div_nonneg (mass_nonneg _ (fun r => le_max_right _ _))
              (mass_nonneg _ (fun r => le_max_right _ _))) (le_max_right _ _)
          · exact le_max_right _ _
          · have h := le_max_left (-Q a r) 0; linarith

private theorem allocation_total {L : ℕ} {J : Type*} [Fintype J]
    (c : J → ℝ) (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    (hc : mass c = 1) (hl : ∀ i, mass (ell i) = 0) (hq : ∀ a, mass (Q a) = 0) :
    (∑ s, mass (allocation c ell Q s 0)) = 1 := by
  have hs := (allocation_masses c ell Q hl hq).1
  have hp := (allocation_masses c ell Q hl hq).2.1
  simp only [Fintype.sum_sum_type,Fintype.sum_unique]
  simp_rw [hs,hp]
  have hV : (∑ i, mass (outgoing Q i)) = ∑ a, mass (fun r => max (-Q a r) 0) := by
    simp_rw [outgoing_mass]; exact sum_rows _
  have hH : mass (totalDemand ell Q) = ∑ i, mass (rowDemand ell Q i) := Finset.sum_comm
  have hr : mass (allocation c ell Q (.inl ()) 0) = mass c - mass (totalDemand ell Q) := by
    simp [mass,allocation,Finset.sum_sub_distrib]
  rw [hr,Finset.sum_sub_distrib,hV,hH,hc]; ring

private theorem allocation_exact {L : ℕ} {J : Type*} [Fintype J]
    (c : J → ℝ) (ell : Fin L → J → ℝ) (Q : Pair L → J → ℝ)
    (b r) : terminalLaw (allocation c ell Q) b r = polynomial c ell Q b r := by
  rw [terminal_expansion]
  have hrows := allocation_rows c ell Q
  have hconstant : (fun r => allocation c ell Q (.inl ()) 0 r +
      ∑ i, firstRow (allocation c ell Q) 0 i r) = c := by
    funext r
    simp [allocation,hrows.1,totalDemand]
  have hlinear : (fun i r => firstRow (allocation c ell Q) 1 i r -
      firstRow (allocation c ell Q) 0 i r) = ell := by
    funext i r; rw [hrows.1,hrows.2]; ring
  have hquadratic : (fun a r => allocation c ell Q (.inr (.inr a)) 2 r -
      allocation c ell Q (.inr (.inr a)) 1 r) = Q := by
    funext a r; simp [allocation]
  rw [hconstant,hlinear,hquadratic]

/-- Original 109.1: one common distribution on complete increasing stopped tables,
with every Boolean word and the original non-strict vector and scalar inequalities. -/
theorem stopped_coefficient_realization_iff (L : ℕ)
    (p : (Fin L → Bool) → PMF (Fin (L + 1)))
    (c : Fin (L + 1) → ℝ) (ell : Fin L → Fin (L + 1) → ℝ)
    (Q : Pair L → Fin (L + 1) → ℝ)
    (expansion : ∀ b r, (p b r).toReal = polynomial c ell Q b r) :
    Realizes L (fun b r => (p b r).toReal) ↔
      (∀ r, totalDemand ell Q r ≤ c r) ∧ budget ell Q ≤ 1 := by
  obtain ⟨hc,hl,hq⟩ := normalized (fun b r => (p b r).toReal) c ell Q
    (fun b => pmf_real_sum (p b)) expansion
  constructor
  · intro realized
    obtain ⟨u,hn,hm,ht,heq⟩ := catalog_terminal_vectors _ realized
    exact terminal_necessity c ell Q u hn hm ht
      (fun b r => (expansion b r).symm.trans (heq b r))
  · rintro ⟨hvec,_⟩
    obtain ⟨w,hw⟩ := common_table_coupling (allocation c ell Q)
      (allocation_nonnegative c ell Q hl hvec)
      (allocation_masses c ell Q hl hq).2.2 (allocation_total c ell Q hc hl hq)
    refine ⟨w,?_⟩
    intro b r
    exact (hw b r).trans ((allocation_exact c ell Q b r).trans (expansion b r).symm)

#print axioms stopped_coefficient_realization_iff

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
