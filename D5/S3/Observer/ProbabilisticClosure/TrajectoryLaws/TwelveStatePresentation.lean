/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStatePresentation
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStatePresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The twelve-state marked parameter has exactly six finite-future equivalence classes. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarAffinityContraction
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalUnifilarQuotient
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Function
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation

/-- False denotes F, true denotes T; the second coordinate is the original index modulo six. -/
abbrev Hidden := Bool × Fin 6
abbrev Label := Bool × Fin 3

def rate (s : Fin 6) : ℝ := if s.val % 3 = 0 then 1/4 else if s.val % 3 = 1 then 1/2 else 3/4

def advance (s : Fin 6) : Fin 6 := ⟨(s.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

def label (i : Hidden) : Label := (i.1, ⟨i.2.val % 3, Nat.mod_lt _ (by decide)⟩)

def mass (i : Hidden) : ℝ := if i.1 then 3/62 else (3/62) / rate i.2

def prob (i : Hidden) (x : Bool) : ℝ :=
  if i.1 then (if x then 0 else 1) else (if x then rate i.2 else 1 - rate i.2)

def next (i : Hidden) (x : Bool) : Hidden := (x, if x then advance i.2 else i.2)

def marked (x : Bool) : Matrix Hidden Hidden ℝ := fun i j =>
  if j = next i x then prob i x else 0

theorem mass_pos (i : Hidden) : 0 < mass i := by
  rcases i with ⟨b,s⟩
  cases b <;> fin_cases s <;> norm_num [mass, rate]

private theorem prob_nonneg (i : Hidden) (x : Bool) : 0 ≤ prob i x := by
  rcases i with ⟨b,s⟩
  cases b <;> cases x <;> fin_cases s <;> norm_num [prob, rate]

private theorem prob_sum (i : Hidden) : prob i false + prob i true = 1 := by
  rcases i with ⟨b,s⟩
  cases b <;> simp [prob]

private theorem marked_nonneg (x : Bool) (i j : Hidden) : 0 ≤ marked x i j := by
  unfold marked
  split_ifs <;> first | exact prob_nonneg i x | exact le_rfl

private theorem marked_row (i : Hidden) (x : Bool) : ∑ j, marked x i j = prob i x := by
  simp [marked]

/-- The exact original twelve-state stationary parameter, without collapsing its two lifts. -/
def parameter : Presentation Hidden where
  initial := mass
  matrix := marked
  initial_nonneg i := (mass_pos i).le
  initial_sum := by
    norm_num [mass, rate, Fintype.sum_prod_type, Fin.sum_univ_succ]
  matrix_nonneg := marked_nonneg
  stochastic i := by
    rw [Finset.sum_add_distrib, marked_row, marked_row, prob_sum]
  stationary j := by
    rcases j with ⟨b,s⟩
    cases b <;> fin_cases s <;>
      norm_num [mass, marked, next, advance, prob, rate, Fintype.sum_prod_type, Fin.sum_univ_succ]
  no11 := by
    have hz : marked true * marked true = 0 := by
      ext i j
      simp only [Matrix.mul_apply, marked, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      simp [next, prob]
    rw [hz]
    simp

theorem unifilar : RowUnifilar marked := by
  intro x i j k hj hk
  have hj' : j = next i x := by
    by_contra h
    simpa [marked,h] using hj
  have hk' : k = next i x := by
    by_contra h
    simpa [marked,h] using hk
  exact hj'.trans hk'.symm

theorem future_rec (i : Hidden) (x : Bool) (n : ℕ) (w : Fin n → Bool) :
    futureMass marked i (n+1) (Fin.cons x w) = prob i x * futureMass marked (next i x) n w := by
  simp only [futureMass, wordMatrix, Fin.cons_zero, Fin.tail_cons, Matrix.mul_apply,
    marked, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.mul_sum]

private theorem label_step (i j : Hidden) (h : label i = label j) (x : Bool) :
    prob i x = prob j x ∧ label (next i x) = label (next j x) := by
  rcases i with ⟨b,s⟩
  rcases j with ⟨d,t⟩
  cases b <;> cases d <;> fin_cases s <;> fin_cases t <;> cases x <;>
    norm_num [label, prob, rate, next, advance] at h <;>
      norm_num [label, prob, rate, next, advance]

theorem future_empty (i : Hidden) (w : Fin 0 → Bool) : futureMass marked i 0 w = 1 := by
  classical
  unfold futureMass
  simp only [wordMatrix, Matrix.one_apply]
  calc
    _ = ∑ j : Hidden, if j = i then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j
      · simp only [if_pos h, if_pos h.symm]
      · simp only [if_neg h, if_neg (Ne.symm h)]
    _ = 1 := by simp

private theorem same_label_future (i j : Hidden) (h : label i = label j) :
    (futureSetoid marked).r i j := by
  change (fun n => futureMass marked i n) = (fun n => futureMass marked j n)
  funext n
  induction n generalizing i j with
  | zero => funext w; rw [future_empty, future_empty]
  | succ n ih =>
    funext w
    rw [← Fin.cons_self_tail w, future_rec, future_rec]
    obtain ⟨hp,hs⟩ := label_step i j h (w 0)
    rw [hp, congrFun (ih (next i (w 0)) (next j (w 0)) hs) (Fin.tail w)]

theorem future_one (i : Hidden) (x : Bool) :
    futureMass marked i 1 (fun _ => x) = prob i x := by
  simp [futureMass, wordMatrix, marked]

private theorem future_two (i : Hidden) :
    futureMass marked i 2 (Fin.cons false (fun _ => true)) =
      prob i false * prob (next i false) true := by
  rw [future_rec, future_one]

/-- Equality of all original finite future laws is precisely equality of phase and residue modulo three. -/
theorem future_classes (i j : Hidden) : (futureSetoid marked).r i j ↔ label i = label j := by
  constructor
  · intro h
    have h1 := congrFun (congrFun h 1) (fun _ => true)
    have h2 := congrFun (congrFun h 2) (Fin.cons false (fun _ => true))
    change futureMass marked i 1 _ = futureMass marked j 1 _ at h1
    change futureMass marked i 2 _ = futureMass marked j 2 _ at h2
    rw [future_one, future_one] at h1
    rw [future_two, future_two] at h2
    rcases i with ⟨b,s⟩
    rcases j with ⟨d,t⟩
    cases b <;> cases d <;> fin_cases s <;> fin_cases t <;>
      simp_all [prob, next, rate, label] <;> norm_num at *
  · exact same_label_future i j


/-- A preceding T forbids a first one; subsequent pairs obey the original no11 rule. -/
def Allowed : Bool → (n : ℕ) → (Fin n → Bool) → Prop
  | _, 0, _ => True
  | b, n+1, w => ¬(b = true ∧ w 0 = true) ∧ Allowed (w 0) n (Fin.tail w)

/-- Complete open-path legality: there is no first-to-last constraint. -/
def Legal (n : ℕ) (w : Fin n → Bool) : Prop := Allowed false n w

private theorem prob_pos (i : Hidden) (x : Bool) :
    0 < prob i x ↔ ¬(i.1 = true ∧ x = true) := by
  rcases i with ⟨b,s⟩
  cases b <;> cases x <;> fin_cases s <;> norm_num [prob, rate]

private theorem word_nonneg (n : ℕ) (i : Hidden) (w : Fin n → Bool) :
    0 ≤ wordMass prob next n i w :=
  UnifilarAffinityContraction.word_nonneg prob next prob_nonneg n i w

private theorem word_pos (n : ℕ) (i : Hidden) (w : Fin n → Bool) :
    0 < wordMass prob next n i w ↔ Allowed i.1 n w := by
  induction n generalizing i with
  | zero => simp [wordMass, Allowed]
  | succ n ih =>
    rw [wordMass]
    have he : 0 < prob i (w 0) * wordMass prob next n (next i (w 0)) (Fin.tail w) ↔
        0 < prob i (w 0) ∧ 0 < wordMass prob next n (next i (w 0)) (Fin.tail w) := by
      constructor
      · intro hp
        rcases mul_pos_iff.mp hp with h | h
        · exact h
        · exact False.elim (not_lt_of_ge (prob_nonneg _ _) h.1)
      · exact fun h => mul_pos h.1 h.2
    rw [he, prob_pos, ih]
    rfl

private theorem allowed_legal (b : Bool) (n : ℕ) (w : Fin n → Bool)
    (h : Allowed b n w) : Legal n w := by
  cases n with
  | zero => trivial
  | succ n => exact ⟨by simp, h.2⟩

private theorem next_chosen (i : Hidden) (x : Bool) (hp : prob i x ≠ 0) :
    successor marked i x = next i x := by
  have hpos : 0 < marked x i (next i x) := by
    simpa [marked] using lt_of_le_of_ne (prob_nonneg i x) (Ne.symm hp)
  have hex : ∃ j, 0 < marked x i j := ⟨next i x,hpos⟩
  change (if h : ∃ j, 0 < marked x i j then Classical.choose h else i) = next i x
  rw [dif_pos hex]
  exact unifilar x i _ _ (Classical.choose_spec hex) hpos

private theorem word_coordinates (n : ℕ) (i : Hidden) (w : Fin n → Bool)
    (a : FutureClass marked) :
    (if classOf marked (endpoint (successor marked) n i w) = a
      then wordMass (symbolMass marked) (successor marked) n i w else 0) =
    if classOf marked (endpoint next n i w) = a then wordMass prob next n i w else 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [endpoint, wordMass, symbolMass, marked_row]
    by_cases hp : prob i (w 0) = 0
    · simp [hp]
    · rw [next_chosen i (w 0) hp]
      simpa only [mul_ite, mul_zero] using
        congrArg (fun z => prob i (w 0) * z) (ih (next i (w 0)) (Fin.tail w))

private theorem class_eq (i j : Hidden) : classOf marked i = classOf marked j ↔ label i = label j :=
  ⟨fun h => (future_classes i j).mp (Quotient.exact h),
    fun h => Quotient.sound ((future_classes i j).mpr h)⟩

/-- One original bilateral joint law and its actual visible marginal are used below. -/
def joint : ProbabilityMeasure (PathSpace Hidden) := jointLaw parameter

def visible : ProbabilityMeasure (ℤ → Bool) := visibleLaw parameter

private theorem cells (t : ℤ) (n : ℕ) (w : Fin n → Bool) (a : Hidden) :
    (joint : Measure _).real (endpointEvent marked t n w (classOf marked a)) =
      ∑ i, mass i * if label (endpoint next n i w) = label a then wordMass prob next n i w else 0 := by
  have hc := (same_law_trimming parameter).1
  have hm := actual_endpoint_mass ⟨Hidden,inferInstance,parameter⟩ unifilar
    (joint : Measure _) hc t n w (classOf marked a)
  change (joint : Measure _).real (endpointEvent marked t n w (classOf marked a)) =
    ∑ i : Hidden, mass i *
      if endpoint (quotientSuccessor marked) n (classOf marked i) w = classOf marked a
      then wordMass (quotientMass marked) (quotientSuccessor marked) n (classOf marked i) w else 0 at hm
  rw [hm]
  apply Finset.sum_congr rfl
  intro i _
  change mass i * _ = _
  rw [← word_quotient marked marked_nonneg unifilar, word_coordinates]
  simp only [class_eq]

private theorem cell_nonneg (n : ℕ) (w : Fin n → Bool) (a i : Hidden) :
    0 ≤ mass i * if label (endpoint next n i w) = label a then wordMass prob next n i w else 0 := by
  exact mul_nonneg (mass_pos i).le (by split_ifs; exact word_nonneg _ _ _; exact le_rfl)

private theorem advance_surjective : Surjective advance := by
  intro s
  fin_cases s
  · exact ⟨5,by decide⟩
  · exact ⟨0,by decide⟩
  · exact ⟨1,by decide⟩
  · exact ⟨2,by decide⟩
  · exact ⟨3,by decide⟩
  · exact ⟨4,by decide⟩

/-- The hidden transition uses the original emitted-bit clock. -/
def hiddenTransition : Matrix Hidden Hidden ℝ := marked false + marked true

private theorem transition_nonneg (i j : Hidden) : 0 ≤ hiddenTransition i j :=
  add_nonneg (marked_nonneg false i j) (marked_nonneg true i j)

private theorem power_join (m n : ℕ) (i k j : Hidden)
    (hm : 0 < (hiddenTransition ^ m) i k) (hn : 0 < (hiddenTransition ^ n) k j) :
    0 < (hiddenTransition ^ (m+n)) i j := by
  rw [pow_add, Matrix.mul_apply]
  exact (mul_pos hm hn).trans_le
    (Finset.single_le_sum (fun l _ => mul_nonneg
      (Matrix.pow_apply_nonneg transition_nonneg m i l)
      (Matrix.pow_apply_nonneg transition_nonneg n l j)) (Finset.mem_univ k))

private theorem zero_edge (i : Hidden) : 0 < hiddenTransition i (false,i.2) := by
  rcases i with ⟨b,s⟩
  cases b <;> fin_cases s <;> norm_num [hiddenTransition,marked,next,prob,rate,advance]

private theorem one_edge (s : Fin 6) : 0 < hiddenTransition (false,s) (true,advance s) := by
  fin_cases s <;> norm_num [hiddenTransition,marked,next,prob,rate,advance]

private theorem wait_free (s : Fin 6) (n : ℕ) :
    0 < (hiddenTransition ^ n) (false,s) (false,s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact power_join n 1 _ _ _ ih (by simpa using zero_edge (false,s))

private theorem advance_path (s : Fin 6) (k : ℕ) :
    0 < (hiddenTransition ^ (2*k)) (false,s) (false,(advance^[k]) s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have hp := power_join 1 1 (false,s) (true,advance s) (false,advance s)
      (by simpa using one_edge s) (by simpa using zero_edge (true,advance s))
    have h := power_join 2 (2*k) _ _ _ hp (ih (advance s))
    simpa only [Function.iterate_succ_apply, show 2*(k+1) = 2+2*k by omega] using h

private theorem advance_reaches (s t : Fin 6) :
    ∃ k : ℕ, k ≤ 5 ∧ (advance^[k]) s = t := by
  have h : ∀ s t : Fin 6, ∃ k : Fin 6, (advance^[k.val]) s = t := by decide
  obtain ⟨k,hk⟩ := h s t
  exact ⟨k.val,by omega,hk⟩

/-- Every hidden transition power from twelve onward is strictly positive. Thus the original
hidden chain is primitive (in particular irreducible and aperiodic), including its T states. -/
theorem actual_hidden_primitivity :
    Matrix.IsPrimitive hiddenTransition ∧
      ∀ n : ℕ, 12 ≤ n → ∀ i j : Hidden, 0 < (hiddenTransition ^ n) i j := by
  have hpos (n : ℕ) (hn : 12 ≤ n) (i j : Hidden) : 0 < (hiddenTransition ^ n) i j := by
    obtain ⟨s,hs⟩ : ∃ s : Fin 6, (if j.1 then (true,advance s) else (false,s)) = j := by
      rcases j with ⟨b,t⟩
      cases b
      · exact ⟨t,rfl⟩
      · obtain ⟨s,hs⟩ := advance_surjective t
        exact ⟨s,by simpa using congrArg (fun x => (true,x)) hs⟩
    obtain ⟨k,hk,he⟩ := advance_reaches i.2 s
    let e : ℕ := if j.1 then 1 else 0
    have he1 : e ≤ 1 := by dsimp [e]; split <;> omega
    have ht : 1 + (n-1-2*k-e) + 2*k + e = n := by omega
    have hp := power_join 1 (n-1-2*k-e) i (false,i.2) (false,i.2)
      (by simpa using zero_edge i) (wait_free i.2 _)
    have hp' := power_join (1+(n-1-2*k-e)) (2*k) i (false,i.2) (false,s) hp
      (by simpa only [he] using advance_path i.2 k)
    have hend : 0 < (hiddenTransition ^ e) (false,s) j := by
      rw [← hs]
      cases hb : j.1 <;> simp only [hb,Bool.false_eq_true,↓reduceIte,e]
      · simp
      · simpa using one_edge s
    simpa only [ht] using power_join _ e i (false,s) j hp' hend
  exact ⟨⟨transition_nonneg,12,by norm_num,fun i j => hpos 12 le_rfl i j⟩,hpos⟩

#print axioms actual_hidden_primitivity

/-- The actual six-class marked quotient is strongly connected and row unifilar. Equality
of its original complete-future measures at every integer cut is exactly label equality. -/
theorem actual_quotient_interface :
    let B := OriginalUnifilarQuotient.classMatrix marked
    Matrix.IsIrreducible (B false + B true) ∧ RowUnifilar B ∧
    ∀ (t : ℤ) (i j : Hidden),
      OriginalFutureScreening.futureLaw (joint : Measure _) t i =
        OriginalFutureScreening.futureLaw (joint : Measure _) t j ↔ label i = label j := by
  let B := OriginalUnifilarQuotient.classMatrix marked
  have hg (i : Hidden) (x : Bool) (b : FutureClass marked) :
      (∑ j, if classOf marked j = b then marked x i j else 0) = B x (classOf marked i) b :=
    OriginalUnifilarQuotient.row_group parameter unifilar i x b
  have hb (x : Bool) (a b : FutureClass marked) : 0 ≤ B x a b := by
    have ha : classOf marked a.out = a := Quotient.out_eq a
    have hh := hg a.out x b
    rw [ha] at hh
    rw [← hh]
    exact Finset.sum_nonneg fun j _ => by split_ifs; exact marked_nonneg _ _ _; exact le_rfl
  have hle (x : Bool) (i j : Hidden) : marked x i j ≤ B x (classOf marked i) (classOf marked j) := by
    rw [← hg]
    simpa using
      (Finset.single_le_sum (s := Finset.univ) (f := fun k =>
        if classOf marked k = classOf marked j then marked x i k else 0)
        (fun k _ => by split_ifs; exact marked_nonneg _ _ _; exact le_rfl) (Finset.mem_univ j))
  have hconn : Matrix.IsIrreducible (B false + B true) := by
    letI : Quiver Hidden := Matrix.toQuiver hiddenTransition
    letI : Quiver (FutureClass marked) := Matrix.toQuiver (B false + B true)
    let F : Hidden ⥤q FutureClass marked := {
      obj := classOf marked
      map := fun {i j} e => ⟨e.down.trans_le (add_le_add (hle false i j) (hle true i j))⟩ }
    have hlength {i j : Hidden} (p : Quiver.Path i j) : (F.mapPath p).length = p.length := by
      induction p with
      | nil => rfl
      | cons p e ih => simpa only [Prefunctor.mapPath_cons,Quiver.Path.length_cons] using congrArg Nat.succ ih
    refine ⟨fun a b => add_nonneg (hb false a b) (hb true a b),?_⟩
    intro a b
    obtain ⟨p,hp⟩ := actual_hidden_primitivity.1.isIrreducible.connected a.out b.out
    have h : ∃ q : Quiver.Path (classOf marked a.out) (classOf marked b.out), 0 < q.length :=
      ⟨F.mapPath p,by rwa [hlength]⟩
    have ha : classOf marked a.out = a := Quotient.out_eq a
    have hb : classOf marked b.out = b := Quotient.out_eq b
    rwa [ha,hb] at h
  refine ⟨hconn,?_,?_⟩
  · intro x a b c hb hc
    have hb' : b = quotientSuccessor marked a x := by
      by_contra h
      simpa [B,OriginalUnifilarQuotient.classMatrix,h] using hb
    have hc' : c = quotientSuccessor marked a x := by
      by_contra h
      simpa [B,OriginalUnifilarQuotient.classMatrix,h] using hc
    exact hb'.trans hc'.symm
  · intro t i j
    let ip : PositiveSupportPresentation.Positive parameter := ⟨i,mass_pos i⟩
    let jp : PositiveSupportPresentation.Positive parameter := ⟨j,mass_pos j⟩
    have h := (OriginalFutureScreening.same_law_future_screening parameter).1 t ip jp
    exact h.1.symm.trans (h.2.symm.trans (future_classes i j))

#print axioms actual_quotient_interface

def residuePath : (n : ℕ) → Fin 6 → (Fin n → Bool) → Fin 6
  | 0, s, _ => s
  | n+1, s, w => residuePath n (if w 0 then advance s else s) (Fin.tail w)

private theorem endpoint_residue (n : ℕ) (i : Hidden) (w : Fin n → Bool) :
    (endpoint next n i w).2 = residuePath n i.2 w := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => exact ih (next i (w 0)) (Fin.tail w)

private theorem residue_surjective (n : ℕ) (w : Fin n → Bool) :
    Surjective (fun s => residuePath n s w) := by
  induction n with
  | zero => exact surjective_id
  | succ n ih =>
    change Surjective ((fun s => residuePath n s (Fin.tail w)) ∘
      (fun s => if w 0 then advance s else s))
    apply (ih (Fin.tail w)).comp
    cases h : w 0 <;> simp only [h, Bool.false_eq_true, ↓reduceIte]
    · exact surjective_id
    · exact advance_surjective

private theorem endpoint_phase (n : ℕ) (i : Hidden) (w : Fin (n+1) → Bool) :
    (endpoint next (n+1) i w).1 = w (Fin.last n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simpa only [endpoint, Fin.tail, Fin.succ_last] using ih (next i (w 0)) (Fin.tail w)

/-- Every original positive-length word ends in precisely the three classes selected by its last bit.
The statement is a joint-event mass identity on the original law, at every integer start. -/
theorem actual_endpoint_support (t : ℤ) (n : ℕ) (w : Fin (n+1) → Bool) (a : Hidden) :
    0 < (joint : Measure _).real (endpointEvent marked t (n+1) w (classOf marked a)) ↔
      Legal (n+1) w ∧ a.1 = w (Fin.last n) := by
  rw [cells]
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => cell_nonneg _ _ _ i)).mp hp
    split_ifs at hi with he
    · have hw : 0 < wordMass prob next (n+1) i w := (mul_pos_iff.mp hi).elim And.right
        (fun h => False.elim (not_lt_of_ge (mass_pos i).le h.1))
      refine ⟨allowed_legal _ _ _ ((word_pos _ _ _).mp hw),?_⟩
      exact (congrArg Prod.fst he).symm.trans (endpoint_phase n i w)
    · simp at hi
  · rintro ⟨hw,ha⟩
    obtain ⟨s,hs⟩ := residue_surjective (n+1) w a.2
    let i : Hidden := (false,s)
    have he : endpoint next (n+1) i w = a := by
      apply Prod.ext
      · exact (endpoint_phase n i w).trans ha.symm
      · exact (endpoint_residue (n+1) i w).trans hs
    have hp : 0 < mass i * if label (endpoint next (n+1) i w) = label a
        then wordMass prob next (n+1) i w else 0 := by
      rw [he,if_pos rfl]
      exact mul_pos (mass_pos i) ((word_pos _ _ _).mpr hw)
    exact hp.trans_le (Finset.single_le_sum (fun j _ => cell_nonneg _ _ _ j) (Finset.mem_univ i))

/-- The empty observed word leaves all six actual future classes with positive mass. -/
theorem actual_empty_support (t : ℤ) (a : Hidden) :
    0 < (joint : Measure _).real (endpointEvent marked t 0 (fun i => nomatch i) (classOf marked a)) := by
  rw [cells]
  have hp : 0 < mass a * if label (endpoint next 0 a (fun i => nomatch i)) = label a
      then wordMass prob next 0 a (fun i => nomatch i) else 0 := by
    simpa [endpoint,wordMass] using mass_pos a
  exact hp.trans_le (Finset.single_le_sum (fun j _ => cell_nonneg _ _ _ j) (Finset.mem_univ a))


private theorem future_word (n : ℕ) (i : Hidden) (w : Fin n → Bool) :
    futureMass marked i n w = wordMass prob next n i w := by
  induction n generalizing i with
  | zero => rw [future_empty]; rfl
  | succ n ih =>
    rw [← Fin.cons_self_tail w, future_rec, wordMass, Fin.cons_zero, Fin.tail_cons, ih]


/-- Every pair of distinct actual future classes has length-two affinity at most sqrt(15)/4.
The distributions are computed from the original marked matrices, not supplied as posterior data. -/
theorem actual_two_word_affinity (i j : Hidden) (hij : label i ≠ label j) :
    D5.S3.TotalVariation.Bhattacharyya.bhattacharyya
      (futureMass marked i 2) (futureMass marked j 2) ≤ Real.sqrt 15 / 4 := by
  have hnorm (a : Hidden) :
      (∀ w, 0 ≤ futureMass marked a 2 w) ∧ ∑ w, futureMass marked a 2 w = 1 := by
    exact ⟨fun w => by rw [future_word]; exact word_nonneg _ _ _,by
      simp_rw [future_word]
      exact UnifilarAffinityContraction.word_total prob next
        (fun b => by rw [Fintype.sum_bool]; exact (add_comm _ _).trans (prob_sum b)) 2 a⟩
  have htv : (1:ℝ)/4 ≤ D5.S3.TotalVariation.Pinsker.totalVariation
      (futureMass marked i 2) (futureMass marked j 2) := by
    unfold D5.S3.TotalVariation.Pinsker.totalVariation
    simp_rw [future_word]
    simp_rw [sum_words]
    simp only [Fintype.sum_bool,wordMass,Fin.cons_zero,Fin.tail_cons,mul_one,Finset.sum_const,Fintype.card_unique,nsmul_eq_mul,one_mul]
    rcases i with ⟨b,s⟩
    rcases j with ⟨d,t⟩
    cases b <;> cases d <;> fin_cases s <;> fin_cases t <;>
      norm_num [label] at hij <;> norm_num [prob,next,rate,advance]
  have hcs := D5.S3.TotalVariation.Bhattacharyya.total_variation_sq_le_one_sub_bhattacharyya_sq
    (futureMass marked i 2) (futureMass marked j 2) (hnorm i) (hnorm j)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)
  have hr := Real.sqrt_nonneg (15:ℝ)
  nlinarith

#print axioms actual_two_word_affinity

private theorem visible_cells (t : ℤ) (n : ℕ) (w : Fin n → Bool) :
    (visible : Measure _).real (visibleCylinder t n w) =
      ∑ i, mass i * wordMass prob next n i w := by
  have hm := visible_masses parameter (joint : Measure _) (same_law_trimming parameter).1 t n w
  change (visible : Measure _).real (visibleCylinder t n w) =
    ∑ i : Hidden, mass i * futureMass marked i n w at hm
  rw [hm]
  simp_rw [future_word]

/-- Every legal open-path cylinder has positive probability, and every other cylinder has zero mass. -/
theorem actual_visible_support (t : ℤ) (n : ℕ) (w : Fin n → Bool) :
    0 < (visible : Measure _).real (visibleCylinder t n w) ↔ Legal n w := by
  rw [visible_cells]
  have hn (i : Hidden) : 0 ≤ mass i * wordMass prob next n i w :=
    mul_nonneg (mass_pos i).le (word_nonneg n i w)
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hn i)).mp hp
    have hw := (mul_pos_iff.mp hi).elim And.right
      (fun h => False.elim (not_lt_of_ge (mass_pos i).le h.1))
    exact allowed_legal _ _ _ ((word_pos _ _ _).mp hw)
  · intro hw
    have hp : 0 < mass (false,0) * wordMass prob next n (false,0) w :=
      mul_pos (mass_pos _) ((word_pos _ _ _).mpr hw)
    exact hp.trans_le (Finset.single_le_sum (fun i _ => hn i) (Finset.mem_univ _))

/-- Actual atomwise class posterior; only positive visible atoms are used in its support theorem. -/
def atomPosterior (t : ℤ) (n : ℕ) (w : Fin n → Bool) (a : Hidden) : ℝ :=
  (joint : Measure _).real (endpointEvent marked t n w (classOf marked a)) /
    (visible : Measure _).real (visibleCylinder t n w)

/-- The exact finite-atom ratio has three positive class entries after a nonempty positive word. -/
theorem actual_atom_posterior_support (t : ℤ) (n : ℕ) (w : Fin (n+1) → Bool)
    (hw : 0 < (visible : Measure _).real (visibleCylinder t (n+1) w)) (a : Hidden) :
    0 < atomPosterior t (n+1) w a ↔ a.1 = w (Fin.last n) := by
  rw [atomPosterior, div_pos_iff_of_pos_right hw, actual_endpoint_support]
  exact and_iff_right ((actual_visible_support t (n+1) w).mp hw)

#print axioms actual_visible_support
#print axioms actual_atom_posterior_support


/-- Exact finite-word synchronization for the actual original future class. -/
def HasSynchronizingWord : Prop :=
  ∃ (t : ℤ) (n : ℕ) (w : Fin n → Bool) (a : FutureClass marked),
    0 < (visible : Measure _).real (visibleCylinder t n w) ∧
    ∀ b : FutureClass marked,
      0 < (joint : Measure _).real (endpointEvent marked t n w b) → b = a

/-- No positive finite word synchronizes the actual future quotient, including the empty word. -/
theorem no_synchronizing_word : ¬ HasSynchronizingWord := by
  rintro ⟨t,n,w,a,hw,ha⟩
  have two (i j : Hidden)
      (hi : 0 < (joint : Measure _).real (endpointEvent marked t n w (classOf marked i)))
      (hj : 0 < (joint : Measure _).real (endpointEvent marked t n w (classOf marked j))) :
      label i = label j := by
    exact (class_eq i j).mp ((ha _ hi).trans (ha _ hj).symm)
  cases n with
  | zero =>
    have hew : w = (fun i : Fin 0 => nomatch i) := Subsingleton.elim _ _
    subst w
    have he := two (false,0) (false,1)
      (by simpa using actual_empty_support t (false,0))
      (by simpa using actual_empty_support t (false,1))
    norm_num [label] at he
  | succ n =>
    have hl := (actual_visible_support t (n+1) w).mp hw
    have hi := (actual_endpoint_support t n w (w (Fin.last n),0)).mpr ⟨hl,rfl⟩
    have hj := (actual_endpoint_support t n w (w (Fin.last n),1)).mpr ⟨hl,rfl⟩
    have he := two (w (Fin.last n),0) (w (Fin.last n),1) hi hj
    have hh := congrArg (fun x : Label => x.2.val) he
    norm_num [label] at hh

#print axioms no_synchronizing_word

#print axioms actual_endpoint_support
#print axioms actual_empty_support

#print axioms future_classes
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.TwelveStatePresentation
