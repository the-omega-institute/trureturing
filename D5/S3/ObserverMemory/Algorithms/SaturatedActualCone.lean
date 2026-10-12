/- GID: D5/S3/ObserverMemory/Algorithms/SaturatedActualCone
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SaturatedActualCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete actual event fibers and their saturated successor transport. -/

import D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
import D5.S0.Computability.Coding.PrefixFreeCode
import Mathlib.Data.Tree.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SaturatedActualCone

open ActualControlSlots SaturatedActualHistories
open scoped BigOperators

variable {p P : Nat} {Q : Type} [Fintype Q] [DecidableEq Q]
variable (hp : 2 ≤ p) (hP : 0 < P) (C : Controller p P Q) (I : C.Correct hp hP)

attribute [local instance] Classical.propDecidable
local notation "Source" => ZMod (p * P)
local notation "Slot" => {q : Q // ∃ b, C.Used I q b} × Fin p

/-- All initialized occurrences at a slot, retaining the original input and physical time. -/
noncomputable def events (u : Slot) : Finset (Source × Nat) := by
  letI : NeZero (p * P) := ⟨by positivity⟩
  exact (Finset.univ.biUnion (fun x : Source =>
    (Finset.range (I.length x)).image (fun t => (x,t)))).filter
      (fun e => C.Occurs I e.1 e.2 u)

private theorem mem_events {u : Slot} {e : Source × Nat} :
    e ∈ events hp hP C I u ↔ C.Occurs I e.1 e.2 u := by
  classical
  letI : NeZero (p * P) := ⟨by positivity⟩
  simp only [events, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨⟨e.1,e.2,h.1,rfl⟩,h⟩⟩

/-- The one-based read index at an actual occurrence. -/
noncomputable def readIndex (e : Source × Nat) : Nat :=
  ((readEvents hp hP C I e.1).filter (fun t => t ≤ e.2)).card

/-- Dyadic mass of the entire slot event fiber at the common read deadline. -/
noncomputable def mass (h : Nat) (u : Slot) : Real :=
  ∑ e ∈ events hp hP C I u, (1 / 2 : Real) ^ (h - readIndex hp hP C I e)

private noncomputable def answer (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    (u v : Slot) : Fin 2 :=
  if hn : (G.next u).Nonempty then if v = hn.choose then 0 else 1 else 0

private theorem answer_injective (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    {u v w : Slot} (hv : v ∈ G.next u) (hw : w ∈ G.next u)
    (eq : answer hp hP C I G u v = answer hp hP C I G u w) : v = w := by
  classical
  have hn : (G.next u).Nonempty := ⟨v,hv⟩
  by_cases vf : v = hn.choose
  · by_cases wf : w = hn.choose
    · exact vf.trans wf.symm
    · simp [answer, hn, vf, wf] at eq
  · by_cases wf : w = hn.choose
    · simp [answer, hn, vf, wf] at eq
    · have small : (G.next u |>.erase hn.choose).card ≤ 1 := by
        have hc := Finset.card_erase_of_mem hn.choose_spec
        have bound := G.at_most_two u
        omega
      exact (Finset.card_le_one.mp small) v (Finset.mem_erase.mpr ⟨vf,hv⟩)
        w (Finset.mem_erase.mpr ⟨wf,hw⟩)

/-- A binary word follows the original run, with only waits between consecutive reads. -/
private inductive FutureWord (G : SlotGraph p {q : Q // ∃ b, C.Used I q b}) :
    Slot → Source → Nat → List (Fin 2) → Prop where
  | stop {u : Slot} {x : Source} {t : Nat}
      (occurs : C.Occurs I x t u) (halt : C.action (C.readNext u.1.val u.2) = .halt) :
      FutureWord G u x t []
  | next {u v : Slot} {x : Source} {t k : Nat} {word : List (Fin 2)}
      (occurs : C.Occurs I x t u) (child : C.Occurs I x k v)
      (before : t < k)
      (waits : ∀ i, t < i → i < k → C.action (C.run hp hP x i).2 = .wait)
      (edge : v ∈ G.next u) (tail : FutureWord G v x k word) :
      FutureWord G u x t (answer hp hP C I G u v :: word)


private theorem terminal_end {u : Slot} {x : Source} {t : Nat}
    (occurs : C.Occurs I x t u) (halt : C.action (C.readNext u.1.val u.2) = .halt) :
    C.output (C.readNext u.1.val u.2) = x ∧ t + 1 = I.length x := by
  obtain ⟨_, _, _, _, _, read, _⟩ := u.1.property
  exact C.terminal_label I
    ⟨⟨x,t,occurs.1,occurs.2.1,read,occurs.2.2⟩,halt⟩
    occurs.1 occurs.2.1 occurs.2.2

private theorem future_exists (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    (edges : ∀ u v, v ∈ G.next u ↔ C.Edge I u v) :
    ∀ n u x t, C.Occurs I x t u → (laterReads hp hP C I x t).card ≤ n →
      ∃ word, FutureWord hp hP C I G u x t word ∧
        word.length = (laterReads hp hP C I x t).card := by
  intro n
  induction n with
  | zero =>
    intro u x t occurs bound
    by_cases halt : C.action (C.readNext u.1.val u.2) = .halt
    · exact ⟨[], .stop occurs halt, by simp; omega⟩
    · obtain ⟨k,v,child,before,waits,count⟩ := next_event hp hP C I occurs halt
      omega
  | succ n ih =>
    intro u x t occurs bound
    by_cases halt : C.action (C.readNext u.1.val u.2) = .halt
    · have last := (terminal_end hp hP C I occurs halt).2
      have empty : laterReads hp hP C I x t = ∅ := by
        ext k
        simp only [laterReads, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
          iff_false, not_and]
        omega
      exact ⟨[],.stop occurs halt,by simp [empty]⟩
    · obtain ⟨k,v,child,before,waits,count⟩ := next_event hp hP C I occurs halt
      obtain ⟨word,tail,length⟩ := ih v x k child (by omega)
      exact ⟨answer hp hP C I G u v :: word,
        .next occurs child before waits ((edges u v).mpr ⟨x,t,k,occurs,child,before,waits⟩) tail,
        by simp only [List.length_cons,length]; omega⟩

private theorem future_prefix (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    {u : Slot} {x y : Source} {t s : Nat} {word other : List (Fin 2)}
    (path : FutureWord hp hP C I G u x t word)
    (path' : FutureWord hp hP C I G u y s other) (pref : word <+: other) :
    x = y ∧ t = s ∧ word = other := by
  induction path generalizing y s other with
  | @stop u x t occurs halt =>
    cases path' with
    | stop occurs' halt' =>
      have a := terminal_end hp hP C I occurs halt
      have b := terminal_end hp hP C I occurs' halt'
      have xy := a.1.symm.trans b.1
      exact ⟨xy,by rw [xy] at a; omega,rfl⟩
    | next occurs' child' before' waits' edge' tail' =>
      exact False.elim (terminal_no_edge hp hP C I halt
        ⟨y,s,_,occurs',child',before',waits'⟩)
  | @next u v x t k word occurs child before waits edge tail ih =>
    cases path' with
    | stop occurs' halt' => simpa using pref
    | @next _ w _ _ j other occurs' child' before' waits' edge' tail' =>
      obtain ⟨head,tailpref⟩ := List.cons_prefix_cons.mp pref
      have vw := answer_injective hp hP C I G edge edge' head
      subst w
      obtain ⟨xy,kj,ww⟩ := ih tail' tailpref
      subst y
      subst j
      obtain ⟨_,_,_,_,_,read,_⟩ := u.1.property
      have ts : t = s := by
        rcases lt_trichotomy t s with lt | eq | gt
        · have clash := waits s lt before'
          rw [occurs'.2.1,read] at clash
          cases clash
        · exact eq
        · have clash := waits' t gt before
          rw [occurs.2.1,read] at clash
          cases clash
      exact ⟨rfl,ts,by rw [ww]⟩

private noncomputable def futureCode (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    (edges : ∀ u v, v ∈ G.next u ↔ C.Edge I u v) (u : Slot) (e : Source × Nat) :
    List (Fin 2) :=
  if he : C.Occurs I e.1 e.2 u then
    (future_exists hp hP C I G edges (laterReads hp hP C I e.1 e.2).card
      u e.1 e.2 he le_rfl).choose else []

private theorem code_spec (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    (edges : ∀ u v, v ∈ G.next u ↔ C.Edge I u v) {u : Slot} {e : Source × Nat}
    (he : e ∈ events hp hP C I u) :
    FutureWord hp hP C I G u e.1 e.2 (futureCode hp hP C I G edges u e) ∧
    (futureCode hp hP C I G edges u e).length = (laterReads hp hP C I e.1 e.2).card := by
  have occurs := (mem_events hp hP C I).mp he
  simp only [futureCode,dif_pos occurs]
  exact (future_exists hp hP C I G edges _ _ _ _ occurs le_rfl).choose_spec

private theorem suffix_kraft (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    (edges : ∀ u v, v ∈ G.next u ↔ C.Edge I u v) (u : Slot)
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt) :
    ∑ e ∈ events hp hP C I u, (1 / 2 : Real) ^ (laterReads hp hP C I e.1 e.2).card ≤ 1 := by
  classical
  let f := futureCode hp hP C I G edges u
  let S := (events hp hP C I u).image f
  have injective : Set.InjOn f (events hp hP C I u) := by
    intro e he d hd eq
    have key := future_prefix hp hP C I G (code_spec hp hP C I G edges he).1
      (code_spec hp hP C I G edges hd).1 (show futureCode hp hP C I G edges u e <+: futureCode hp hP C I G edges u d from by
        change f e <+: f d
        rw [eq])
    exact Prod.ext key.1 key.2.1
  have pf : D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree (S : Set (List (Fin 2))) := by
    intro a ha b hb pref
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hb
    exact (future_prefix hp hP C I G (code_spec hp hP C I G edges he).1
      (code_spec hp hP C I G edges hd).1 pref).2.2
  have nil : [] ∉ S := by
    intro hn
    obtain ⟨e,he,eq⟩ := Finset.mem_image.mp hn
    have path := (code_spec hp hP C I G edges he).1
    change FutureWord hp hP C I G u e.1 e.2 (f e) at path
    rw [eq] at path
    cases path with
    | stop occurs halt => exact active halt
  have kraft := D5.S0.Computability.Coding.PrefixFreeCode.kraft_inequality_of_isPrefixFree pf nil
  simp only [Fintype.card_fin] at kraft
  rw [Finset.sum_image injective] at kraft
  convert kraft using 1
  apply Finset.sum_congr rfl
  intro e he
  rw [(code_spec hp hP C I G edges he).2]
  norm_num


private theorem index_split (e : Source × Nat) :
    readIndex hp hP C I e + (laterReads hp hP C I e.1 e.2).card =
      (readEvents hp hP C I e.1).card := by
  classical
  have partition := (readEvents hp hP C I e.1).card_filter_add_card_filter_not
    (fun t => t ≤ e.2)
  convert partition using 1
  congr 1
  congr 1
  ext t
  simp only [readEvents, laterReads, Finset.mem_filter, Finset.mem_range, not_le]
  tauto

private theorem event_weight_le_one (h : Nat) (e : Source × Nat) :
    (1 / 2 : Real) ^ (h - readIndex hp hP C I e) ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

private theorem slot_capacity (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) (u : Slot) :
    mass hp hP C I h u ≤ 1 := by
  classical
  by_cases active : C.action (C.readNext u.1.val u.2) ≠ .halt
  · obtain ⟨G,root,used,edges,rest⟩ := C.result I
    apply le_trans (b := ∑ e ∈ events hp hP C I u,
      (1 / 2 : Real) ^ (laterReads hp hP C I e.1 e.2).card)
    · apply Finset.sum_le_sum
      intro e he
      have split := index_split hp hP C I e
      have bound := budget e.1
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · exact suffix_kraft hp hP C I G edges u active
  · have halt : C.action (C.readNext u.1.val u.2) = .halt := not_ne_iff.mp active
    have small : (events hp hP C I u).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro e he d hd
      have a := terminal_end hp hP C I ((mem_events hp hP C I).mp he) halt
      have b := terminal_end hp hP C I ((mem_events hp hP C I).mp hd) halt
      have eq : e.1 = d.1 := a.1.symm.trans b.1
      apply Prod.ext eq
      rw [eq] at a
      omega
    calc
      mass hp hP C I h u ≤ ∑ _e ∈ events hp hP C I u, (1 : Real) :=
        Finset.sum_le_sum (fun e _ => event_weight_le_one hp hP C I h e)
      _ = ((events hp hP C I u).card : Real) := by simp
      _ ≤ 1 := by exact_mod_cast small

private noncomputable def advance (u : Slot)
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt) (e : Source × Nat) :
    (Source × Nat) × Slot :=
  if he : C.Occurs I e.1 e.2 u then
    let next := next_event hp hP C I he active
    ((e.1,next.choose),next.choose_spec.choose)
  else (e,u)

private theorem advance_spec {u : Slot}
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt) {e : Source × Nat}
    (he : e ∈ events hp hP C I u) :
    let a := advance hp hP C I u active e
    a.1.1 = e.1 ∧ C.Occurs I e.1 a.1.2 a.2 ∧ e.2 < a.1.2 ∧
      (∀ t, e.2 < t → t < a.1.2 → C.action (C.run hp hP e.1 t).2 = .wait) ∧
      (laterReads hp hP C I e.1 a.1.2).card + 1 =
        (laterReads hp hP C I e.1 e.2).card := by
  have occurs := (mem_events hp hP C I).mp he
  simp only [advance,dif_pos occurs]
  exact ⟨trivial,(next_event hp hP C I occurs active).choose_spec.choose_spec⟩

private theorem advance_injective {u : Slot}
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt) :
    Set.InjOn (fun e => (advance hp hP C I u active e).1) (events hp hP C I u) := by
  intro e he d hd eq
  have a := advance_spec hp hP C I active he
  have b := advance_spec hp hP C I active hd
  have xy : e.1 = d.1 := a.1.symm.trans ((congrArg Prod.fst eq).trans b.1)
  have times := congrArg Prod.snd eq
  have ed : e.2 = d.2 := by
    obtain ⟨_,_,_,_,_,read,_⟩ := u.1.property
    rcases lt_trichotomy e.2 d.2 with lt | same | gt
    · have clash := a.2.2.2.1 d.2 lt (by rw [times]; exact b.2.2.1)
      rw [xy,(mem_events hp hP C I).mp hd |>.2.1,read] at clash
      cases clash
    · exact same
    · have clash := b.2.2.2.1 e.2 gt (by rw [← times]; exact a.2.2.1)
      rw [← xy,(mem_events hp hP C I).mp he |>.2.1,read] at clash
      cases clash
  exact Prod.ext xy ed

private theorem advance_weight (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u : Slot}
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt) {e : Source × Nat}
    (he : e ∈ events hp hP C I u) :
    (1 / 2 : Real) ^ (h - readIndex hp hP C I (advance hp hP C I u active e).1) =
      2 * (1 / 2 : Real) ^ (h - readIndex hp hP C I e) := by
  have a := advance_spec hp hP C I active he
  have before := index_split hp hP C I e
  have after := index_split hp hP C I (advance hp hP C I u active e).1
  rw [a.1] at after
  have bound := budget e.1
  have exp : h - readIndex hp hP C I e =
      (h - readIndex hp hP C I (advance hp hP C I u active e).1) + 1 := by omega
  rw [exp,pow_succ]
  ring


private theorem event_slot_unique {u v : Slot} {x : Source} {t : Nat}
    (hu : C.Occurs I x t u) (hv : C.Occurs I x t v) : u = v :=
  Prod.ext (Subtype.ext (hu.2.1.symm.trans hv.2.1)) (hu.2.2.symm.trans hv.2.2)

private theorem events_disjoint {u v : Slot} (different : u ≠ v) :
    Disjoint (events hp hP C I u) (events hp hP C I v) := by
  apply Finset.disjoint_left.mpr
  intro e he hd
  exact different (event_slot_unique hp hP C I
    ((mem_events hp hP C I).mp he) ((mem_events hp hP C I).mp hd))

private theorem saturated_children (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) (u : Slot)
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt)
    (full : mass hp hP C I h u = 1) :
    ∃ v w : Slot, v ≠ w ∧ C.Edge I u v ∧ C.Edge I u w ∧
      mass hp hP C I h v = 1 ∧ mass hp hP C I h w = 1 ∧
      (∀ z, C.Edge I u z ↔ z = v ∨ z = w) ∧
      (∀ e ∈ events hp hP C I v ∪ events hp hP C I w,
        ∃ d ∈ events hp hP C I u, e.1 = d.1 ∧ d.2 < e.2 ∧
          ∀ t, d.2 < t → t < e.2 → C.action (C.run hp hP d.1 t).2 = .wait) ∧
      (events hp hP C I u).card = (events hp hP C I v).card + (events hp hP C I w).card := by
  classical
  let f := fun e => (advance hp hP C I u active e).1
  let A := (events hp hP C I u).image f
  let weight := fun e => (1 / 2 : Real) ^ (h - readIndex hp hP C I e)
  have positive (e : Source × Nat) : 0 < weight e := by dsimp [weight]; positivity
  have transport : ∑ e ∈ A, weight e = 2 := by
    rw [Finset.sum_image (advance_injective hp hP C I active)]
    calc
      ∑ e ∈ events hp hP C I u, weight (f e) =
          ∑ e ∈ events hp hP C I u, 2 * weight e := by
        apply Finset.sum_congr rfl
        intro e he
        exact advance_weight hp hP C I h budget active he
      _ = 2 * mass hp hP C I h u := by rw [← Finset.mul_sum]; rfl
      _ = 2 := by rw [full]; norm_num
  have nonempty : (events hp hP C I u).Nonempty := by
    by_contra empty
    have zero := Finset.not_nonempty_iff_eq_empty.mp empty
    simp [mass,zero] at full
  obtain ⟨e,he⟩ := nonempty
  obtain ⟨G,root,used,edges,adjacent,rest⟩ := C.result I
  have next_edge (d : Source × Nat) (hd : d ∈ events hp hP C I u) :
      C.Edge I u (advance hp hP C I u active d).2 := by
    have a := advance_spec hp hP C I active hd
    exact ⟨d.1,d.2,_,(mem_events hp hP C I).mp hd,a.2.1,a.2.2.1,a.2.2.2.1⟩
  obtain ⟨q,b,c,cover,neighbor⟩ := adjacent u
    ⟨_,(edges u _).mpr (next_edge e he)⟩
  let v : Slot := (q,b)
  let w : Slot := (q,c)
  have covered (d : Source × Nat) (hd : d ∈ events hp hP C I u) :
      (advance hp hP C I u active d).2 = v ∨
        (advance hp hP C I u active d).2 = w := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,v,w] using
      cover ((edges u _).mpr (next_edge d hd))
  have subset : A ⊆ events hp hP C I v ∪ events hp hP C I w := by
    intro a ha
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    have s := advance_spec hp hP C I active hd
    have realized : C.Occurs I (f d).1 (f d).2 (advance hp hP C I u active d).2 := by
      simpa only [f,s.1] using s.2.1
    rcases covered d hd with eq | eq
    · apply Finset.mem_union_left
      exact (mem_events hp hP C I).mpr (eq ▸ realized)
    · apply Finset.mem_union_right
      exact (mem_events hp hP C I).mpr (eq ▸ realized)
  have lower : 2 ≤ ∑ e ∈ events hp hP C I v ∪ events hp hP C I w, weight e := by
    rw [← transport]
    exact Finset.sum_le_sum_of_subset_of_nonneg subset (fun a _ _ => (positive a).le)
  have different : v ≠ w := by
    intro eq
    rw [eq,Finset.union_self] at lower
    have bound := slot_capacity hp hP C I h budget w
    change (∑ e ∈ events hp hP C I w, weight e) ≤ 1 at bound
    linarith
  have separated := events_disjoint hp hP C I different
  have union_sum : (∑ e ∈ events hp hP C I v ∪ events hp hP C I w, weight e) =
      mass hp hP C I h v + mass hp hP C I h w := Finset.sum_union separated
  have vb := slot_capacity hp hP C I h budget v
  have wb := slot_capacity hp hP C I h budget w
  have vs : mass hp hP C I h v = 1 := by rw [union_sum] at lower; linarith
  have ws : mass hp hP C I h w = 1 := by rw [union_sum] at lower; linarith
  have full_image : A = events hp hP C I v ∪ events hp hP C I w := by
    apply Finset.Subset.antisymm subset
    intro a ha
    by_contra missing
    have strict := Finset.sum_lt_sum_of_subset subset ha missing (positive a)
      (fun b _ _ => (positive b).le)
    rw [transport,union_sum,vs,ws] at strict
    norm_num at strict
  have vnonempty : (events hp hP C I v).Nonempty := by
    by_contra empty
    simp [mass,Finset.not_nonempty_iff_eq_empty.mp empty] at vs
  have wnonempty : (events hp hP C I w).Nonempty := by
    by_contra empty
    simp [mass,Finset.not_nonempty_iff_eq_empty.mp empty] at ws
  have incoming (z : Slot) (hz : z = v ∨ z = w) : C.Edge I u z := by
    have zn : (events hp hP C I z).Nonempty := by rcases hz with rfl | rfl <;> assumption
    obtain ⟨a,ha⟩ := zn
    have hu : a ∈ events hp hP C I v ∪ events hp hP C I w := by
      rcases hz with rfl | rfl
      · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_right _ ha
    rw [← full_image] at hu
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hu
    have old := next_edge d hd
    have s := advance_spec hp hP C I active hd
    have occurs : C.Occurs I (f d).1 (f d).2 (advance hp hP C I u active d).2 := by
      simpa only [f,s.1] using s.2.1
    have eqz := event_slot_unique hp hP C I (eq ▸ occurs)
      ((mem_events hp hP C I).mp ha)
    exact eqz ▸ old
  refine ⟨v,w,different,incoming v (Or.inl rfl),incoming w (Or.inr rfl),vs,ws,?_,?_,?_⟩
  · intro z
    refine ⟨fun hz => ?_, incoming z⟩
    simpa only [Finset.mem_insert,Finset.mem_singleton,v,w] using cover ((edges u z).mpr hz)
  · intro a ha
    rw [← full_image] at ha
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp ha
    have s := advance_spec hp hP C I active hd
    exact ⟨d,hd,by rw [← eq]; exact s.1,
      by rw [← eq]; exact s.2.2.1,by rw [← eq]; exact s.2.2.2.1⟩


  · have cardinal := Finset.card_image_of_injOn (advance_injective hp hP C I active)
    change A.card = (events hp hP C I u).card at cardinal
    rw [full_image,Finset.card_union_of_disjoint separated] at cardinal
    exact cardinal.symm

private theorem index_edge {x : Source} {i j : Nat} {u v : Slot}
    (hu : C.Occurs I x i u) (hv : C.Occurs I x j v) (before : i < j)
    (waits : ∀ t, i < t → t < j → C.action (C.run hp hP x t).2 = .wait) :
    readIndex hp hP C I (x,j) = readIndex hp hP C I (x,i) + 1 := by
  have a := index_split hp hP C I (x,i)
  have b := index_split hp hP C I (x,j)
  have step := later_read_step hp hP C I hu hv before waits
  dsimp only at a b
  omega

private theorem predecessor_unique {u v w : Slot} {x : Source} {i j k : Nat}
    (hu : C.Occurs I x i u) (hv : C.Occurs I x j v)
    (hw : C.Occurs I x k w) (ik : i < k) (jk : j < k)
    (iw : ∀ t, i < t → t < k → C.action (C.run hp hP x t).2 = .wait)
    (jw : ∀ t, j < t → t < k → C.action (C.run hp hP x t).2 = .wait) : u = v := by
  have ij : i = j := by
    obtain ⟨_,_,_,_,_,ur,_⟩ := u.1.property
    obtain ⟨_,_,_,_,_,vr,_⟩ := v.1.property
    rcases lt_trichotomy i j with lt | eq | gt
    · have clash := iw j lt jk
      rw [hv.2.1,vr] at clash
      cases clash
    · exact eq
    · have clash := jw i gt ik
      rw [hu.2.1,ur] at clash
      cases clash
  exact event_slot_unique hp hP C I (ij ▸ hu) hv

/-- Minimum original read index among the complete initialized events of a slot. -/
private noncomputable def rank (u : Slot) : Nat :=
  if hn : ((events hp hP C I u).image (readIndex hp hP C I)).Nonempty then
    ((events hp hP C I u).image (readIndex hp hP C I)).min' hn else 0

private theorem rank_spec {u : Slot} (ne : (events hp hP C I u).Nonempty) :
    (∃ e ∈ events hp hP C I u, readIndex hp hP C I e = rank hp hP C I u) ∧
      ∀ e ∈ events hp hP C I u, rank hp hP C I u ≤ readIndex hp hP C I e := by
  classical
  have hn := ne.image (readIndex hp hP C I)
  simp only [rank,dif_pos hn]
  refine ⟨?_,?_⟩
  · exact Finset.mem_image.mp (Finset.min'_mem _ hn)
  · intro e he
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)

private theorem mass_nonempty (h : Nat) {u : Slot} (full : mass hp hP C I h u = 1) :
    (events hp hP C I u).Nonempty := by
  by_contra empty
  simp [mass,Finset.not_nonempty_iff_eq_empty.mp empty] at full

private theorem full_edge (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u v : Slot}
    (full : mass hp hP C I h u = 1) (edge : C.Edge I u v) :
    mass hp hP C I h v = 1 ∧ rank hp hP C I u < rank hp hP C I v ∧
      ∀ z, C.Edge I z v → z = u := by
  have active : C.action (C.readNext u.1.val u.2) ≠ .halt := by
    intro halt
    exact terminal_no_edge hp hP C I halt edge
  obtain ⟨l,r,ne,el,er,lf,rf,exhaustive,complete,balance⟩ :=
    saturated_children hp hP C I h budget u active full
  have choice := (exhaustive v).mp edge
  have vf : mass hp hP C I h v = 1 := by rcases choice with rfl | rfl <;> assumption
  have cover (e : Source × Nat) (he : e ∈ events hp hP C I v) :
      ∃ d ∈ events hp hP C I u, e.1 = d.1 ∧ d.2 < e.2 ∧
        ∀ t, d.2 < t → t < e.2 → C.action (C.run hp hP d.1 t).2 = .wait := by
    apply complete e
    rcases choice with rfl | rfl
    · exact Finset.mem_union_left _ he
    · exact Finset.mem_union_right _ he
  refine ⟨vf,?_,?_⟩
  · obtain ⟨e,he,min⟩ := (rank_spec hp hP C I (mass_nonempty hp hP C I h vf)).1
    obtain ⟨d,hd,xy,before,waits⟩ := cover e he
    have step := index_edge hp hP C I ((mem_events hp hP C I).mp hd)
      (xy ▸ (mem_events hp hP C I).mp he) before waits
    have bound := (rank_spec hp hP C I (mass_nonempty hp hP C I h full)).2 d hd
    have same : readIndex hp hP C I (d.1,e.2) = readIndex hp hP C I e := by
      cases e; cases d; simp_all
    change readIndex hp hP C I (d.1,e.2) = readIndex hp hP C I d + 1 at step
    rw [same,min] at step
    omega
  · intro z hz
    obtain ⟨x,i,j,hi,hj,before,waits⟩ := hz
    obtain ⟨d,hd,xy,before',waits'⟩ := cover (x,j) ((mem_events hp hP C I).mpr hj)
    have dx : d.1 = x := xy.symm
    apply predecessor_unique hp hP C I hi (dx ▸ (mem_events hp hP C I).mp hd)
      hj before before'
      waits
    simpa only [dx] using waits'

private theorem reachable_full (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u v : Slot}
    (full : mass hp hP C I h u = 1) (path : Relation.ReflTransGen (C.Edge I) u v) :
    mass hp hP C I h v = 1 := by
  induction path with
  | refl => exact full
  | tail before edge ih => exact (full_edge hp hP C I h budget ih edge).1

private theorem path_rank (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u v : Slot}
    (path : Relation.TransGen (C.Edge I) u v) (full : mass hp hP C I h u = 1) :
    rank hp hP C I u < rank hp hP C I v := by
  induction path with
  | single edge => exact (full_edge hp hP C I h budget full edge).2.1
  | @tail v w path edge ih =>
    have vf := reachable_full hp hP C I h budget full path.to_reflTransGen
    exact ih.trans ((full_edge hp hP C I h budget vf edge).2.1)


private theorem future_reaches (G : SlotGraph p {q : Q // ∃ b, C.Used I q b})
    {u v : Slot} {x : Source} {t j : Nat} {word : List (Fin 2)}
    (path : FutureWord hp hP C I G u x t word) (later : C.Occurs I x j v)
    (before : t < j) : Relation.TransGen (C.Edge I) u v := by
  induction path generalizing v j with
  | stop occurs halt =>
    have last := (terminal_end hp hP C I occurs halt).2
    have bound := later.1
    omega
  | @next u w x t k word occurs child tk waits edge tail ih =>
    have kj : k ≤ j := by
      by_contra bad
      have clash := waits j before (by omega)
      obtain ⟨_,_,_,_,_,vr,_⟩ := v.1.property
      rw [later.2.1,vr] at clash
      cases clash
    have actual : C.Edge I u w := ⟨x,t,k,occurs,child,tk,waits⟩
    by_cases eq : k = j
    · have same := event_slot_unique hp hP C I (eq ▸ child) later
      exact same ▸ Relation.TransGen.single actual
    · exact Relation.TransGen.head actual (ih later (by omega))

private theorem saturated_originals (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u : Slot}
    (full : mass hp hP C I h u = 1) :
    Set.InjOn Prod.fst (events hp hP C I u : Set (Source × Nat)) := by
  intro e he d hd same
  have hu := (mem_events hp hP C I).mp he
  have hv := (mem_events hp hP C I).mp hd
  have source : e.1 = d.1 := same
  obtain ⟨G,root,used,edges,rest⟩ := C.result I
  have no_return (x : Source) (i j : Nat) (hi : C.Occurs I x i u)
      (hj : C.Occurs I x j u) (before : i < j) : False := by
    obtain ⟨word,path,length⟩ := future_exists hp hP C I G edges
      (laterReads hp hP C I x i).card u x i hi le_rfl
    have loop := future_reaches hp hP C I G path hj before
    exact Nat.lt_irrefl _ (path_rank hp hP C I h budget loop full)
  apply Prod.ext source
  rcases lt_trichotomy e.2 d.2 with lt | eq | gt
  · exact False.elim (no_return d.1 e.2 d.2 (source ▸ hu) hv lt)
  · exact eq
  · exact False.elim (no_return e.1 d.2 e.2 (source.symm ▸ hv) hu gt)

private theorem same_target (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) (small : p ≤ 3)
    {u z v w : Slot} (uf : mass hp hP C I h u = 1) (zf : mass hp hP C I h z = 1)
    (uv : C.Edge I u v) (zw : C.Edge I z w) (target : v.1 = w.1) : u = z := by
  classical
  have ua : C.action (C.readNext u.1.val u.2) ≠ .halt :=
    fun halt => terminal_no_edge hp hP C I halt uv
  have za : C.action (C.readNext z.1.val z.2) ≠ .halt :=
    fun halt => terminal_no_edge hp hP C I halt zw
  obtain ⟨a,b,ab,ua',ub,af,bf,ex,comp,balance⟩ := saturated_children hp hP C I h budget u ua uf
  obtain ⟨c,d,cd,zc,zd,cf,df,ex',comp',balance'⟩ := saturated_children hp hP C I h budget z za zf
  have ac : a.1 = c.1 := (C.edge_target_unique I ua' uv).trans
    (target.trans (C.edge_target_unique I zw zc))
  have abq := C.edge_target_unique I ua' ub
  have cdq := C.edge_target_unique I zc zd
  have abdigit : a.2 ≠ b.2 := fun eq => ab (Prod.ext abq eq)
  have cddigit : c.2 ≠ d.2 := fun eq => cd (Prod.ext cdq eq)
  have common : (({a.2,b.2} : Finset (Fin p)) ∩ {c.2,d.2}).Nonempty := by
    apply Finset.inter_nonempty_of_card_lt_card_add_card
      (s := Finset.univ) (Finset.subset_univ _) (Finset.subset_univ _)
    simp only [Finset.card_univ,Fintype.card_fin,Finset.card_pair abdigit,
      Finset.card_pair cddigit]
    omega
  obtain ⟨digit,mem⟩ := common
  obtain ⟨ld,rd⟩ := Finset.mem_inter.mp mem
  let child : Slot := (a.1,digit)
  have left : child = a ∨ child = b := by
    rcases Finset.mem_insert.mp ld with eq | eq
    · exact Or.inl (Prod.ext rfl eq)
    · exact Or.inr (Prod.ext abq (Finset.mem_singleton.mp eq))
  have right : child = c ∨ child = d := by
    rcases Finset.mem_insert.mp rd with eq | eq
    · exact Or.inl (Prod.ext ac eq)
    · exact Or.inr (Prod.ext (ac.trans cdq) (Finset.mem_singleton.mp eq))
  have uc := (ex child).mpr left
  have zchild := (ex' child).mpr right
  exact ((full_edge hp hP C I h budget uf uc).2.2 z zchild).symm

private theorem saturated_card (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u : Slot}
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt)
    (full : mass hp hP C I h u = 1) : 2 ≤ (events hp hP C I u).card := by
  classical
  have bound (e : Source × Nat) (he : e ∈ events hp hP C I u) :
      (1 / 2 : Real) ^ (h - readIndex hp hP C I e) ≤ 1 / 2 := by
    have a := advance_spec hp hP C I active he
    have b := index_split hp hP C I e
    have c := budget e.1
    exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have upper : mass hp hP C I h u ≤ ((events hp hP C I u).card : Real) * (1 / 2) := by
    calc
      _ ≤ ∑ _e ∈ events hp hP C I u, (1 / 2 : Real) := Finset.sum_le_sum bound
      _ = _ := by simp
  rw [full] at upper
  have lower : (2 : Real) ≤ (events hp hP C I u).card := by linarith
  exact_mod_cast lower


private theorem literal_interval {u v : Slot} {x : Source} {i j : Nat}
    (hi : C.Occurs I x i u) (hj : C.Occurs I x j v) (before : i < j)
    (waits : ∀ t, i < t → t < j → C.action (C.run hp hP x t).2 = .wait) :
    let d := j - (i + 1)
    0 < d ∧ j = i + 1 + d ∧
      (∀ n, n < d → C.action (C.waitNext^[n] (C.readNext u.1.val u.2)) = .wait) ∧
      C.waitNext^[d] (C.readNext u.1.val u.2) = v.1.val := by
  obtain ⟨_,_,_,_,_,ur,_⟩ := u.1.property
  obtain ⟨_,_,_,_,_,vr,_⟩ := v.1.property
  have read := C.read_advance (hi.2.1 ▸ ur)
  have live := hj.1
  have strict : i + 1 < j := by
    by_contra bad
    have ij : j = i + 1 := by omega
    have after := I.after_read x i (by omega) (hi.2.1 ▸ ur)
    rw [← ij,hj.2.1,vr] at after
    cases after
  let d := j - (i + 1)
  have endtime : j = i + 1 + d := by dsimp [d]; omega
  have positions (n : Nat) (hn : n ≤ d) :
      (C.run hp hP x (i + 1 + n)).2 = C.waitNext^[n] (C.readNext u.1.val u.2) := by
    have segment := C.wait_segment (hp := hp) (hP := hP) x (i + 1) n
      (fun k hk => waits _ (by omega) (by omega))
    rw [read] at segment
    exact congrArg Prod.snd segment |>.trans (by rw [hi.2.1,hi.2.2])
  refine ⟨by omega,endtime,?_,?_⟩
  · intro n hn
    rw [← positions n hn.le]
    exact waits _ (by omega) (by omega)
  · rw [← positions d le_rfl,← endtime]
    exact hj.2.1

private theorem literal_transport (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) (u : Slot)
    (active : C.action (C.readNext u.1.val u.2) ≠ .halt)
    (full : mass hp hP C I h u = 1) :
    ∃ v w : Slot, ∃ delay : Nat, v ≠ w ∧ 0 < delay ∧
      C.Edge I u v ∧ C.Edge I u w ∧ mass hp hP C I h v = 1 ∧ mass hp hP C I h w = 1 ∧
      (∀ z, C.Edge I u z ↔ z = v ∨ z = w) ∧
      (∀ e ∈ events hp hP C I v ∪ events hp hP C I w,
        ∃ d ∈ events hp hP C I u, e.1 = d.1 ∧ e.2 = d.2 + 1 + delay ∧
          ∀ t, d.2 < t → t < e.2 → C.action (C.run hp hP d.1 t).2 = .wait) := by
  obtain ⟨v,w,ne,uv,uw,vf,wf,ex,complete,balance⟩ :=
    saturated_children hp hP C I h budget u active full
  obtain ⟨x,i,delay,hi,pos,endpoint,digit,waits,control,physical⟩ := C.edge_tail I uv
  refine ⟨v,w,delay,ne,pos,uv,uw,vf,wf,ex,?_⟩
  intro e he
  obtain ⟨d,hd,xy,before,actual⟩ := complete e he
  have ev : C.Occurs I d.1 e.2 v ∨ C.Occurs I d.1 e.2 w := by
    rcases Finset.mem_union.mp he with he | he
    · exact Or.inl (xy ▸ (mem_events hp hP C I).mp he)
    · exact Or.inr (xy ▸ (mem_events hp hP C I).mp he)
  have fixed (z : Slot) (ev : C.Occurs I d.1 e.2 z) : e.2 = d.2 + 1 + delay := by
    have interval := literal_interval hp hP C I ((mem_events hp hP C I).mp hd)
      ev before actual
    obtain ⟨_,_,_,_,_,read,_⟩ := z.1.property
    obtain ⟨_,_,_,_,_,vread,_⟩ := v.1.property
    have same := C.tail_unique interval.2.2.1 waits
      (interval.2.2.2 ▸ read) (control ▸ vread)
    rw [← same]
    exact interval.2.1
  exact ⟨d,hd,xy,ev.elim (fixed v) (fixed w),actual⟩

private theorem terminal_deadline (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u : Slot}
    (full : mass hp hP C I h u = 1)
    (halt : C.action (C.readNext u.1.val u.2) = .halt) :
    ∃ e : Source × Nat, events hp hP C I u = {e} ∧
      readIndex hp hP C I e = h ∧ e.2 + 1 = I.length e.1 := by
  classical
  obtain ⟨e,he⟩ := mass_nonempty hp hP C I h full
  have end' := terminal_end hp hP C I ((mem_events hp hP C I).mp he) halt
  have singleton : events hp hP C I u = {e} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨he,?_⟩
    intro d hd
    have other := terminal_end hp hP C I ((mem_events hp hP C I).mp hd) halt
    have xy : d.1 = e.1 := other.1.symm.trans end'.1
    apply Prod.ext xy
    rw [xy] at other
    omega
  have mass' : (1 / 2 : Real) ^ (h - readIndex hp hP C I e) = 1 := by
    simpa only [mass,singleton,Finset.sum_singleton] using full
  have zero : h - readIndex hp hP C I e = 0 := by
    by_contra nonzero
    have strict : (1 / 2 : Real) ^ (h - readIndex hp hP C I e) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) nonzero
    linarith
  have split := index_split hp hP C I e
  have bound := budget e.1
  exact ⟨e,singleton,by omega,end'.2⟩

private theorem target_nonroot {u v : Slot} (edge : C.Edge I u v) : v.1.val ≠ C.initial := by
  classical
  obtain ⟨G,root,used,edges,rest⟩ := C.result I
  intro same
  have eq : v.1 = G.root := Subtype.ext (same.trans root.symm)
  have entry := (edges u v).mpr edge
  have forbidden := G.root_no_incoming u v.2
  exact forbidden (by simpa only [← eq,Prod.eta] using entry)

private theorem saturated_budget (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u : Slot}
    (full : mass hp hP C I h u = 1) :
    ∀ e ∈ events hp hP C I u, (readEvents hp hP C I e.1).card = h := by
  classical
  by_cases active : C.action (C.readNext u.1.val u.2) ≠ .halt
  · obtain ⟨G,root,used,edges,rest⟩ := C.result I
    have upper := suffix_kraft hp hP C I G edges u active
    have termwise : ∀ e ∈ events hp hP C I u,
        (1 / 2 : Real) ^ (h - readIndex hp hP C I e) ≤
          (1 / 2 : Real) ^ (laterReads hp hP C I e.1 e.2).card := by
      intro e he
      have split := index_split hp hP C I e
      have bound := budget e.1
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have equality : (∑ e ∈ events hp hP C I u,
        (1 / 2 : Real) ^ (h - readIndex hp hP C I e)) =
      ∑ e ∈ events hp hP C I u, (1 / 2 : Real) ^ (laterReads hp hP C I e.1 e.2).card := by
      have lower := Finset.sum_le_sum termwise
      change mass hp hP C I h u ≤ _ at lower
      change mass hp hP C I h u = _
      rw [full] at lower ⊢
      linarith
    intro e he
    have point := (Finset.sum_eq_sum_iff_of_le termwise).mp equality e he
    have exponents := (pow_right_strictAnti₀ (by norm_num : (0 : Real) < 1 / 2)
      (by norm_num : (1 / 2 : Real) < 1)).injective point
    have split := index_split hp hP C I e
    have bound := budget e.1
    omega
  · have halt := not_ne_iff.mp active
    obtain ⟨d,singleton,index,last⟩ := terminal_deadline hp hP C I h budget full halt
    intro e he
    have eq := Finset.mem_singleton.mp (singleton ▸ he)
    subst e
    have split := index_split hp hP C I d
    have empty : laterReads hp hP C I d.1 d.2 = ∅ := by
      ext t
      simp only [laterReads,Finset.mem_filter,Finset.mem_range,Finset.notMem_empty,iff_false,not_and]
      omega
    rw [empty,Finset.card_empty,index] at split
    omega

/-- A full binary expansion of the complete actual successor relation.
Leaves retain their entire singleton event fiber; forks retain both actual
edges, the exhaustive successor list and the exact event-count balance. -/
inductive ConeTree : Slot → Type where
  | leaf {u : Slot} (e : Source × Nat)
      (events_eq : events hp hP C I u = {e})
      (halt : C.action (C.readNext u.1.val u.2) = .halt) : ConeTree u
  | fork {u l r : Slot} (different : l ≠ r) (left_edge : C.Edge I u l)
      (right_edge : C.Edge I u r) (exhaustive : ∀ z, C.Edge I u z ↔ z = l ∨ z = r)
      (balance : (events hp hP C I u).card =
        (events hp hP C I l).card + (events hp hP C I r).card)
      (left : ConeTree l) (right : ConeTree r) : ConeTree u

def leafCount {u : Slot} : ConeTree hp hP C I u → Nat
  | .leaf _ _ _ => 1
  | .fork _ _ _ _ _ left right => leafCount left + leafCount right

def internalCount {u : Slot} : ConeTree hp hP C I u → Nat
  | .leaf _ _ _ => 0
  | .fork _ _ _ _ _ left right => 1 + internalCount left + internalCount right

private theorem rank_le (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u : Slot}
    (full : mass hp hP C I h u = 1) : rank hp hP C I u ≤ h := by
  obtain ⟨e,he,min⟩ := (rank_spec hp hP C I (mass_nonempty hp hP C I h full)).1
  have split := index_split hp hP C I e
  have bound := budget e.1
  omega

private theorem cone_tree_exists (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) {u : Slot}
    (full : mass hp hP C I h u = 1) : Nonempty (ConeTree hp hP C I u) := by
  have construct : ∀ n v, mass hp hP C I h v = 1 → h - rank hp hP C I v = n →
      Nonempty (ConeTree hp hP C I v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v vf measure
      by_cases halt : C.action (C.readNext v.1.val v.2) = .halt
      · obtain ⟨e,singleton,index,last⟩ := terminal_deadline hp hP C I h budget vf halt
        exact ⟨.leaf e singleton halt⟩
      · obtain ⟨l,r,ne,vl,vr,lf,rf,ex,complete,balance⟩ :=
          saturated_children hp hP C I h budget v halt vf
        have ls := (full_edge hp hP C I h budget vf vl).2.1
        have rs := (full_edge hp hP C I h budget vf vr).2.1
        have lb := rank_le hp hP C I h budget lf
        have rb := rank_le hp hP C I h budget rf
        obtain ⟨L⟩ := ih (h - rank hp hP C I l) (by omega) l lf rfl
        obtain ⟨R⟩ := ih (h - rank hp hP C I r) (by omega) r rf rfl
        exact ⟨.fork ne vl vr ex balance L R⟩
  exact construct _ u full rfl

private def treeShape {u : Slot} : ConeTree hp hP C I u → BinaryTree Unit
  | .leaf _ _ _ => .nil
  | .fork _ _ _ _ _ left right => .node () (treeShape left) (treeShape right)

private theorem tree_counts {u : Slot} (T : ConeTree hp hP C I u) :
    leafCount hp hP C I T = (events hp hP C I u).card ∧
      internalCount hp hP C I T + 1 = leafCount hp hP C I T := by
  have counts : leafCount hp hP C I T = (treeShape hp hP C I T).numLeaves ∧
      internalCount hp hP C I T = (treeShape hp hP C I T).numNodes := by
    induction T with
    | leaf e singleton halt => simp [leafCount,internalCount,treeShape]
    | fork ne left_edge right_edge exhaustive balance left right ihl ihr =>
      simp only [leafCount,internalCount,treeShape,BinaryTree.numLeaves,BinaryTree.numNodes]
      exact ⟨by rw [ihl.1,ihr.1],by rw [ihl.2,ihr.2]; omega⟩
  refine ⟨?_,?_⟩
  · clear counts
    induction T with
    | leaf e singleton halt => simp [leafCount,singleton]
    | fork ne left_edge right_edge exhaustive balance left right ihl ihr =>
      simp only [leafCount]
      rw [ihl,ihr,← balance]
  · rw [counts.1,counts.2]
    exact (BinaryTree.numLeaves_eq_numNodes_succ (treeShape hp hP C I T)).symm

/-- A saturated actual cone has complete child fibers, unique incoming edges,
no slot cycle, and distinct next-reading controls when p is two or three. -/
theorem result (h : Nat)
    (budget : ∀ x, (readEvents hp hP C I x).card ≤ h) (small : p ≤ 3)
    (u : Slot) (active : C.action (C.readNext u.1.val u.2) ≠ .halt)
    (full : mass hp hP C I h u = 1) :
    2 ≤ (events hp hP C I u).card ∧
    (∀ v, Relation.ReflTransGen (C.Edge I) u v →
      mass hp hP C I h v = 1 ∧
      (∀ e ∈ events hp hP C I v, (readEvents hp hP C I e.1).card = h) ∧
      Set.InjOn Prod.fst (events hp hP C I v : Set (Source × Nat)) ∧
      ¬ Relation.TransGen (C.Edge I) v v ∧
      (C.action (C.readNext v.1.val v.2) = .halt →
        ∃ e : Source × Nat, events hp hP C I v = {e} ∧
          readIndex hp hP C I e = h ∧ e.2 + 1 = I.length e.1) ∧
      (C.action (C.readNext v.1.val v.2) ≠ .halt →
        ∃ l r : Slot, ∃ delay : Nat, l ≠ r ∧ 0 < delay ∧ C.Edge I v l ∧ C.Edge I v r ∧
          mass hp hP C I h l = 1 ∧ mass hp hP C I h r = 1 ∧
          (∀ z, C.Edge I v z ↔ z = l ∨ z = r) ∧
          (∀ e ∈ events hp hP C I l ∪ events hp hP C I r,
            ∃ d ∈ events hp hP C I v, e.1 = d.1 ∧ e.2 = d.2 + 1 + delay ∧
              ∀ t, d.2 < t → t < e.2 → C.action (C.run hp hP d.1 t).2 = .wait)) ∧
      (∀ w, C.Edge I v w → (∀ z, C.Edge I z w → z = v) ∧ w.1.val ≠ C.initial)) ∧
    (∀ v w a b, Relation.ReflTransGen (C.Edge I) u v →
      Relation.ReflTransGen (C.Edge I) u w → C.Edge I v a → C.Edge I w b →
      a.1 = b.1 → v = w) ∧
    (∃ T : ConeTree hp hP C I u, leafCount hp hP C I T = (events hp hP C I u).card ∧
      internalCount hp hP C I T + 1 = leafCount hp hP C I T) := by
  refine ⟨saturated_card hp hP C I h budget active full,?_,?_,?_⟩
  · intro v path
    have vf := reachable_full hp hP C I h budget full path
    refine ⟨vf,saturated_budget hp hP C I h budget vf,
      saturated_originals hp hP C I h budget vf,?_,terminal_deadline hp hP C I h budget vf,
      (fun va => literal_transport hp hP C I h budget v va vf),?_⟩
    · intro loop
      have strict := path_rank hp hP C I h budget loop vf
      exact Nat.lt_irrefl _ strict
    · intro w edge
      exact ⟨(full_edge hp hP C I h budget vf edge).2.2,
        target_nonroot hp hP C I edge⟩
  · intro v w a b vp wp va wb eq
    exact same_target hp hP C I h budget small
      (reachable_full hp hP C I h budget full vp)
      (reachable_full hp hP C I h budget full wp) va wb eq
  · obtain ⟨T⟩ := cone_tree_exists hp hP C I h budget full
    exact ⟨T,tree_counts hp hP C I T⟩

end D5.S3.ObserverMemory.Algorithms.SaturatedActualCone
