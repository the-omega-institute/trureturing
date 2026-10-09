/- GID: D5/S3/ObserverMemory/Algorithms/SaturatedActualCone
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SaturatedActualCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete actual event fibers and their saturated successor transport. -/

import D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
import D5.S0.Computability.Coding.PrefixFreeCode

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
          ∀ t, d.2 < t → t < e.2 → C.action (C.run hp hP d.1 t).2 = .wait) := by
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
  refine ⟨v,w,different,incoming v (Or.inl rfl),incoming w (Or.inr rfl),vs,ws,?_,?_⟩
  · intro z
    refine ⟨fun hz => ?_, incoming z⟩
    simpa only [Finset.mem_insert,Finset.mem_singleton,v,w] using cover ((edges u z).mpr hz)
  · intro a ha
    rw [← full_image] at ha
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp ha
    have s := advance_spec hp hP C I active hd
    exact ⟨d,hd,by rw [← eq]; exact s.1,
      by rw [← eq]; exact s.2.2.1,by rw [← eq]; exact s.2.2.2.1⟩

end D5.S3.ObserverMemory.Algorithms.SaturatedActualCone
