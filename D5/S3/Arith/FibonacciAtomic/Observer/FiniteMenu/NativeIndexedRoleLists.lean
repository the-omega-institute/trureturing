/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeIndexedRoleLists
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Deterministic exact capped native languages for indexed role constraints. -/

import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeBooleanAssignmentBanks
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeClassRootImage (Image)
open NativeBooleanAssignmentBanks (B B_height pad_preimage dToNative)
open SourceCoordinates.IntrinsicSubstitutionCoordinates (pair_image no_alpha)

/-- These are whole-source types, distinct from the two Boolean leaf labels. -/
inductive Kind | A | H | I | O
  deriving DecidableEq, Repr

/-- Fixed original type order. -/
def kinds : List Kind := [.A,.H,.I,.O]

/-- Exactly the five original ordered image alternatives. -/
def parent : Kind → Kind → Kind
  | .H,.A | .H,.H | .H,.I | .I,.H | .I,.I => .I
  | _,_ => .O

/-- A computable classifier on actual finite nonempty ordered terms. -/
def kind : Source → Kind
  | .of true => .A
  | .of false => .H
  | .mul s t => parent (kind s) (kind t)

/-- The original four classes, using the original substitution image. -/
def Class : Kind → Source → Prop
  | .A,t => t = .of true
  | .H,t => t = .of false
  | .I,t => Image t ∧ t ≠ .of false
  | .O,t => t ≠ .of true ∧ t ≠ .of false ∧ ¬ Image t

private theorem kind_A (t : Source) : kind t = .A ↔ t = .of true := by
  cases t with
  | of b => cases b <;> decide
  | mul s t => cases hs : kind s <;> cases ht : kind t <;> simp [kind,hs,ht,parent]

private theorem kind_H (t : Source) : kind t = .H ↔ t = .of false := by
  cases t with
  | of b => cases b <;> decide
  | mul s t => cases hs : kind s <;> cases ht : kind t <;> simp [kind,hs,ht,parent]

private theorem kind_image (t : Source) : Image t ↔ kind t = .H ∨ kind t = .I := by
  induction t with
  | of b =>
    cases b with
    | false => exact ⟨fun _ => Or.inl rfl,fun _ => ⟨.of true,rfl⟩⟩
    | true =>
      constructor
      · rintro ⟨u,h⟩; exact (no_alpha u h).elim
      · intro h; cases h <;> contradiction
  | mul s t ihs iht =>
    change (∃ u, substitution u = .mul s t) ↔ _
    rw [pair_image]
    change ((s = .of false ∧ t = .of true) ∨ (Image s ∧ Image t)) ↔ _
    rw [← kind_H s,← kind_A t,ihs,iht]
    cases hs : kind s <;> cases ht : kind t <;> simp [kind,hs,ht,parent]

private theorem class_kind (t : Source) (k : Kind) : Class k t ↔ kind t = k := by
  cases k with
  | A => exact (kind_A t).symm
  | H => exact (kind_H t).symm
  | I =>
    change (Image t ∧ t ≠ .of false) ↔ _
    simp only [ne_eq,kind_image,← kind_H t]
    cases kind t <;> simp
  | O =>
    change (t ≠ .of true ∧ t ≠ .of false ∧ ¬ Image t) ↔ _
    simp only [ne_eq,← kind_A t,← kind_H t,kind_image]
    cases kind t <;> simp

/-- Concrete unconstrained witnesses, in the original prescribed order. -/
def basis : Kind → List Source
  | .A => [.of true]
  | .H => [.of false]
  | .I => (List.range 6).map (fun i => B (i+1))
  | .O => (List.range 6).map (fun i => .mul (.of true) (B (i+1)))

/-- A list is sound and, unless saturated, contains the whole language. -/
structure Exact (L : List Source) (K : Set Source) : Prop where
  nodup : L.Nodup
  bound : L.length ≤ 6
  sound : ∀ t ∈ L, t ∈ K
  complete : L.length < 6 → ∀ t ∈ K, t ∈ L

private theorem basis_exact (k : Kind) : Exact (basis k) {t | kind t = k} := by
  have bi (i : Nat) (hi : i < 6) : kind (B (i+1)) = .I := by
    have image : Image (B (i+1)) := ⟨_,pad_preimage (i+1)⟩
    have nb : B (i+1) ≠ .of false := by
      intro h
      have hh := congrArg ActualImageAddressCertificate.height h
      rw [B_height] at hh
      change i+1 = 0 at hh
      omega
    exact (class_kind _ .I).mp ⟨image,nb⟩
  have injectiveB : Function.Injective (fun i : Nat => B (i+1)) := by
    intro i j h
    have hh := congrArg ActualImageAddressCertificate.height h
    simpa only [B_height,Nat.add_right_cancel_iff] using hh
  cases k with
  | A => exact ⟨by simp [basis],by simp [basis],by simp [basis,kind],by
      intro _ t ht; simpa [basis] using (kind_A t).mp ht⟩
  | H => exact ⟨by simp [basis],by simp [basis],by simp [basis,kind],by
      intro _ t ht; simpa [basis] using (kind_H t).mp ht⟩
  | I =>
    refine ⟨(List.nodup_range (n := 6)).map injectiveB,by simp [basis],?_,by simp [basis]⟩
    intro t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    exact bi i (List.mem_range.mp hi)
  | O =>
    have inj : Function.Injective (fun i : Nat => FreeMagma.mul (.of true) (B (i+1))) := by
      intro i j h
      apply injectiveB
      injection h
    refine ⟨(List.nodup_range (n := 6)).map inj,by simp [basis],?_,by simp [basis]⟩
    intro t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ht
    simp [kind,parent]

private theorem exact_nonempty {L : List Source} {K : Set Source}
    (h : Exact L K) {t : Source} (ht : t ∈ K) : ∃ x, x ∈ L := by
  by_cases hn : L = []
  · have mem := h.complete (by simp [hn]) t ht
    simp [hn] at mem
  · exact List.exists_mem_of_ne_nil L hn

private theorem length_le_of_injective {L C : List Source} (hL : L.Nodup)
    (f : Source → Source) (hf : Function.Injective f)
    (hm : ∀ x ∈ L, f x ∈ C) : L.length ≤ C.dedup.length := by
  have sub : (L.map f).toFinset ⊆ C.toFinset := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    exact List.mem_toFinset.mpr (hm x hx)
  have h := Finset.card_le_card sub
  simpa only [List.toFinset_card_of_nodup (hL.map hf),List.card_toFinset,List.length_map] using h

private theorem exact_card {L : List Source} {K : Set Source} (h : Exact L K) :
    (L.length : ENat) = min 6 K.encard := by
  have count : (L.toFinset : Set Source).encard = (L.length : ENat) := by
    rw [Set.encard_coe_eq_coe_finsetCard,List.toFinset_card_of_nodup h.nodup]
  have sub : (L.toFinset : Set Source) ⊆ K := by
    intro t ht; exact h.sound t (List.mem_toFinset.mp ht)
  by_cases small : L.length < 6
  · have eq : (L.toFinset : Set Source) = K := by
      ext t
      exact ⟨fun ht => sub ht,fun ht => List.mem_toFinset.mpr (h.complete small t ht)⟩
    rw [← eq,count,min_eq_right (by exact_mod_cast h.bound)]
  · have full : L.length = 6 := by have := h.bound; omega
    have lower : (6 : ENat) ≤ K.encard := by
      simpa only [count,full,Nat.cast_ofNat] using Set.encard_mono sub
    rw [min_eq_left lower,full]
    norm_num

/-- One original installed long Read, retaining its individual index. -/
structure Constraint where
  index : Nat
  role : Fin 6
  suffix : Address
  reply : Reply
  deriving DecidableEq

/-- Every index for this role is imposed, including equal suffixes. -/
def Compatible (R : List Constraint) (d : Fin 6) (t : Source) : Prop :=
  ∀ c ∈ R, c.role = d → readout c.suffix t = c.reply

/-- The exact native language; it can be empty or infinite. -/
def language (R : List Constraint) (d : Fin 6) (k : Kind) : Set Source :=
  {t | kind t = k ∧ Compatible R d t}

/-- Testing a concrete candidate uses only its finitely many native readouts. -/
def test (R : List Constraint) (d : Fin 6) (t : Source) : Bool :=
  R.all (fun c => decide (c.role = d → readout c.suffix t = c.reply))

/-- Only ending role indices constrain whether this root may be a branch. -/
def branchOK (R : List Constraint) (d : Fin 6) : Bool :=
  R.all (fun c => decide (c.role = d → c.suffix = [] → c.reply = .branch))

/-- Restore the incoming edge without changing index, role or requested reply. -/
def shift (b : Bool) (c : Constraint) : Constraint :=
  {c with suffix := b :: c.suffix}

/-- One trie edge, retaining every matching record in its original order. -/
def child (b : Bool) (R : List Constraint) : List Constraint :=
  R.filterMap (fun c => match c.suffix with
    | [] => none
    | a :: v => if a = b then some {c with suffix := v} else none)

private theorem mem_child (b : Bool) (R : List Constraint) (q : Constraint) :
    q ∈ child b R ↔ shift b q ∈ R := by
  unfold child
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨c,hc,h⟩
    cases c with
    | mk i d v r =>
      cases v with
      | nil => simp at h
      | cons a v =>
        dsimp at h
        split_ifs at h with hab
        · subst a
          cases h
          exact hc
  · intro h
    exact ⟨shift b q,h,by simp [shift]⟩

private theorem test_iff (R : List Constraint) (d : Fin 6) (t : Source) :
    test R d t = true ↔ Compatible R d t := by
  simp only [test,List.all_eq_true,decide_eq_true_eq,Compatible]

private theorem compatible_mul (R : List Constraint) (d : Fin 6) (l r : Source) :
    Compatible R d (.mul l r) ↔ branchOK R d = true ∧
      Compatible (child false R) d l ∧ Compatible (child true R) d r := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · apply List.all_eq_true.mpr
      intro c hc
      apply decide_eq_true
      intro hd hv
      have atRoot := h c hc hd
      simpa [hv,readout] using atRoot.symm
    · intro c hc hd
      have atChild := h (shift false c) ((mem_child false R c).mp hc) hd
      simpa only [shift,readout] using atChild
    · intro c hc hd
      have atChild := h (shift true c) ((mem_child true R c).mp hc) hd
      simpa only [shift,readout] using atChild
  · rintro ⟨root,left,right⟩ c hc hd
    cases hv : c.suffix with
    | nil =>
      have hr := of_decide_eq_true (List.all_eq_true.mp root c hc)
      simpa [hv,readout] using (hr hd hv).symm
    | cons b v =>
      let q : Constraint := {c with suffix := v}
      have hq : q ∈ child b R := (mem_child b R q).mpr (by
        have eq : shift b q = c := by cases c; simp_all [shift,q]
        rwa [eq])
      cases b with
      | false => simpa [hv,readout,q] using left q hq hd
      | true => simpa [hv,readout,q] using right q hq hd

/-- Sixteen ordered alternatives, with concrete child-list order fixed. -/
def pairs (k : Kind) (L G : Kind → List Source) : List Source :=
  kinds.flatMap fun u => kinds.flatMap fun v =>
    if parent u v = k then
      (L u).flatMap (fun l => (G v).map (fun r => .mul l r)) else []

private theorem mem_kinds (k : Kind) : k ∈ kinds := by cases k <;> simp [kinds]

private theorem mem_pairs (k : Kind) (L G : Kind → List Source) (t : Source) :
    t ∈ pairs k L G ↔ ∃ u v, parent u v = k ∧
      ∃ l ∈ L u, ∃ r ∈ G v, .mul l r = t := by
  constructor
  · intro ht
    obtain ⟨u,_,hu⟩ := List.mem_flatMap.mp ht
    obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hu
    by_cases hp : parent u v = k
    · rw [if_pos hp] at hv
      obtain ⟨l,hl,hm⟩ := List.mem_flatMap.mp hv
      obtain ⟨r,hr,ht⟩ := List.mem_map.mp hm
      exact ⟨u,v,hp,l,hl,r,hr,ht⟩
    · simp [hp] at hv
  · rintro ⟨u,v,hp,l,hl,r,hr,ht⟩
    apply List.mem_flatMap.mpr
    refine ⟨u,mem_kinds u,List.mem_flatMap.mpr ⟨v,mem_kinds v,?_⟩⟩
    rw [if_pos hp]
    exact List.mem_flatMap.mpr ⟨l,hl,List.mem_map.mpr ⟨r,hr,ht⟩⟩

/-- Leaf tests read every strict descendant as absent even when no branch can
realize the child constraints. Pair candidates obey only the ending root test. -/
def candidates (R : List Constraint) (d : Fin 6) (k : Kind)
    (L G : Kind → List Source) : List Source :=
  ([.of true,.of false] : List Source).filter
    (fun t => decide (kind t = k) && test R d t) ++
  if branchOK R d then pairs k L G else []

private theorem pair_candidate (R : List Constraint) (d : Fin 6) (k u v : Kind)
    (L G : Kind → List Source) (l r : Source)
    (hb : branchOK R d = true) (hp : parent u v = k)
    (hl : l ∈ L u) (hr : r ∈ G v) :
    FreeMagma.mul l r ∈ candidates R d k L G := by
  apply List.mem_append_right
  simp only [hb,ite_true]
  exact (mem_pairs k L G _).mpr ⟨u,v,hp,l,hl,r,hr,rfl⟩

/-- Keep the first six distinct actual terms in the fixed candidate order. -/
def retain (C : List Source) : List Source := C.dedup.take 6

private theorem candidates_sound (R : List Constraint) (d : Fin 6) (k : Kind)
    (L G : Kind → List Source)
    (hl : ∀ u, Exact (L u) (language (child false R) d u))
    (hr : ∀ v, Exact (G v) (language (child true R) d v)) :
    ∀ t ∈ candidates R d k L G, t ∈ language R d k := by
  intro t ht
  rcases List.mem_append.mp ht with leaf | branch
  · obtain ⟨_,hs⟩ := List.mem_filter.mp leaf
    have h := Bool.and_eq_true_iff.mp hs
    exact ⟨of_decide_eq_true h.1,(test_iff R d t).mp h.2⟩
  · by_cases hb : branchOK R d = true
    · simp only [hb,ite_true] at branch
      obtain ⟨u,v,hp,l,hlm,r,hrm,rfl⟩ := (mem_pairs k L G t).mp branch
      have lprop := (hl u).sound l hlm
      have rprop := (hr v).sound r hrm
      exact ⟨by simpa only [kind,lprop.1,rprop.1] using hp,
        (compatible_mul R d l r).mpr ⟨hb,lprop.2,rprop.2⟩⟩
    · simp [hb] at branch

private theorem step_exact (R : List Constraint) (d : Fin 6) (k : Kind)
    (L G : Kind → List Source)
    (hl : ∀ u, Exact (L u) (language (child false R) d u))
    (hr : ∀ v, Exact (G v) (language (child true R) d v)) :
    Exact (retain (candidates R d k L G)) (language R d k) := by
  let C := candidates R d k L G
  refine ⟨(List.nodup_dedup C).take,?_,?_,?_⟩
  · simp [retain,List.length_take]
  · intro t ht
    exact candidates_sound R d k L G hl hr t
      (List.mem_dedup.mp (List.mem_of_mem_take ht))
  · intro small t ht
    have csmall : C.dedup.length < 6 := by
      change (C.dedup.take 6).length < 6 at small
      rw [List.length_take] at small
      omega
    have whole : retain C = C.dedup := List.take_of_length_le (by omega)
    rw [show retain (candidates R d k L G) = C.dedup from whole]
    apply List.mem_dedup.mpr
    cases t with
    | of b =>
      apply List.mem_append_left
      apply List.mem_filter.mpr
      refine ⟨by cases b <;> simp,?_⟩
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ht.1,(test_iff R d _).mpr ht.2⟩
    | mul l r =>
      have roots := (compatible_mul R d l r).mp ht.2
      have hp : parent (kind l) (kind r) = k := ht.1
      obtain ⟨l0,hl0⟩ := exact_nonempty (hl (kind l)) ⟨rfl,roots.2.1⟩
      obtain ⟨r0,hr0⟩ := exact_nonempty (hr (kind r)) ⟨rfl,roots.2.2⟩
      have smallL : (L (kind l)).length < 6 := by
        have bound := length_le_of_injective (hl (kind l)).nodup
          (fun x => FreeMagma.mul x r0) (by intro x y h; injection h)
          (fun x hx => pair_candidate R d k (kind l) (kind r) L G x r0 roots.1 hp hx hr0)
        exact lt_of_le_of_lt bound csmall
      have smallR : (G (kind r)).length < 6 := by
        have bound := length_le_of_injective (hr (kind r)).nodup
          (fun y => FreeMagma.mul l0 y) (by intro x y h; injection h)
          (fun y hy => pair_candidate R d k (kind l) (kind r) L G l0 y roots.1 hp hl0 hy)
        exact lt_of_le_of_lt bound csmall
      exact pair_candidate R d k (kind l) (kind r) L G l r roots.1 hp
        ((hl (kind l)).complete smallL l ⟨rfl,roots.2.1⟩)
        ((hr (kind r)).complete smallR r ⟨rfl,roots.2.2⟩)

/-- A finite recursion budget; it bounds the observations, never the sources. -/
def budget (R : List Constraint) : Nat :=
  (R.map (fun c => c.suffix.length + 1)).foldr max 0

private theorem budget_bound (R : List Constraint) :
    ∀ c ∈ R, c.suffix.length < budget R := by
  intro c hc
  have upper : c.suffix.length + 1 ≤ budget R :=
    List.le_max_of_le (List.mem_map.mpr ⟨c, hc, rfl⟩) le_rfl
  exact lt_of_lt_of_le (Nat.lt_succ_self _) upper

private theorem child_bound (n : Nat) (R : List Constraint)
    (h : ∀ c ∈ R, c.suffix.length < n+1) (b : Bool) :
    ∀ c ∈ child b R, c.suffix.length < n := by
  intro c hc
  have bound := h (shift b c) ((mem_child b R c).mp hc)
  change c.suffix.length+1 < n+1 at bound
  omega

/-- The unobserved child has no records and always uses the prescribed actual basis.
No source-size bound or choice operation determines any output. -/
def produce : Nat → List Constraint → Fin 6 → Kind → List Source
  | 0,_,_,k => basis k
  | n+1,R,d,k => if R = [] then basis k else
      retain (candidates R d k (produce n (child false R) d) (produce n (child true R) d))

private theorem produce_exact (n : Nat) (R : List Constraint)
    (h : ∀ c ∈ R, c.suffix.length < n) (d : Fin 6) (k : Kind) :
    Exact (produce n R d k) (language R d k) := by
  induction n generalizing R d k with
  | zero =>
    have empty : R = [] := by
      cases R with
      | nil => rfl
      | cons c R => have no := h c (by simp); omega
    simpa [produce,empty,language,Compatible] using basis_exact k
  | succ n ih =>
    by_cases empty : R = []
    · simpa [produce,empty,language,Compatible] using basis_exact k
    · simp only [produce,if_neg empty]
      exact step_exact R d k _ _
        (fun u => ih (child false R) (child_bound n R h false) d u)
        (fun v => ih (child true R) (child_bound n R h true) d v)

private theorem produce_independent (n m : Nat) (R : List Constraint)
    (hn : ∀ c ∈ R, c.suffix.length < n) (hm : ∀ c ∈ R, c.suffix.length < m)
    (d : Fin 6) (k : Kind) : produce n R d k = produce m R d k := by
  induction n generalizing m R d k with
  | zero =>
    have empty : R = [] := by
      cases R with
      | nil => rfl
      | cons c R => have no := hn c (by simp); omega
    subst R
    cases m <;> simp [produce]
  | succ n ih =>
    cases m with
    | zero =>
      have empty : R = [] := by
        cases R with
        | nil => rfl
        | cons c R => have no := hm c (by simp); omega
      subst R
      simp [produce]
    | succ m =>
      by_cases empty : R = []
      · simp [empty,produce]
      · have left : produce n (child false R) d = produce m (child false R) d := by
          funext u
          exact ih m _ (child_bound n R hn false) (child_bound m R hm false) d u
        have right : produce n (child true R) d = produce m (child true R) d := by
          funext u
          exact ih m _ (child_bound n R hn true) (child_bound m R hm true) d u
        simp only [produce,if_neg empty,left,right]

/-- Rebase along actual trie edges; all roles share the same record trie. -/
def under (v : Address) (R : List Constraint) : List Constraint :=
  v.foldl (fun Q b => child b Q) R

/-- Prefix restoration preserves the original installed index and requested reply. -/
def restore (v : Address) (c : Constraint) : Constraint :=
  {c with suffix := v ++ c.suffix}

private theorem mem_under (v : Address) (R : List Constraint) (c : Constraint) :
    c ∈ under v R ↔ restore v c ∈ R := by
  induction v generalizing R with
  | nil => simp [under,restore]
  | cons b v ih =>
    change c ∈ under v (child b R) ↔ _
    rw [ih,mem_child]
    rfl

/-- Exactly the explicit nodes of the common prefix trie. The empty record
family has no explicit root. A missing child denotes an arbitrary subtree. -/
def Explicit (R : List Constraint) (v : Address) : Prop := under v R ≠ []

instance (R : List Constraint) (v : Address) : Decidable (Explicit R v) :=
  inferInstanceAs (Decidable (under v R ≠ []))

/-- None is the unobserved child #; some [] is the root. Nonexplicit addresses
also have the unconstrained basis, so lookup remains total. -/
def nodeRecords (R : List Constraint) : Option Address → List Constraint
  | none => []
  | some v => under v R

/-- All ending indices at this explicit marker, with multiplicity retained. -/
def markers (R : List Constraint) (v : Address) : List Constraint :=
  (under v R).filter (fun c => decide (c.suffix = []))

/-- The empty menu has only #. -/
def rootNode (R : List Constraint) : Option Address := if R = [] then none else some []

/-- A missing trie child selects #, never an absent actual child. -/
def childNode (R : List Constraint) (v : Address) (b : Bool) : Option Address :=
  if Explicit R (v ++ [b]) then some (v ++ [b]) else none

private theorem under_append (v w : Address) (R : List Constraint) :
    under (v ++ w) R = under w (under v R) := by
  simp only [under, List.foldl_append]

private theorem child_records (R : List Constraint) (v : Address) (b : Bool) :
    nodeRecords R (childNode R v b) = child b (under v R) := by
  unfold childNode
  split_ifs with h
  · change under (v ++ [b]) R = _
    rw [under_append]
    rfl
  · have empty : under (v ++ [b]) R = [] := by
      simpa only [Explicit,not_not] using h
    rw [under_append] at empty
    exact empty.symm

private theorem root_records (R : List Constraint) : nodeRecords R (rootNode R) = R := by
  by_cases h : R = [] <;> simp [rootNode,h,nodeRecords,under]

private theorem explicit_iff (R : List Constraint) (v : Address) :
    Explicit R v ↔ ∃ q, restore v q ∈ R := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := List.exists_mem_of_ne_nil (under v R) h
    exact ⟨q,(mem_under v R q).mp hq⟩
  · rintro ⟨q,hq⟩ h
    have mem := (mem_under v R q).mpr hq
    simp [h] at mem

private theorem marker_iff (R : List Constraint) (v : Address) (q : Constraint) :
    q ∈ markers R v ↔ restore v q ∈ R ∧ q.suffix = [] := by
  simp only [markers,List.mem_filter,decide_eq_true_eq,mem_under]

def lists (R : List Constraint) (v : Option Address) (d : Fin 6) (k : Kind) : List Source :=
  match v with
  | none => basis k
  | some v =>
    let Q := under v R
    if Q = [] then retain (candidates [] d k basis basis)
    else produce (budget Q) Q d k

def nodeLanguage (R : List Constraint) (v : Option Address) (d : Fin 6) (k : Kind) :
    Set Source := language (nodeRecords R v) d k

private theorem lists_exact (R : List Constraint) (v : Option Address) (d : Fin 6) (k : Kind) :
    Exact (lists R v d k) (nodeLanguage R v d k) := by
  cases v with
  | none => simpa [lists,nodeLanguage,nodeRecords,language,Compatible] using basis_exact k
  | some v =>
    by_cases empty : under v R = []
    · simp only [lists,empty,if_true]
      have h := step_exact [] d k basis basis
        (fun u => by simpa [language,Compatible,child] using basis_exact u)
        (fun u => by simpa [language,Compatible,child] using basis_exact u)
      simpa only [nodeLanguage,nodeRecords,empty] using h
    · simpa only [lists,if_neg empty,nodeLanguage,nodeRecords] using
        produce_exact _ _ (budget_bound _) d k

private theorem lists_at_child (R : List Constraint) (v : Address) (b : Bool)
    (d : Fin 6) (k : Kind) : lists R (childNode R v b) d k =
      produce (budget (child b (under v R))) (child b (under v R)) d k := by
  unfold childNode
  split_ifs with h
  · have nonempty : under (v ++ [b]) R ≠ [] := h
    change (if under (v ++ [b]) R = [] then retain (candidates [] d k basis basis)
      else produce (budget (under (v ++ [b]) R)) (under (v ++ [b]) R) d k) = _
    rw [if_neg nonempty,under_append]
    rfl
  · have empty : child b (under v R) = [] := by
      have e : under (v ++ [b]) R = [] := by simpa only [Explicit,not_not] using h
      rw [under_append] at e
      exact e
    simp [lists,empty,budget,produce]

private theorem lists_step (R : List Constraint) (v : Address) (d : Fin 6) (k : Kind)
    (h : Explicit R v) : lists R (some v) d k =
      retain (candidates (under v R) d k
        (fun u => lists R (childNode R v false) d u)
        (fun u => lists R (childNode R v true) d u)) := by
  let Q := under v R
  have nonempty : Q ≠ [] := h
  have qb := budget_bound Q
  cases hn : budget Q with
  | zero =>
    obtain ⟨c,hc⟩ := List.exists_mem_of_ne_nil Q nonempty
    have bound := qb c hc
    rw [hn] at bound
    omega
  | succ n =>
    have bound : ∀ c ∈ Q, c.suffix.length < n+1 := by simpa only [hn] using qb
    have left : produce n (child false Q) d =
        (fun u => lists R (childNode R v false) d u) := by
      funext u
      rw [lists_at_child]
      exact produce_independent n _ _ (child_bound n Q bound false) (budget_bound _) d u
    have right : produce n (child true Q) d =
        (fun u => lists R (childNode R v true) d u) := by
      funext u
      rw [lists_at_child]
      exact produce_independent n _ _ (child_bound n Q bound true) (budget_bound _) d u
    change (if Q = [] then retain (candidates [] d k basis basis)
      else produce (budget Q) Q d k) = _
    rw [if_neg nonempty,hn,produce,if_neg nonempty,left,right]

/-- Original a,c,b1,b2,b3,b4 role order at each length-three occurrence. -/
def occurrenceRole : Bool → Bool → Bool → Fin 6
  | false,_,false => 0
  | true,_,false => 1
  | false,false,true => 2
  | false,true,true => 3
  | true,false,true => 4
  | true,true,true => 5

/-- An installed Read keeps its original index. Words shorter than three
produce no suffix record and are checked by the independent branch guard. -/
def installOne (i : Nat) (a : Address) (r : Reply) : Option Constraint :=
  match a with
  | x :: y :: z :: v => some ⟨i,occurrenceRole x y z,v,r⟩
  | _ => none

/-- No deduplication of installed Reads or their suffix records is performed. -/
def install {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply) : List Constraint :=
  (List.finRange n).filterMap (fun i => installOne i.val (words i) (replies i))

/-- A nonempty original installed menu has an explicit root even when all
its words are short. The empty installed menu uses only #. -/
def installedRoot : Nat → Option Address
  | 0 => none
  | _+1 => some []

private theorem installed_records {n : Nat} (words : Fin n → Address)
    (replies : Fin n → Reply) : nodeRecords (install words replies) (installedRoot n) =
      install words replies := by
  cases n with
  | zero => simp [installedRoot,nodeRecords,install]
  | succ n => rfl

/-- The original common trie includes the root of every nonempty installed
menu and all prefixes of its long-record suffixes. -/
def InstalledExplicit {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply)
    (v : Address) : Prop := (n ≠ 0 ∧ v = []) ∨ Explicit (install words replies) v

/-- Every original short installed word must request the actual branch reply. -/
def ShortGuard {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply) : Prop :=
  ∀ i, (words i).length < 3 → replies i = .branch

/-- This is the actual native relation, not an assumed suffix recurrence. -/
def Realizes {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply) (t : Source) : Prop :=
  ∀ i, readout (words i) t = replies i

private theorem filling_short (x : Fin 6 → Source) (a : Address) (h : a.length < 3) :
    readout a (NativeSixSourceCones.filling x) = .branch := by
  rcases a with _ | ⟨a,_ | ⟨b,_ | ⟨c,v⟩⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> rfl
  · simp at h; omega

private theorem filling_long (x : Fin 6 → Source) (a b c : Bool) (v : Address) :
    readout (a :: b :: c :: v) (NativeSixSourceCones.filling x) =
      readout v (x (dToNative (occurrenceRole a b c))) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem install_mem {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply)
    (c : Constraint) : c ∈ install words replies ↔
      ∃ i, installOne i.val (words i) (replies i) = some c := by
  simp only [install,List.mem_filterMap,List.mem_finRange,true_and]

private theorem native_root {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply)
    (x : Fin 6 → Source) :
    Realizes words replies (NativeSixSourceCones.filling x) ↔
      ShortGuard words replies ∧ ∀ d, Compatible (install words replies) d (x (dToNative d)) := by
  constructor
  · intro h
    refine ⟨fun i hi => (h i).symm.trans (filling_short x (words i) hi),?_⟩
    intro d q hq hd
    obtain ⟨i,hi⟩ := (install_mem words replies q).mp hq
    cases hw : words i with
    | nil => simp [hw,installOne] at hi
    | cons a v =>
      cases v with
      | nil => simp [hw,installOne] at hi
      | cons b v =>
        cases v with
        | nil => simp [hw,installOne] at hi
        | cons c v =>
          simp only [hw,installOne,Option.some.injEq] at hi
          subst q
          cases hd
          simpa only [hw,filling_long] using h i
  · rintro ⟨short,long⟩ i
    by_cases hs : (words i).length < 3
    · exact (filling_short x (words i) hs).trans (short i hs).symm
    · cases hw : words i with
      | nil => simp [hw] at hs
      | cons a v =>
        cases v with
        | nil => simp [hw] at hs
        | cons b v =>
          cases v with
          | nil => simp [hw] at hs
          | cons c v =>
            rw [filling_long]
            exact long (occurrenceRole a b c) ⟨i.val,occurrenceRole a b c,v,replies i⟩
              ((install_mem words replies _).mpr ⟨i,by simp [installOne,hw]⟩) rfl

/-- The actual class roots of any original origin, in native filling order. -/
noncomputable def recoveredNative (u : NativeSixSourceCones.Fiber) : Fin 6 → Source :=
  fun i => (NativeCutFibers.recover NativeSixSourceCones.P NativeSixSourceCones.prefix_free
    NativeSixSourceCones.row ⟨substitution u.val,u.property⟩).val
      (NativeRepeatedPartnerControllers.coord i)

private theorem recovered_filling (u : NativeSixSourceCones.Fiber) :
    NativeSixSourceCones.filling (recoveredNative u) = substitution u.val := by
  have h := NativeCutFibers.recover_fill NativeSixSourceCones.P NativeSixSourceCones.prefix_free
    NativeSixSourceCones.row ⟨substitution u.val,u.property⟩
  exact h

/-- The source-language clause at an original indexed trie node. Both actual
occurrences of a or c constrain this same whole role value. -/
def OriginalCompatible {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply)
    (v : Address) (d : Fin 6) (t : Source) : Prop :=
  ∀ (i : Fin n) (a b c : Bool) (w : Address),
    words i = a :: b :: c :: (v ++ w) → occurrenceRole a b c = d →
      readout w t = replies i

/-- All original type and indexed suffix requirements, including empty fibers. -/
def originalLanguage {n : Nat} (words : Fin n → Address) (replies : Fin n → Reply)
    (v : Address) (d : Fin 6) (k : Kind) : Set Source :=
  {t | Class k t ∧ OriginalCompatible words replies v d t}

private theorem indexed_compatible {n : Nat} (words : Fin n → Address)
    (replies : Fin n → Reply) (v : Address) (d : Fin 6) (t : Source) :
    Compatible (under v (install words replies)) d t ↔
      OriginalCompatible words replies v d t := by
  constructor
  · intro h i a b c w hw hd
    let q : Constraint := ⟨i.val,occurrenceRole a b c,w,replies i⟩
    have mem : q ∈ under v (install words replies) := (mem_under v _ q).mpr
      ((install_mem words replies _).mpr ⟨i,by simp [installOne,hw,restore,q]⟩)
    exact h q mem hd
  · intro h q hq hd
    obtain ⟨i,hi⟩ := (install_mem words replies (restore v q)).mp
      ((mem_under v _ q).mp hq)
    cases hw : words i with
    | nil => simp [hw,installOne] at hi
    | cons a z =>
      cases z with
      | nil => simp [hw,installOne] at hi
      | cons b z =>
        cases z with
        | nil => simp [hw,installOne] at hi
        | cons c w =>
          simp only [hw,installOne,Option.some.injEq] at hi
          have role : occurrenceRole a b c = q.role := congrArg Constraint.role hi
          have suffix : w = v ++ q.suffix := congrArg Constraint.suffix hi
          have reply : replies i = q.reply := congrArg Constraint.reply hi
          exact (h i a b c q.suffix (by rw [hw,suffix]) (role.trans hd)).trans reply

private theorem indexed_language {n : Nat} (words : Fin n → Address)
    (replies : Fin n → Reply) (v : Address) (d : Fin 6) (k : Kind) :
    nodeLanguage (install words replies) (some v) d k =
      originalLanguage words replies v d k := by
  ext t
  exact and_congr (class_kind t k).symm (indexed_compatible words replies v d t)

/-- Native leaf replies at an ending record; every proper continuation is absent. -/
def leafReply (b : Bool) : Reply := if b then .alpha else .beta

def LeafRule (R : List Constraint) (d : Fin 6) (b : Bool) : Prop :=
  ∀ c ∈ R, c.role = d →
    (c.suffix = [] → c.reply = leafReply b) ∧
    (c.suffix ≠ [] → c.reply = .absent)

private theorem leaf_rule (R : List Constraint) (d : Fin 6) (b : Bool) :
    Compatible R d (.of b) ↔ LeafRule R d b := by
  constructor
  · intro h c hc hd
    have read := h c hc hd
    constructor
    · intro hv
      cases b <;> simpa [hv,readout,leafReply] using read.symm
    · intro hv
      cases hs : c.suffix with
      | nil => exact (hv hs).elim
      | cons a v => simpa [hs,readout] using read.symm
  · intro h c hc hd
    have rules := h c hc hd
    cases hs : c.suffix with
    | nil => cases b <;> simpa [hs,readout,leafReply] using (rules.1 hs).symm
    | cons a v => simpa [hs,readout] using (rules.2 (by simp [hs])).symm

private theorem leaf_list (R : List Constraint) (v : Option Address) (d : Fin 6) (b : Bool) :
    .of b ∈ lists R v d (kind (.of b)) ↔ LeafRule (nodeRecords R v) d b := by
  have exact := lists_exact R v d (kind (.of b))
  have sub : ∀ t ∈ lists R v d (kind (.of b)), t = .of b := by
    intro t ht
    have typed := (exact.sound t ht).1
    cases b with
    | false => exact (kind_H t).mp typed
    | true => exact (kind_A t).mp typed
  have bound := length_le_of_injective exact.nodup id Function.injective_id
    (fun t ht => (List.mem_singleton.mpr (sub t ht) : id t ∈ [.of b]))
  have small : (lists R v d (kind (.of b))).length < 6 := by
    simp at bound
    omega
  rw [← leaf_rule]
  exact ⟨fun h => (exact.sound _ h).2,
    fun h => exact.complete small _ ⟨rfl,h⟩⟩

/-- A clause-complete native exact-list statement. The supplied function is
computable; classical reasoning is confined to its cardinality proof. -/
structure Specification
    (F : List Constraint → Option Address → Fin 6 → Kind → List Source) : Prop where
  classes : ∀ t k, Class k t ↔ kind t = k
  hash : ∀ R d k, F R none d k = basis k
  unconstrainedExplicit : ∀ R v d k, under v R = [] →
    F R (some v) d k = retain (candidates [] d k basis basis)
  exact : ∀ R v d k, Exact (F R v d k) (nodeLanguage R v d k)
  cardinality : ∀ R v d k,
    ((F R v d k).length : ENat) = min 6 (nodeLanguage R v d k).encard
  leaves : ∀ R v d b,
    .of b ∈ F R v d (kind (.of b)) ↔ LeafRule (nodeRecords R v) d b
  branches : ∀ R d l r,
    Compatible R d (.mul l r) ↔ branchOK R d = true ∧
      Compatible (child false R) d l ∧ Compatible (child true R) d r
  rebasing : ∀ R v q, q ∈ under v R ↔ restore v q ∈ R
  explicitNodes : ∀ R v, Explicit R v ↔ ∃ q, restore v q ∈ R
  endingIndices : ∀ R v q, q ∈ markers R v ↔ restore v q ∈ R ∧ q.suffix = []
  rootRecords : ∀ R, nodeRecords R (rootNode R) = R
  childRecords : ∀ R v b, nodeRecords R (childNode R v b) = child b (under v R)
  recurrence : ∀ R v d k, Explicit R v → F R (some v) d k =
    retain (candidates (under v R) d k
      (fun u => F R (childNode R v false) d u) (fun u => F R (childNode R v true) d u))
  indexed : ∀ (n : Nat) (words : Fin n → Address) (replies : Fin n → Reply) v d k,
    nodeLanguage (install words replies) (some v) d k = originalLanguage words replies v d k
  installedRootLaw : ∀ n,
    (installedRoot n = none ↔ n = 0) ∧ (installedRoot n = some [] ↔ n ≠ 0)
  installedNodes : ∀ (n : Nat) (words : Fin n → Address) (replies : Fin n → Reply) v,
    InstalledExplicit words replies v ↔
      (n ≠ 0 ∧ v = []) ∨ ∃ q, restore v q ∈ install words replies
  rootLists : ∀ (n : Nat) (words : Fin n → Address) (replies : Fin n → Reply) d k,
    Exact (F (install words replies) (installedRoot n) d k)
      (originalLanguage words replies [] d k)
  rootCardinality : ∀ (n : Nat) (words : Fin n → Address) (replies : Fin n → Reply) d k,
    ((F (install words replies) (installedRoot n) d k).length : ENat) =
      min 6 (originalLanguage words replies [] d k).encard
  filling : ∀ (n : Nat) (words : Fin n → Address) (replies : Fin n → Reply) (x : Fin 6 → Source),
    Realizes words replies (NativeSixSourceCones.filling x) ↔
      ShortGuard words replies ∧ ∀ d,
        OriginalCompatible words replies [] d (x (dToNative d))
  origins : ∀ (n : Nat) (words : Fin n → Address) (replies : Fin n → Reply)
    (u : NativeSixSourceCones.Fiber),
    NativeSixSourceCones.filling (recoveredNative u) = substitution u.val ∧
    (Realizes words replies (substitution u.val) ↔
      ShortGuard words replies ∧ ∀ d,
        OriginalCompatible words replies [] d (recoveredNative u (dToNative d)))

/-- Deterministic retained actual finite terms at all original indexed nodes
and #, with exact extended-natural cardinality and full small languages. -/
theorem native_indexed_role_lists : Specification lists := by
  refine ⟨class_kind,by intros; rfl,?_,lists_exact,?_,leaf_list,compatible_mul,
    (fun R v q => mem_under v R q),
    explicit_iff,marker_iff,root_records,child_records,lists_step,
    fun _ => indexed_language,?_,?_,?_,?_,?_,?_⟩
  · intro R v d k empty
    simp only [lists,empty,if_true]
  · intro R v d k
    exact exact_card (lists_exact R v d k)
  · intro n
    cases n <;> simp [installedRoot]
  · intro n words replies v
    exact or_congr Iff.rfl (explicit_iff (install words replies) v)
  · intro n words replies d k
    rw [← indexed_language words replies [] d k]
    have h := lists_exact (install words replies) (installedRoot n) d k
    change Exact _ (language (nodeRecords _ (installedRoot n)) d k) at h
    rw [installed_records] at h
    exact h
  · intro n words replies d k
    have h := lists_exact (install words replies) (installedRoot n) d k
    change Exact _ (language (nodeRecords _ (installedRoot n)) d k) at h
    rw [installed_records] at h
    have count := exact_card h
    rw [← indexed_language words replies [] d k]
    exact count
  · intro n words replies x
    rw [native_root]
    apply and_congr Iff.rfl
    exact forall_congr' (fun d => indexed_compatible words replies [] d _)
  · intro n words replies u
    refine ⟨recovered_filling u,?_⟩
    rw [← recovered_filling u,native_root]
    apply and_congr Iff.rfl
    exact forall_congr' (fun d => indexed_compatible words replies [] d _)

#print axioms native_indexed_role_lists

end D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeIndexedRoleLists
