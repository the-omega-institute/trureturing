/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.effective_inverse; instance=D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.sixVertex
   digest: Original birth-typed material roots and complete ordered terminal presentations. -/

import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin

/-! Original birth-typed material rigidity and finite complete-order recognition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves nodes)
open ActualLeafHistoryRigidity (subtree)

/-- Exactly the original LAB birth condition, at every left-ending logical address. -/
def D (t : Source) : Prop := ∀ p : Address, readout (p ++ [false]) t ≠ .alpha

/-- All vertices of C, including the distinct left marker of every beta. -/
def material : Source → List Address
  | .of true => [[]]
  | .of false => [[], [false]]
  | .mul l r => [] :: ((material l).map (false :: ·) ++ (material r).map (true :: ·))

/-- The complete linear terminal roster, with one terminal per logical leaf. -/
def terminals : Source → List Address
  | .of true => [[]]
  | .of false => [[false]]
  | .mul l r => (terminals l).map (false :: ·) ++ (terminals r).map (true :: ·)

/-- Original outward material neighbors; a marker has no logical readout. -/
def children (t : Source) (p : Address) : List Address :=
  match readout p t with
  | .branch => [p ++ [false], p ++ [true]]
  | .beta => [p ++ [false]]
  | _ => []

/-- The unordered neighborhood is represented by a list without repetition. -/
def neighbors (t : Source) (p : Address) : List Address :=
  children t p ++ if p = [] then [] else [p.dropLast]

/-- An arbitrary unrooted isomorphism of the full material supports, preserving
all positions of the complete linear terminal roster. Neighborhood equations are
permutations, so their displayed enumeration supplies no edge orientation. -/
structure OrderedIso (t s : Source) where
  forward : Address → Address
  backward : Address → Address
  forward_mem : ∀ p ∈ material t, forward p ∈ material s
  backward_mem : ∀ p ∈ material s, backward p ∈ material t
  left_inv : ∀ p ∈ material t, backward (forward p) = p
  right_inv : ∀ p ∈ material s, forward (backward p) = p
  forward_neighbors : ∀ p ∈ material t,
    ((neighbors t p).map forward).Perm (neighbors s (forward p))
  forward_terminals : (terminals t).map forward = terminals s

private theorem root_mem (t : Source) : [] ∈ material t := by
  cases t with
  | of b => cases b <;> simp [material]
  | mul l r => simp [material]

private theorem logical_mem (t : Source) (p : Address) (h : readout p t ≠ .absent) :
    p ∈ material t := by
  induction p generalizing t with
  | nil => exact root_mem t
  | cons b p ih =>
    cases t with
    | of a => simp [readout] at h
    | mul l r =>
      cases b <;> simp only [readout] at h
      · simp [material, List.mem_map, ih l h]
      · simp [material, List.mem_map, ih r h]

private theorem read_leaf (t : Source) (p : Address) (b : Bool)
    (h : readout p t = if b then .alpha else .beta) (q : Address) :
    readout (p ++ q) t = readout q (.of b) := by
  have leaf := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t p b h
  rw [ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p q t, leaf]

private theorem beta_marker (t : Source) (p : Address) (h : readout p t = .beta) :
    p ++ [false] ∈ material t ∧ neighbors t (p ++ [false]) = [p] := by
  have hr := read_leaf t p false h [false]
  constructor
  · clear hr
    induction p generalizing t with
    | nil => cases t with
      | of b => cases b <;> simp_all [readout, material]
      | mul l r => simp [readout] at h
    | cons b p ih =>
      cases t with
      | of a => simp [readout] at h
      | mul l r =>
        cases b <;> simp only [readout] at h
        · simp [material, List.mem_map, ih l h]
        · simp [material, List.mem_map, ih r h]
  · simp [neighbors, children, hr, readout]

private theorem nonroot_two (t : Source) (p : Address) (hp : p ≠ [])
    (hd : (neighbors t p).length = 2) :
    ∃ q ∈ neighbors t p, q ∈ material t ∧ neighbors t q = [p] := by
  have hb : readout p t = .beta := by
    cases hr : readout p t <;> simp [neighbors, children, hp, hr] at hd ⊢
  refine ⟨p ++ [false], ?_, (beta_marker t p hb).1, (beta_marker t p hb).2⟩
  simp [neighbors, children, hb]

private theorem three_branch (t : Source) (h : 3 ≤ (leaves t).length) :
    ∃ l r, t = .mul l r := by
  cases t with
  | of b => simp [leaves] at h
  | mul l r => exact ⟨l, r, rfl⟩

private theorem root_degree (t : Source) (h : 3 ≤ (leaves t).length) :
    (neighbors t []).length = 2 := by
  obtain ⟨l,r,rfl⟩ := three_branch t h
  rfl

private theorem root_terminal (t : Source) (ht : D t) (h : 3 ≤ (leaves t).length)
    (q : Address) (hq : q ∈ neighbors t []) (hd : (neighbors t q).length = 1) :
    (terminals t).getLast? = some q ∧ neighbors t q = [[]] := by
  obtain ⟨l,r,rfl⟩ := three_branch t h
  have hl : l ≠ .of true := by
    intro he
    have hh := ht []
    simp [he, readout] at hh
  have hq' : q = [false] ∨ q = [true] := by simpa [neighbors, children, readout] using hq
  rcases hq' with rfl | rfl
  · cases l with
    | of b => cases b <;> simp_all [neighbors, children, readout]
    | mul a b => simp [neighbors, children, readout] at hd
  · cases r with
    | of b =>
      cases b with
      | false => simp [neighbors, children, readout] at hd
      | true => simp [terminals, neighbors, children, readout]
    | mul a b => simp [neighbors, children, readout] at hd

/-- A degree-two vertex with no adjacent degree-one vertex. -/
private def Bare (t : Source) (p : Address) : Prop :=
  ∀ q ∈ neighbors t p, (neighbors t q).length ≠ 1

private theorem bare_only_root (t : Source) (p : Address)
    (hd : (neighbors t p).length = 2) (hb : Bare t p) : p = [] := by
  by_contra hp
  obtain ⟨q,hq,_,he⟩ := nonroot_two t p hp hd
  have bad := hb q hq
  simp [he] at bad

private theorem children_cons (l r : Source) (b : Bool) (p : Address) :
    children (.mul l r) (b :: p) =
      (children (if b then r else l) p).map (b :: ·) := by
  cases b
  · cases h : readout p l <;> simp [children, readout, h]
  · cases h : readout p r <;> simp [children, readout, h]

private theorem neighbors_cons (l r : Source) (b : Bool) (p : Address) :
    neighbors (.mul l r) (b :: p) =
      (neighbors (if b then r else l) p).map (b :: ·) ++
        if p = [] then [[]] else [] := by
  simp only [neighbors, children_cons, List.map_append]
  cases p with
  | nil => simp
  | cons c p => simp

private theorem neighbor_mem (t : Source) (p : Address) (hp : p ∈ material t)
    (q : Address) (hq : q ∈ neighbors t p) : q ∈ material t := by
  induction t generalizing p q with
  | of b =>
    cases b <;> simp only [material, List.mem_cons, List.not_mem_nil, or_false] at hp
    · rcases hp with rfl | rfl
      · have : q = [false] := by simpa [neighbors, children, readout] using hq
        subst q
        simp [material]
      · have : q = [] := by simpa [neighbors, children, readout] using hq
        subst q
        exact root_mem _
    · subst p
      simp [neighbors, children, readout] at hq
  | mul l r il ir =>
    cases p with
    | nil =>
      have hq' : q = [false] ∨ q = [true] := by
        simpa [neighbors, children, readout] using hq
      rcases hq' with rfl | rfl <;> simp [material, List.mem_map, root_mem]
    | cons b p =>
      rw [neighbors_cons] at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
        cases b
        · have hm : p ∈ material l := by simpa [material, List.mem_map] using hp
          have hv' := il p hm v hv
          simp [material, List.mem_map, hv']
        · have hm : p ∈ material r := by simpa [material, List.mem_map] using hp
          have hv' := ir p hm v hv
          simp [material, List.mem_map, hv']
      · split_ifs at hq with he
        · have : q = [] := List.mem_singleton.mp hq
          subst q
          exact root_mem _
        · simp at hq

private theorem terminal_mem (t : Source) (p : Address) (hp : p ∈ terminals t) :
    p ∈ material t := by
  induction t generalizing p with
  | of b => cases b <;> simp_all [terminals, material]
  | mul l r il ir =>
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      simp [material, List.mem_map, il q hq]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      simp [material, List.mem_map, ir q hq]

private def OrderedIso.symm {t s : Source} (e : OrderedIso t s) : OrderedIso s t where
  forward := e.backward
  backward := e.forward
  forward_mem := e.backward_mem
  backward_mem := e.forward_mem
  left_inv := e.right_inv
  right_inv := e.left_inv
  forward_neighbors p hp := by
    have hq := e.backward_mem p hp
    have h := (e.forward_neighbors (e.backward p) hq).map e.backward
    rw [e.right_inv p hp] at h
    have he : ((neighbors t (e.backward p)).map e.forward).map e.backward =
        neighbors t (e.backward p) := by
      rw [List.map_map]
      calc
        _ = (neighbors t (e.backward p)).map id := List.map_congr_left
          (fun q hq' => e.left_inv q (neighbor_mem t _ hq q hq'))
        _ = _ := List.map_id _
    rw [he] at h
    exact h.symm
  forward_terminals := by
    rw [← e.forward_terminals, List.map_map]
    calc
      _ = (terminals t).map id := List.map_congr_left
        (fun p hp => e.left_inv p (terminal_mem t p hp))
      _ = _ := List.map_id _

private theorem degree_map {t s : Source} (e : OrderedIso t s)
    (p : Address) (hp : p ∈ material t) :
    (neighbors t p).length = (neighbors s (e.forward p)).length := by
  simpa only [List.length_map] using (e.forward_neighbors p hp).length_eq

private theorem bare_map {t s : Source} (e : OrderedIso t s)
    (p : Address) (hp : p ∈ material t) (hb : Bare t p) : Bare s (e.forward p) := by
  intro q hq
  have hpre := (e.forward_neighbors p hp).mem_iff.mpr hq
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hpre
  rw [← degree_map e v (neighbor_mem t p hp v hv)]
  exact hb v hv

private theorem child_present (t : Source) (p : Address) (b : Bool) :
    p ++ [b] ∈ material t ↔ p ++ [b] ∈ children t p := by
  induction p generalizing t with
  | nil =>
    cases t with
    | of c => cases c <;> cases b <;> simp [material, children, readout]
    | mul l r => cases b <;> simp [material, children, readout, List.mem_map, root_mem]
  | cons c p ih =>
    cases t with
    | of a => cases a <;> simp [material, children, readout]
    | mul l r =>
      rw [List.cons_append, children_cons]
      cases c
      · simpa [material, List.mem_map] using ih l
      · simpa [material, List.mem_map] using ih r

private theorem parent_mem (t : Source) (p : Address) (b : Bool)
    (hp : p ++ [b] ∈ material t) : p ∈ material t := by
  have hc := (child_present t p b).mp hp
  apply logical_mem t p
  intro h
  simp [children, h] at hc

private theorem prefix_mem (t : Source) (p q : Address)
    (h : p ++ q ∈ material t) : p ∈ material t := by
  induction q using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton q b ih =>
    exact ih (parent_mem t (p ++ q) b (by simpa [List.append_assoc] using h))

private theorem neighbor_length (t : Source) (p q : Address) (hq : q ∈ neighbors t p) :
    q.length ≤ p.length + 1 := by
  rcases List.mem_append.mp hq with hc | hp
  · cases h : readout p t <;> simp only [children, h, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    all_goals rcases hc with rfl | rfl <;> simp
  · split_ifs at hp with he
    · simp at hp
    · obtain rfl := List.mem_singleton.mp hp
      simp
      omega

private theorem forward_depth_le {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p : Address) (hp : p ∈ material t) :
    (e.forward p).length ≤ p.length := by
  induction p using List.reverseRecOn with
  | nil => simp [hr]
  | append_singleton p b ih =>
    have hm := parent_mem t p b hp
    have hc : p ++ [b] ∈ neighbors t p := List.mem_append_left _ ((child_present t p b).mp hp)
    have hi := (e.forward_neighbors p hm).mem_iff.mp (List.mem_map.mpr ⟨_,hc,rfl⟩)
    have hb := neighbor_length s (e.forward p) (e.forward (p ++ [b])) hi
    have hd := ih hm
    simp only [List.length_append, List.length_singleton]
    omega

private theorem depth_map {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p : Address) (hp : p ∈ material t) :
    (e.forward p).length = p.length := by
  have hback : e.backward [] = [] := by
    simpa [hr] using e.left_inv [] (root_mem t)
  have a := forward_depth_le e hr p hp
  have b := forward_depth_le e.symm hback (e.forward p) (e.forward_mem p hp)
  change (e.backward (e.forward p)).length ≤ (e.forward p).length at b
  rw [e.left_inv p hp] at b
  omega

private theorem child_map {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p : Address) (b : Bool)
    (hp : p ++ [b] ∈ material t) :
    ∃ c : Bool, e.forward (p ++ [b]) = e.forward p ++ [c] := by
  have hm := parent_mem t p b hp
  have hc : p ++ [b] ∈ neighbors t p := List.mem_append_left _ ((child_present t p b).mp hp)
  have hi := (e.forward_neighbors p hm).mem_iff.mp (List.mem_map.mpr ⟨_,hc,rfl⟩)
  have hd := depth_map e hr p hm
  have hd' := depth_map e hr (p ++ [b]) hp
  rcases List.mem_append.mp hi with hi | hi
  · cases h : readout (e.forward p) s <;>
      simp only [children, h, List.mem_cons, List.not_mem_nil, or_false] at hi
    · exact ⟨false,hi⟩
    · rcases hi with hi | hi
      · exact ⟨false,hi⟩
      · exact ⟨true,hi⟩
  · split_ifs at hi with he
    · simp at hi
    · obtain heq := List.mem_singleton.mp hi
      have hlen := congrArg List.length heq
      simp only [List.length_dropLast, hd, hd', List.length_append,
        List.length_singleton] at hlen
      omega

private theorem prefix_map {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p q : Address) (hp : p ++ q ∈ material t) :
    (e.forward p).IsPrefix (e.forward (p ++ q)) := by
  induction q generalizing p with
  | nil => simp
  | cons b q ih =>
    have hm : p ++ [b] ∈ material t := prefix_mem t (p ++ [b]) q (by
      simpa [List.append_assoc] using hp)
    obtain ⟨c,hc⟩ := child_map e hr p b hm
    have hpre : (e.forward p).IsPrefix (e.forward (p ++ [b])) := ⟨[c],hc.symm⟩
    exact hpre.trans (by simpa [List.append_assoc] using (ih (p ++ [b])
      (by simpa [List.append_assoc] using hp)))

private abbrev Before : Address → Address → Prop :=
  List.Lex (InvImage (· < ·) Bool.toNat)

private theorem terminals_ordered (t : Source) : (terminals t).Pairwise Before := by
  induction t with
  | of b => cases b <;> simp [terminals]
  | mul l r il ir =>
    simp only [terminals, List.pairwise_append, List.pairwise_map]
    refine ⟨il.imp (fun h => List.Lex.cons h),
      ir.imp (fun h => List.Lex.cons h), ?_⟩
    intro a ha b hb
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    exact List.Lex.rel (show false.toNat < true.toNat from by decide)

private theorem order_transfer (L : List Address) (f : Address → Address)
    (hL : L.Pairwise Before) (hf : (L.map f).Pairwise Before)
    (x y : Address) (hx : x ∈ L) (hy : y ∈ L) (hxy : Before x y) :
    Before (f x) (f y) := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    simp only [List.pairwise_cons] at hL
    simp only [List.map_cons, List.pairwise_cons] at hf
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact False.elim (asymm hxy hxy)
    · exact hf.1 _ (List.mem_map.mpr ⟨_,hy,rfl⟩)
    · exact False.elim (asymm hxy (hL.1 _ hx))
    · exact ih hL.2 hf.2 hx hy

private theorem terminal_descendant (t : Source) (p : Address) (hp : p ∈ material t) :
    ∃ q ∈ terminals t, p.IsPrefix q := by
  induction t generalizing p with
  | of b =>
    cases b
    · simp only [material, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨[false],by simp [terminals],by simp⟩
    · have : p = [] := by simpa [material] using hp
      subst p
      exact ⟨[],by simp [terminals],by simp⟩
  | mul l r il ir =>
    cases p with
    | nil =>
      obtain ⟨q,hq,_⟩ := il [] (root_mem l)
      exact ⟨false :: q,by simp [terminals, List.mem_map, hq],by simp⟩
    | cons b p =>
      cases b
      · have hm : p ∈ material l := by simpa [material, List.mem_map] using hp
        obtain ⟨q,hq,⟨a,ha⟩⟩ := il p hm
        exact ⟨false :: q,by simp [terminals, List.mem_map,hq],⟨a,by simpa using ha⟩⟩
      · have hm : p ∈ material r := by simpa [material, List.mem_map] using hp
        obtain ⟨q,hq,⟨a,ha⟩⟩ := ir p hm
        exact ⟨true :: q,by simp [terminals, List.mem_map,hq],⟨a,by simpa using ha⟩⟩

private theorem forward_order {t s : Source} (e : OrderedIso t s)
    (x y : Address) (hx : x ∈ terminals t) (hy : y ∈ terminals t)
    (hxy : Before x y) : Before (e.forward x) (e.forward y) := by
  apply order_transfer (terminals t) e.forward (terminals_ordered t)
    (by rw [e.forward_terminals]; exact terminals_ordered s) x y hx hy hxy

private theorem no_reversal (p a b : Address) :
    ¬ Before (p ++ true :: a) (p ++ false :: b) := by
  induction p with
  | nil => intro h; cases h with | rel h => exact (by decide : ¬ (true.toNat < false.toNat)) h
  | cons c p ih => exact fun h => ih (List.lex_cons_iff.mp h)

private theorem children_degree_map {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p : Address) (hp : p ∈ material t) :
    (children t p).length = (children s (e.forward p)).length := by
  have hz : e.forward p = [] ↔ p = [] := by
    rw [← List.length_eq_zero_iff, depth_map e hr p hp, List.length_eq_zero_iff]
  have hd := degree_map e p hp
  by_cases h : p = []
  · subst p
    simpa [neighbors, hr] using hd
  · have h' : e.forward p ≠ [] := fun he => h (hz.mp he)
    simpa [neighbors, h, h'] using hd

private theorem forward_injective {t s : Source} (e : OrderedIso t s)
    (p q : Address) (hp : p ∈ material t) (hq : q ∈ material t)
    (he : e.forward p = e.forward q) : p = q := by
  simpa [e.left_inv p hp, e.left_inv q hq] using congrArg e.backward he

private theorem branch_map {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p : Address) (hb : readout p t = .branch) :
    e.forward (p ++ [false]) = e.forward p ++ [false] ∧
    e.forward (p ++ [true]) = e.forward p ++ [true] := by
  have hl : p ++ [false] ∈ material t := (child_present t p false).mpr (by simp [children,hb])
  have hh : p ++ [true] ∈ material t := (child_present t p true).mpr (by simp [children,hb])
  obtain ⟨c,hc⟩ := child_map e hr p false hl
  obtain ⟨d,hd⟩ := child_map e hr p true hh
  have hne : c ≠ d := by
    intro he
    have hm := forward_injective e _ _ hl hh (hc.trans (he ▸ hd.symm))
    simp at hm
  cases c <;> cases d
  · exact False.elim (hne rfl)
  · exact ⟨hc,hd⟩
  · obtain ⟨x,hx,⟨a,ha⟩⟩ := terminal_descendant t (p ++ [false]) hl
    obtain ⟨y,hy,⟨b,hbb⟩⟩ := terminal_descendant t (p ++ [true]) hh
    have hxy : Before x y := by
      rw [← ha,← hbb]
      simpa [List.append_assoc] using
        (List.Lex.rel (show false.toNat < true.toNat from by decide) :
          Before (false :: a) (true :: b)).append_left _ p
    have horder := forward_order e x y hx hy hxy
    have px := prefix_map e hr (p ++ [false]) a (by rw [ha]; exact terminal_mem t x hx)
    have py := prefix_map e hr (p ++ [true]) b (by rw [hbb]; exact terminal_mem t y hy)
    rw [ha] at px
    rw [hbb] at py
    obtain ⟨u,hu⟩ := px
    obtain ⟨v,hv⟩ := py
    rw [← hu,← hv,hc,hd] at horder
    exact False.elim (no_reversal (e.forward p) u v (by
      simpa [List.append_assoc] using horder))
  · exact False.elim (hne rfl)

private theorem child_bit {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p : Address) (b : Bool)
    (hp : p ++ [b] ∈ material t) :
    e.forward (p ++ [b]) = e.forward p ++ [b] := by
  have hm := parent_mem t p b hp
  have hc := (child_present t p b).mp hp
  cases h : readout p t with
  | alpha => simp [children,h] at hc
  | absent => simp [children,h] at hc
  | branch =>
    cases b
    · exact (branch_map e hr p h).1
    · exact (branch_map e hr p h).2
  | beta =>
    have hb : b = false := by simpa [children,h] using hc
    subst b
    have hd := children_degree_map e hr p hm
    have hs : readout (e.forward p) s = .beta := by
      cases hs' : readout (e.forward p) s <;> simp_all [children]
    obtain ⟨c,he⟩ := child_map e hr p false hp
    have hcm : e.forward p ++ [c] ∈ material s := he ▸ e.forward_mem _ hp
    have hcc := (child_present s (e.forward p) c).mp hcm
    have hcf : c = false := by simpa [children,hs] using hcc
    simpa [hcf] using he

private theorem coordinates_from_root {t s : Source} (e : OrderedIso t s)
    (hr : e.forward [] = []) (p : Address) (hp : p ∈ material t) : e.forward p = p := by
  induction p using List.reverseRecOn with
  | nil => exact hr
  | append_singleton p b ih =>
    rw [child_bit e hr p b hp, ih (parent_mem t p b hp)]

/-- Every unrooted full-roster isomorphism on the original domain preserves
its actual original root. Neither map receives a distinguished root as advice. -/
private theorem original_root (t s : Source) (ht : D t) (hs : D s)
    (hlt : 3 ≤ (leaves t).length) (hls : 3 ≤ (leaves s).length)
    (e : OrderedIso t s) : e.forward [] = [] := by
  classical
  have hdt := root_degree t hlt
  have hds := root_degree s hls
  have rootmap := degree_map e [] (root_mem t)
  by_cases hb : Bare t []
  · exact bare_only_root s (e.forward []) (rootmap ▸ hdt)
      (bare_map e [] (root_mem t) hb)
  · have hbs : ¬ Bare s [] := by
      intro hbs
      have back := bare_map e.symm [] (root_mem s) hbs
      have he := bare_only_root t (e.backward [])
        ((degree_map e.symm [] (root_mem s)) ▸ hds) back
      exact hb (by change Bare t (e.backward []) at back; simpa [he] using back)
    obtain ⟨q,hq,hqd⟩ : ∃ q ∈ neighbors t [], (neighbors t q).length = 1 := by
      simpa only [Bare, not_forall, not_not, exists_prop] using hb
    obtain ⟨v,hv,hvd⟩ : ∃ v ∈ neighbors s [], (neighbors s v).length = 1 := by
      simpa only [Bare, not_forall, not_not, exists_prop] using hbs
    have tq := root_terminal t ht hlt q hq hqd
    have sv := root_terminal s hs hls v hv hvd
    have lastmap : (terminals s).getLast? = some (e.forward q) := by
      rw [← e.forward_terminals, List.getLast?_map, tq.1]
      rfl
    have heq : e.forward q = v := Option.some.inj (lastmap.symm.trans sv.1)
    have hpq : [] ∈ neighbors t q := by simp [tq.2]
    have hmap : e.forward [] ∈ neighbors s (e.forward q) :=
      (e.forward_neighbors q (neighbor_mem t [] (root_mem t) q hq)).mem_iff.mp
        (List.mem_map.mpr ⟨[], hpq, rfl⟩)
    simpa [heq, sv.2] using hmap

private theorem readouts_from_support (t s : Source)
    (hm : ∀ p : Address, p ∈ material t ↔ p ∈ material s) :
    ∀ p : Address, readout p t = readout p s := by
  induction t generalizing s with
  | of b =>
    cases s with
    | of c =>
      cases b <;> cases c
      · intro p; rfl
      · have hh := hm [false]; simp [material] at hh
      · have hh := hm [false]; simp [material] at hh
      · intro p; rfl
    | mul l r =>
      have hh := hm [true]
      cases b <;> simp [material, List.mem_map, root_mem] at hh
  | mul l r il ir =>
    cases s with
    | of b =>
      have hh := hm [true]
      cases b <;> simp [material, List.mem_map, root_mem] at hh
    | mul a b =>
      have hl : ∀ p : Address, p ∈ material l ↔ p ∈ material a := by
        intro p
        simpa [material, List.mem_map] using hm (false :: p)
      have hr : ∀ p : Address, p ∈ material r ↔ p ∈ material b := by
        intro p
        simpa [material, List.mem_map] using hm (true :: p)
      intro p
      cases p with
      | nil => rfl
      | cons c p =>
        cases c
        · exact il a hl p
        · exact ir b hr p

/-- Universal rigidity of the original C presentation, including every material
coordinate and therefore every original left/right edge and logical constructor. -/
theorem original_rigidity (t s : Source) (ht : D t) (hs : D s)
    (hlt : 3 ≤ (leaves t).length) (hls : 3 ≤ (leaves s).length)
    (e : OrderedIso t s) :
    e.forward [] = [] ∧ (∀ p ∈ material t, e.forward p = p) ∧ t = s := by
  have root := original_root t s ht hs hlt hls e
  have coords := coordinates_from_root e root
  have backroot := original_root s t hs ht hls hlt e.symm
  have back := coordinates_from_root e.symm backroot
  have hm (p : Address) : p ∈ material t ↔ p ∈ material s := by
    constructor
    · intro hp; simpa [coords p hp] using e.forward_mem p hp
    · intro hp
      have hb : e.backward p = p := back p hp
      simpa only [hb] using e.backward_mem p hp
  refine ⟨root,coords,?_⟩
  exact (ActualTreeReadoutAcquisition.source_foundation.2.2.1 t s
    (fun p _ => (readouts_from_support t s hm p).symm)).symm


private theorem material_nodup (t : Source) : (material t).Nodup := by
  induction t with
  | of b => cases b <;> simp [material]
  | mul l r il ir =>
    simp only [material, List.nodup_cons, List.mem_append, List.mem_map]
    constructor
    · simp
    · rw [List.nodup_append]
      refine ⟨il.map (fun _ _ he => (List.cons.inj he).2),
        ir.map (fun _ _ he => (List.cons.inj he).2), ?_⟩
      intro x hx y hy he
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
      cases he

/-- A finite labelled input. No root, term, validity proof or size advice occurs. -/
structure FiniteInput where
  n : Nat
  adjacent : Fin n → List (Fin n)
  terminalOrder : List (Fin n)

/-- The candidate records every input vertex in its own original material coordinates. -/
structure Recovery where
  term : Source
  coordinates : List Address
  deriving DecidableEq

private def birthCheck : Source → Bool
  | .of _ => true
  | .mul l r => (l != .of true) && birthCheck l && birthCheck r

private theorem birthCheck_iff (t : Source) : birthCheck t = true ↔ D t := by
  induction t with
  | of b =>
    constructor
    · intro _ p; cases p <;> simp [readout]
    · intro _; rfl
  | mul l r il ir =>
    simp only [birthCheck, Bool.and_eq_true, bne_iff_ne, il, ir]
    constructor
    · rintro ⟨⟨hl,dl⟩,dr⟩ p
      cases p with
      | nil =>
        cases l with
        | of b => cases b <;> simp_all [readout]
        | mul a b => simp [readout]
      | cons b p =>
        cases b
        · simpa [readout] using dl p
        · simpa [readout] using dr p
    · intro h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro he
        have hh := h []
        simp [he,readout] at hh
      · intro p
        simpa [readout] using h (false :: p)
      · intro p
        simpa [readout] using h (true :: p)

/-- A fully executable compatibility test on the supplied finite enumeration. -/
def Fits (I : FiniteInput) (R : Recovery) : Prop :=
  R.coordinates.length = I.n ∧ R.coordinates.Perm (material R.term) ∧
  (∀ i : Fin I.n, ((I.adjacent i).map (fun j : Fin I.n => R.coordinates.getD j.val [])).Perm
    (neighbors R.term (R.coordinates.getD i []))) ∧
  I.terminalOrder.map (fun j : Fin I.n => R.coordinates.getD j.val []) = terminals R.term ∧
  birthCheck R.term = true ∧ 3 ≤ (leaves R.term).length

instance (I : FiniteInput) (R : Recovery) : Decidable (Fits I R) := by
  unfold Fits
  infer_instance

/-- Exact-size syntax enumeration, with fuel supplied by the finite input itself. -/
private def catalog : Nat → Nat → List Source
  | 0, _ => []
  | fuel+1, n =>
    (if n = 1 then [.of true] else []) ++
    (if n = 2 then [.of false] else []) ++
    (List.range n).flatMap (fun k =>
      (catalog fuel k).flatMap (fun l =>
        (catalog fuel (n-1-k)).map (fun r => .mul l r)))

private theorem material_positive (t : Source) : 0 < (material t).length :=
  List.length_pos_of_mem (root_mem t)

private theorem catalog_complete (t : Source) (fuel : Nat)
    (h : (material t).length ≤ fuel) : t ∈ catalog fuel (material t).length := by
  induction t generalizing fuel with
  | of b =>
    cases fuel with
    | zero => have := material_positive (.of b); omega
    | succ fuel => cases b <;> simp [catalog,material]
  | mul l r il ir =>
    cases fuel with
    | zero => have := material_positive (.mul l r); omega
    | succ fuel =>
      have pl := material_positive l
      have pr := material_positive r
      have hl : (material l).length ≤ fuel := by simp [material] at h; omega
      have hr : (material r).length ≤ fuel := by simp [material] at h; omega
      simp only [catalog]
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨(material l).length, ?_, ?_⟩
      · simp [material]
      · apply List.mem_flatMap.mpr
        refine ⟨l,il fuel hl,?_⟩
        apply List.mem_map.mpr
        refine ⟨r,?_,rfl⟩
        have he : (material (.mul l r)).length - 1 - (material l).length =
            (material r).length := by simp [material]
        rw [he]
        exact ir fuel hr

private def candidates (I : FiniteInput) : List Recovery :=
  (catalog I.n I.n).flatMap (fun t =>
    (material t).permutations.map (fun c => ⟨t,c⟩))

/-- Total exhaustive recognition; all search bounds are read from the finite input. -/
def recover (I : FiniteInput) : Option Recovery :=
  (candidates I).find? (fun R => decide (Fits I R))

private theorem recover_sound (I : FiniteInput) (R : Recovery) (h : recover I = some R) :
    Fits I R := by
  have hr : decide (Fits I R) = true :=
    List.find?_some (p := fun S => decide (Fits I S)) h
  exact of_decide_eq_true hr

private theorem recover_exists (I : FiniteInput) (R : Recovery) (h : Fits I R) :
    ∃ S, recover I = some S ∧ Fits I S := by
  have hn : (material R.term).length = I.n := h.2.1.length_eq.symm.trans h.1
  have hm : R ∈ candidates I := by
    apply List.mem_flatMap.mpr
    refine ⟨R.term, ?_, ?_⟩
    · rw [← hn]
      exact catalog_complete R.term _ (by omega)
    · apply List.mem_map.mpr
      exact ⟨R.coordinates,List.mem_permutations.mpr h.2.1,by cases R; rfl⟩
  cases hs : recover I with
  | none =>
    have no := List.find?_eq_none.mp hs R hm
    exact False.elim (no (decide_eq_true h))
  | some S => exact ⟨S,rfl,recover_sound I S hs⟩



private def coordEquiv (I : FiniteInput) (R : Recovery) (h : Fits I R) :
    Fin I.n ≃ {p // p ∈ material R.term} :=
  (finCongr h.1.symm).trans
    (((material_nodup R.term).perm h.2.1.symm).getEquiv R.coordinates |>.trans
      (Equiv.subtypeEquivRight (fun _ => h.2.1.mem_iff)))

private theorem coordEquiv_apply (I : FiniteInput) (R : Recovery) (h : Fits I R)
    (i : Fin I.n) : (coordEquiv I R h i).val = R.coordinates.getD i [] := by
  change R.coordinates.get ⟨i.val, _⟩ = R.coordinates.getD i []
  exact (List.getD_eq_get _ _ _).symm

private def extend {t s : Source}
    (e : {p // p ∈ material t} ≃ {p // p ∈ material s}) (p : Address) : Address :=
  if hp : p ∈ material t then (e ⟨p,hp⟩).val else []

private theorem extend_coord (I : FiniteInput) (R S : Recovery)
    (hR : Fits I R) (hS : Fits I S) (i : Fin I.n) :
    extend ((coordEquiv I R hR).symm.trans (coordEquiv I S hS))
      (R.coordinates.getD i []) = S.coordinates.getD i [] := by
  rw [← coordEquiv_apply I R hR i, ← coordEquiv_apply I S hS i]
  have hm := (coordEquiv I R hR i).property
  simp [extend, hm]

private theorem transfer_neighbors (I : FiniteInput) (R S : Recovery)
    (hR : Fits I R) (hS : Fits I S) (p : Address) (hp : p ∈ material R.term) :
    ((neighbors R.term p).map
      (extend ((coordEquiv I R hR).symm.trans (coordEquiv I S hS)))).Perm
    (neighbors S.term
      (extend ((coordEquiv I R hR).symm.trans (coordEquiv I S hS)) p)) := by
  let i := (coordEquiv I R hR).symm ⟨p,hp⟩
  have hi : R.coordinates.getD i [] = p := by
    rw [← coordEquiv_apply I R hR i]
    exact congrArg Subtype.val ((coordEquiv I R hR).apply_symm_apply ⟨p,hp⟩)
  have hr := hR.2.2.1 i
  rw [hi] at hr
  have hs := hS.2.2.1 i
  have he := extend_coord I R S hR hS i
  rw [hi] at he
  rw [he]
  apply (hr.map _).symm.trans
  simpa only [List.map_map, Function.comp_def, extend_coord] using hs

private theorem transfer_terminals (I : FiniteInput) (R S : Recovery)
    (hR : Fits I R) (hS : Fits I S) :
    (terminals R.term).map
      (extend ((coordEquiv I R hR).symm.trans (coordEquiv I S hS))) =
      terminals S.term := by
  rw [← hR.2.2.2.1, List.map_map]
  simpa only [Function.comp_def, extend_coord] using hS.2.2.2.1

private def candidateIso (I : FiniteInput) (R S : Recovery)
    (hR : Fits I R) (hS : Fits I S) : OrderedIso R.term S.term where
  forward := extend ((coordEquiv I R hR).symm.trans (coordEquiv I S hS))
  backward := extend ((coordEquiv I S hS).symm.trans (coordEquiv I R hR))
  forward_mem p hp := by simp only [extend, dif_pos hp]; exact Subtype.property _
  backward_mem p hp := by simp only [extend, dif_pos hp]; exact Subtype.property _
  left_inv p hp := by
    simp only [extend, dif_pos hp]
    rw [dif_pos (Subtype.property _)]
    simp
  right_inv p hp := by
    simp only [extend, dif_pos hp]
    rw [dif_pos (Subtype.property _)]
    simp
  forward_neighbors := transfer_neighbors I R S hR hS
  forward_terminals := transfer_terminals I R S hR hS

private theorem fits_unique (I : FiniteInput) (R S : Recovery)
    (hR : Fits I R) (hS : Fits I S) : R = S := by
  have rigid := original_rigidity R.term S.term
    ((birthCheck_iff R.term).mp hR.2.2.2.2.1)
    ((birthCheck_iff S.term).mp hS.2.2.2.2.1)
    hR.2.2.2.2.2 hS.2.2.2.2.2 (candidateIso I R S hR hS)
  have hc : R.coordinates = S.coordinates := by
    apply List.ext_getElem (hR.1.trans hS.1.symm)
    intro i hi hj
    have hb : i < I.n := by simpa only [hR.1] using hi
    have hm : R.coordinates.getD i [] ∈ material R.term := by
      rw [← coordEquiv_apply I R hR ⟨i,hb⟩]
      exact Subtype.property _
    have he := rigid.2.1 _ hm
    change extend ((coordEquiv I R hR).symm.trans (coordEquiv I S hS))
      (R.coordinates.getD i []) = R.coordinates.getD i [] at he
    rw [extend_coord I R S hR hS ⟨i,hb⟩] at he
    simpa only [List.getD_eq_getElem R.coordinates [] hi,
      List.getD_eq_getElem S.coordinates [] hj] using he.symm
  cases R; cases S; simp_all

/-- Uniform exact inverse on the full actual relabelled image. The image witness
is used only here in the proof, never as an argument of recover. -/
private theorem inverse_correct (I : FiniteInput) (R : Recovery) (h : Fits I R) :
    recover I = some R ∧ (∀ S, Fits I S → S = R) := by
  obtain ⟨S,hs,hS⟩ := recover_exists I R h
  have he := fits_unique I S R hS h
  exact ⟨he ▸ hs,fun S hS => fits_unique I S R hS h⟩



private theorem terminal_children (t : Source) (p : Address) :
    p ∈ terminals t ↔ p ∈ material t ∧ children t p = [] := by
  induction t generalizing p with
  | of b =>
    cases p with
    | nil => cases b <;> simp [terminals,material,children,readout]
    | cons c p => cases b <;> cases c <;> cases p <;>
        simp [terminals,material,children,readout]
  | mul l r il ir =>
    cases p with
    | nil => simp [terminals,material,children,readout,List.mem_map]
    | cons b p =>
      rw [children_cons]
      cases b
      · simpa [terminals,material,List.mem_map] using il p
      · simpa [terminals,material,List.mem_map] using ir p

private theorem terminal_degree (t : Source) (h : 3 ≤ (leaves t).length)
    (p : Address) (hp : p ∈ material t) :
    p ∈ terminals t ↔ (neighbors t p).length = 1 := by
  by_cases he : p = []
  · subst p
    obtain ⟨l,r,rfl⟩ := three_branch t h
    simp [terminals,neighbors,children,readout,List.mem_map]
  · rw [terminal_children]
    simp only [hp,true_and,neighbors,if_neg he,List.length_append,List.length_singleton]
    constructor
    · intro hc; simp [hc]
    · intro hc
      apply List.length_eq_zero_iff.mp
      omega

private theorem fits_roster (I : FiniteInput) (R : Recovery) (h : Fits I R)
    (i : Fin I.n) : i ∈ I.terminalOrder ↔ (I.adjacent i).length = 1 := by
  let c := fun j : Fin I.n => R.coordinates.getD j []
  have hm : c i ∈ material R.term := by
    rw [show c i = (coordEquiv I R h i).val from (coordEquiv_apply I R h i).symm]
    exact Subtype.property _
  have hd : (I.adjacent i).length = (neighbors R.term (c i)).length := by
    simpa only [List.length_map] using (h.2.2.1 i).length_eq
  rw [hd, ← terminal_degree R.term h.2.2.2.2.2 (c i) hm, ← h.2.2.2.1]
  constructor
  · intro hi; exact List.mem_map.mpr ⟨i,hi,rfl⟩
  · intro hi
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
    have eqc : coordEquiv I R h j = coordEquiv I R h i := by
      apply Subtype.ext
      simpa only [coordEquiv_apply] using he
    have : j = i := (coordEquiv I R h).injective eqc
    simpa [this] using hj

/-- The actual LAB14.2 six-vertex graph, with complete ordered terminals c,d,e. -/
def sixVertex : FiniteInput where
  n := 6
  adjacent i := match i.val with
    | 0 => [1,5]
    | 1 => [2,4,0]
    | 2 => [3,1]
    | 3 => [2]
    | 4 => [1]
    | _ => [0]
  terminalOrder := [3,4,5]

def sixRecovery : Recovery :=
  ⟨.mul (.mul (.of false) (.of true)) (.of true),
    [[],[false],[false,false],[false,false,false],[false,true],[true]]⟩

/-- Sound recognition on arbitrary finite inputs, complete unique recovery on
every actual relabelling, and the existing six-vertex check on that same path. -/
theorem effective_inverse :
    (∀ (I : FiniteInput) (R : Recovery), recover I = some R →
      Fits I R ∧ ∀ i : Fin I.n, i ∈ I.terminalOrder ↔ (I.adjacent i).length = 1) ∧
    (∀ (I : FiniteInput) (R : Recovery), Fits I R →
      recover I = some R ∧ ∀ S, Fits I S → S = R) ∧
    (recover sixVertex = some sixRecovery ∧
      ∀ S, Fits sixVertex S → S = sixRecovery) := by
  refine ⟨?_, ?_, ?_⟩
  · intro I R hr
    have h := recover_sound I R hr
    exact ⟨h,fits_roster I R h⟩
  · exact inverse_correct
  · exact inverse_correct sixVertex sixRecovery (by decide)


end D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition.original_rigidity

#print axioms D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition.effective_inverse
