/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Canonical blocking-factor classes, realized cylinders and relative prefix projections. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeConstructorArrays
import D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedNavigationCompiler
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
import Mathlib.Data.List.TakeDrop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeRelativePrefixBoxes

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeConstructorArrays (Canonical S W Allowed scalarReadout extend)
open NativeRankedNavigationCompiler (pathCost)
open NativeFiniteMenuCode (spine)

/-- The Boolean second coordinate denotes the integers zero and one. -/
abbrev Factor := Nat × Bool

/-- Last-edge indicator; the empty-word value is unused for a residual. -/
def lastRight : Address → Bool
  | [] => false
  | [b] => b
  | _ :: c :: r => lastRight (c :: r)

/-- The complete factor of an actually present blocking leaf. True is alpha. -/
def leafFactor (r : Address) (b : Bool) : Factor :=
  (pathCost r + if b then 2 else 1, if r = [] then b else lastRight r)

/-- Follow actual constructors, stopping at the first actual leaf. -/
def gamma : Address → Source → Factor
  | q, .of b => leafFactor q b
  | [], .mul _ _ => (0,false)
  | false :: q, .mul l _ => gamma q l
  | true :: q, .mul _ r => gamma q r

/-- The factor attached to a prefix position and a genuine leaf label. -/
def descriptor (q : Address) (i : Nat) (b : Bool) : Factor := leafFactor (q.drop i) b

/-- The only possible pair of distinct complete-factor descriptors. -/
def DoubleAt (q : Address) (i : Nat) : Prop :=
  i + 1 < q.length ∧ q[i]? = some false

/-- The entire original level, inside the exact existing canonical carrier. -/
def level (d : Nat) (q : Address) (z : Factor) : Set (S d) :=
  {u | gamma q u.val = z}

/-- Actual readout image of the entire level; no independent array is introduced. -/
def projection (d : Nat) (q v : Address) (z : Factor) : Set Reply :=
  (fun u : S d => readout v u.val) '' level d q z

/-- Literal reply of the corresponding genuine source leaf. -/
def leafReply (b : Bool) : Reply := if b then .alpha else .beta

private theorem leaf_positive (q : Address) (b : Bool) : 0 < (leafFactor q b).1 := by
  cases b <;> simp [leafFactor] <;> omega

private theorem cost_gap (q : Address) (i : Nat) :
    pathCost (q.drop i) + min i q.length ≤ pathCost q := by
  induction q generalizing i with
  | nil => simp [pathCost]
  | cons a q ih =>
      cases i with
      | zero => simp
      | succ i =>
          have h := ih i
          cases a <;> simp [List.drop_succ_cons, pathCost, Nat.min_comm] at * <;> omega

private theorem last_cons (a : Bool) (r : Address) (hr : r ≠ []) :
    lastRight (a :: r) = lastRight r := by
  cases r with
  | nil => contradiction
  | cons b r => rfl

private theorem same_position (q : Address) (i : Nat) (b c : Bool) :
    descriptor q i b = descriptor q i c ↔ b = c := by
  cases b <;> cases c <;> simp [descriptor, leafFactor]

private theorem descriptor_collision (q : Address) (i j : Nat) (b c : Bool)
    (hi : i ≤ q.length) (hj : j ≤ q.length) (hij : i < j) :
    descriptor q i b = descriptor q j c ↔
      b = false ∧ c = true ∧ j = i+1 ∧ DoubleAt q i := by
  induction q generalizing i j with
  | nil => simp at hi hj; omega
  | cons a q ih =>
      cases i with
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              have h := ih i j (by simpa using hi) (by simpa using hj) (by omega)
              simpa only [descriptor, List.drop_succ_cons, DoubleAt, List.length_cons,
                List.getElem?_cons_succ, Nat.succ_eq_add_one, Nat.add_lt_add_iff_right,
                Nat.add_left_inj] using h
      | zero =>
          cases j with
          | zero => omega
          | succ j =>
              have hg := cost_gap q j
              have hbound : j ≤ q.length := by simpa using hj
              rw [Nat.min_eq_left hbound] at hg
              constructor
              · intro he
                have hf := congrArg Prod.fst he
                change pathCost (a :: q) + (if b then 2 else 1) =
                  pathCost (q.drop j) + (if c then 2 else 1) at hf
                have shapes : a = false ∧ b = false ∧ c = true ∧ j = 0 := by
                  cases a <;> cases b <;> cases c <;> simp [pathCost] at hf ⊢ <;> omega
                rcases shapes with ⟨rfl,rfl,rfl,rfl⟩
                have hn : q ≠ [] := by
                  intro hq
                  subst q
                  have hs := congrArg Prod.snd he
                  simp [descriptor, leafFactor, lastRight] at hs
                exact ⟨rfl,rfl,rfl, by simp [DoubleAt]; simpa using List.length_pos_iff.mpr hn⟩
              · rintro ⟨rfl,rfl,he,hd⟩
                have : j = 0 := by omega
                subst j
                have ha : a = false := by simpa [DoubleAt] using hd.2
                have hn : q ≠ [] := by
                  have := hd.1
                  cases q <;> simp_all
                subst a
                simp [descriptor, leafFactor, pathCost, hn, last_cons false q hn, Nat.add_comm] <;> omega

private theorem double_descriptors (q : Address) (i : Nat) (h : DoubleAt q i)
    (j : Nat) (b : Bool) (hj : j ≤ q.length) :
    descriptor q j b = descriptor q i false ↔
      (j = i ∧ b = false) ∨ (j = i+1 ∧ b = true) := by
  have hi1 : i+1 < q.length := h.1
  have hi : i ≤ q.length := by omega
  have pair := (descriptor_collision q i (i+1) false true hi (by omega) (by omega)).mpr
    ⟨rfl,rfl,rfl,h⟩
  constructor
  · intro he
    rcases lt_trichotomy j i with hlt | hji | hgt
    · have hc := (descriptor_collision q j i b false hj hi hlt).mp he
      cases hc.2.1
    · subst j
      exact Or.inl ⟨rfl,(same_position q i b false).mp he⟩
    · have hc := (descriptor_collision q i j false b hi hj hgt).mp he.symm
      exact Or.inr ⟨hc.2.2.1,hc.2.1⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact pair.symm

private theorem descriptor_class (q : Address) (i : Nat) (b : Bool)
    (hi : i ≤ q.length) :
    (∀ j : Nat, j ≤ q.length → ∀ c : Bool,
      descriptor q j c = descriptor q i b ↔ j = i ∧ c = b) ∨
    ∃ k : Nat, DoubleAt q k ∧ descriptor q i b = descriptor q k false := by
  classical
  by_cases hd : ∃ k : Nat, DoubleAt q k ∧ descriptor q i b = descriptor q k false
  · obtain ⟨k,hk,he⟩ := hd
    exact Or.inr ⟨k,hk,he⟩
  · left
    intro j hj c
    constructor
    · intro he
      rcases lt_trichotomy j i with hlt | hji | hgt
      · have hc := (descriptor_collision q j i c b hj hi hlt).mp he
        exact (hd ⟨j,hc.2.2.2,he.symm.trans (by rw [hc.1])⟩).elim
      · subst j
        exact ⟨rfl,(same_position q i c b).mp he⟩
      · have hc := (descriptor_collision q i j b c hi hj hgt).mp he.symm
        exact (hd ⟨i,hc.2.2.2,by rw [hc.1]⟩).elim
    · rintro ⟨rfl,rfl⟩; rfl

private theorem gamma_zero (q : Address) (u : Source) :
    gamma q u = (0,false) ↔ readout q u = .branch := by
  induction q generalizing u with
  | nil =>
      cases u with
      | of b => cases b <;> simp [gamma, leafFactor, pathCost, readout]
      | mul l r => simp [gamma, readout]
  | cons a q ih =>
      cases u with
      | of b =>
          have h := leaf_positive (a :: q) b
          simp only [gamma, readout, reduceCtorEq, iff_false]
          intro he
          have := congrArg Prod.fst he
          simp at this
          omega
      | mul l r => cases a <;> simpa [gamma, readout] using ih _

private theorem gamma_at_leaf (q : Address) (i : Nat) (b : Bool) (u : Source)
    (hi : i ≤ q.length) (h : readout (q.take i) u = leafReply b) :
    gamma q u = descriptor q i b := by
  induction i generalizing q u with
  | zero =>
      cases u with
      | of c => cases b <;> cases c <;> simp_all [readout, leafReply, gamma, descriptor]
      | mul l r => cases b <;> simp [readout, leafReply] at h
  | succ i ih =>
      cases q with
      | nil => simp at hi
      | cons a q =>
          cases u with
          | of c => cases b <;> simp [readout, leafReply] at h
          | mul l r =>
              cases a <;> simpa [gamma, descriptor] using
                ih q _ (by simpa using hi) (by simpa [readout] using h)

private theorem actual_blocker (q : Address) (u : Source) :
    (gamma q u = (0,false) ∧ readout q u = .branch) ∨
    ∃ i : Nat, i ≤ q.length ∧ ∃ b : Bool,
      readout (q.take i) u = leafReply b ∧ gamma q u = descriptor q i b := by
  induction q generalizing u with
  | nil =>
      cases u with
      | of b => exact Or.inr ⟨0,by simp,b,by cases b <;> rfl,rfl⟩
      | mul l r => exact Or.inl ⟨rfl,rfl⟩
  | cons a q ih =>
      cases u with
      | of b => exact Or.inr ⟨0,by simp,b,by cases b <;> rfl,rfl⟩
      | mul l r =>
          have h := ih (if a then r else l)
          rcases h with h | ⟨i,hi,b,hr,hg⟩
          · left; cases a <;> simpa [gamma, readout] using h
          · right
            refine ⟨i+1,by simp; omega,b,?_,?_⟩
            · cases a <;> simpa [readout] using hr
            · cases a <;> simpa [gamma, descriptor] using hg

private theorem spine_cylinder (a : Address) (d : Nat) (t : Source)
    (ha : a.length < d) (ht : Canonical (d - a.length) t) :
    Canonical d (spine a t) ∧ readout a (spine a t) = readout [] t := by
  induction a generalizing d with
  | nil =>
      constructor
      · simpa [spine] using ht
      · rfl
  | cons b a ih =>
      cases d with
      | zero => simp at ha
      | succ d =>
          have h := ih d (by simp at ha; omega) (by simpa using ht)
          have hd : 0 < d := by simp at ha; omega
          have alpha : Canonical d (.of true) := by cases d <;> simp_all [Canonical]
          cases b
          · simpa [spine, List.foldr, Canonical, readout] using
              (show (Canonical d (spine a t) ∧ Canonical d (.of true)) ∧
                readout a (spine a t) = readout [] t from ⟨⟨h.1,alpha⟩,h.2⟩)
          · simpa [spine, List.foldr, Canonical, readout] using
              (show (Canonical d (.of true) ∧ Canonical d (spine a t)) ∧
                readout a (spine a t) = readout [] t from ⟨⟨alpha,h.1⟩,h.2⟩)

private theorem cylinders_attained (d : Nat) (q : Address) (hq : q.length < d) :
    (∀ i : Nat, i ≤ q.length → ∀ b : Bool,
      ∃ u : S d, readout (q.take i) u.val = leafReply b) ∧
    (∃ u : S d, readout q u.val = .branch) := by
  have leaf (a : Address) (ha : a.length < d) (b : Bool) :
      ∃ u : S d, readout a u.val = leafReply b := by
    have ht : Canonical (d - a.length) (.of b) := by
      have : 0 < d-a.length := by omega
      cases h : d-a.length <;> simp_all [Canonical]
    have h := spine_cylinder a d (.of b) ha ht
    exact ⟨⟨spine a (.of b),h.1⟩,by cases b <;> simpa [leafReply, readout] using h.2⟩
  constructor
  · intro i hi b
    exact leaf (q.take i) (by simp [List.length_take]; omega) b
  · have ht : Canonical (d-q.length) (.mul (.of true) (.of true)) := by
      have : 0 < d-q.length := by omega
      cases h : d-q.length with
      | zero => omega
      | succ k =>
          simp only [Canonical]
          cases k <;> simp [Canonical]
    have h := spine_cylinder q d (.mul (.of true) (.of true)) hq ht
    exact ⟨⟨_,h.1⟩,h.2⟩

private theorem path_edge (d : Nat) (q : Address) (hq : q.length < d)
    (i : Nat) (h : DoubleAt q i) (u : S d) :
    Allowed (readout (q.take i) u.val) (readout (q.take (i+1)) u.val) := by
  have hd : 0 < d := by omega
  have hi : i < q.length := by have := h.1; omega
  have take : q.take (i+1) = q.take i ++ [false] := by
    rw [List.take_add_one, h.2]; rfl
  have e := (scalarReadout d hd u).property.2 (q.take i) false
    (by simp [List.length_take]; omega)
  simpa [NativeConstructorArrays.scalarReadout, extend, List.length_take,
    Nat.min_eq_left (by omega : i ≤ q.length), show i < d by omega,
    show i+1 < d by omega, ← take] using e

private theorem pair_tests (d : Nat) (q : Address) (hq : q.length < d)
    (i : Nat) (h : DoubleAt q i) (u : S d) :
    (readout (q.take i) u.val = .beta ∨ readout (q.take (i+1)) u.val = .alpha) ↔
    ((readout (q.take i) u.val = .beta ∨ readout (q.take i) u.val = .branch) ∧
      (readout (q.take (i+1)) u.val = .absent ∨
        readout (q.take (i+1)) u.val = .alpha)) := by
  have e := path_edge d q hq i h u
  cases h₀ : readout (q.take i) u.val <;>
    cases h₁ : readout (q.take (i+1)) u.val <;> simp_all [Allowed]

private theorem level_single (d : Nat) (q : Address) (i : Nat) (b : Bool)
    (hi : i ≤ q.length)
    (hc : ∀ j : Nat, j ≤ q.length → ∀ c : Bool,
      descriptor q j c = descriptor q i b ↔ j = i ∧ c = b) (u : S d) :
    gamma q u.val = descriptor q i b ↔ readout (q.take i) u.val = leafReply b := by
  constructor
  · intro hg
    rcases actual_blocker q u.val with ⟨hz,_⟩ | ⟨j,hj,c,hr,he⟩
    · have hp := leaf_positive (q.drop i) b
      have := congrArg Prod.fst (hz.symm.trans hg)
      simp [descriptor] at this
      omega
    · obtain ⟨rfl,rfl⟩ := (hc j hj c).mp (he.symm.trans hg)
      exact hr
  · exact gamma_at_leaf q i b u.val hi

private theorem level_pair (d : Nat) (q : Address) (hq : q.length < d)
    (i : Nat) (hi : DoubleAt q i) (u : S d) :
    gamma q u.val = descriptor q i false ↔
      ((readout (q.take i) u.val = .beta ∨ readout (q.take i) u.val = .branch) ∧
        (readout (q.take (i+1)) u.val = .absent ∨
          readout (q.take (i+1)) u.val = .alpha)) := by
  rw [← pair_tests d q hq i hi u]
  constructor
  · intro hg
    rcases actual_blocker q u.val with ⟨hz,_⟩ | ⟨j,hj,c,hr,he⟩
    · have hp := leaf_positive (q.drop i) false
      have := congrArg Prod.fst (hz.symm.trans hg)
      simp [descriptor] at this
      omega
    · rcases (double_descriptors q i hi j c hj).mp (he.symm.trans hg) with
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl hr
      · exact Or.inr hr
  · rintro (h | h)
    · exact gamma_at_leaf q i false u.val (by have := hi.1; omega) h
    · have hg := gamma_at_leaf q (i+1) true u.val (by have := hi.1; omega) h
      exact hg.trans ((double_descriptors q i hi (i+1) true (by have := hi.1; omega)).mpr
        (Or.inr ⟨rfl,rfl⟩))

/-- Exact three-case classification, including the entire-level projections. -/
def Classified (d : Nat) (q : Address) (z : Factor) : Prop :=
  (z = (0,false) ∧
    (∀ u : S d, gamma q u.val = z ↔ readout q u.val = .branch) ∧
    projection d q q z = {.branch}) ∨
  (∃ (i : Nat) (b : Bool), i ≤ q.length ∧
    (∀ (j : Nat), j ≤ q.length → ∀ c : Bool,
      descriptor q j c = z ↔ j = i ∧ c = b) ∧
    (∀ u : S d, gamma q u.val = z ↔ readout (q.take i) u.val = leafReply b) ∧
    projection d q (q.take i) z = {leafReply b}) ∨
  (∃ i : Nat, DoubleAt q i ∧ z = descriptor q i false ∧
    (∀ j : Nat, j ≤ q.length → ∀ c : Bool,
      descriptor q j c = z ↔ (j = i ∧ c = false) ∨ (j = i+1 ∧ c = true)) ∧
    (∀ u : S d, gamma q u.val = z ↔
      ((readout (q.take i) u.val = .beta ∨ readout (q.take i) u.val = .branch) ∧
        (readout (q.take (i+1)) u.val = .absent ∨
          readout (q.take (i+1)) u.val = .alpha))) ∧
    projection d q (q.take i) z = {.beta,.branch} ∧
    projection d q (q.take (i+1)) z = {.absent,.alpha})

private theorem classify_level (d : Nat) (q : Address) (hq : q.length < d)
    (z : Factor) (attained : ∃ u : S d, gamma q u.val = z) : Classified d q z := by
  classical
  obtain ⟨u,hu⟩ := attained
  have witnesses := cylinders_attained d q hq
  rcases actual_blocker q u.val with ⟨hz,hr⟩ | ⟨i,hi,b,hr,hg⟩
  · have he : z = (0,false) := hu.symm.trans hz
    rw [he]
    left
    refine ⟨rfl,(fun v => gamma_zero q v.val),?_⟩
    ext y
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (gamma_zero q v.val).mp hv
    · intro hy
      have hy : y = .branch := hy
      subst y
      obtain ⟨v,hv⟩ := witnesses.2
      exact ⟨v,(gamma_zero q v.val).mpr hv,hv⟩
  · have he : z = descriptor q i b := hu.symm.trans hg
    rw [he]
    rcases descriptor_class q i b hi with hs | ⟨k,hk,he⟩
    · right; left
      refine ⟨i,b,hi,hs,level_single d q i b hi hs,?_⟩
      ext y
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact (level_single d q i b hi hs v).mp hv
      · intro hy
        have hy : y = leafReply b := hy
        subst y
        obtain ⟨v,hv⟩ := witnesses.1 i hi b
        exact ⟨v,(level_single d q i b hi hs v).mpr hv,hv⟩
    · right; right
      refine ⟨k,hk,he,?_,?_,?_,?_⟩
      · intro j hj c; rw [he]; exact double_descriptors q k hk j c hj
      · intro v; rw [he]; exact level_pair d q hq k hk v
      all_goals
        obtain ⟨v,hv⟩ := witnesses.1 k (by have := hk.1; omega) false
        obtain ⟨w,hw⟩ := witnesses.1 (k+1) (by have := hk.1; omega) true
        have vg : gamma q v.val = descriptor q i b := by
          rw [he]; exact gamma_at_leaf q k false v.val (by have := hk.1; omega) hv
        have wg : gamma q w.val = descriptor q i b := by
          rw [he]
          exact (gamma_at_leaf q (k+1) true w.val (by have := hk.1; omega) hw).trans
            ((double_descriptors q k hk (k+1) true (by have := hk.1; omega)).mpr
              (Or.inr ⟨rfl,rfl⟩))
        have ev := path_edge d q hq k hk v
        have ew := path_edge d q hq k hk w
        have va : readout (q.take (k+1)) v.val = .absent := by
          change readout (q.take k) v.val = .beta at hv
          rw [hv] at ev
          cases h : readout (q.take (k+1)) v.val <;> simp_all [Allowed]
        have wb : readout (q.take k) w.val = .branch := by
          change readout (q.take (k+1)) w.val = .alpha at hw
          rw [hw] at ew
          cases h : readout (q.take k) w.val <;> simp_all [Allowed]
      · ext y
        constructor
        · rintro ⟨x,hx,rfl⟩
          rw [he] at hx
          exact ((level_pair d q hq k hk x).mp hx).1
        · intro hy
          rcases hy with hy | hy
          · exact ⟨v,vg,hv.trans hy.symm⟩
          · exact ⟨w,wg,wb.trans hy.symm⟩
      · ext y
        constructor
        · rintro ⟨x,hx,rfl⟩
          rw [he] at hx
          exact ((level_pair d q hq k hk x).mp hx).2
        · intro hy
          rcases hy with hy | hy
          · exact ⟨v,vg,va.trans hy.symm⟩
          · exact ⟨w,wg,hw.trans hy.symm⟩

private theorem box_from_classification (d : Nat) (q : Address) (z : Factor)
    (hc : Classified d q z) :
    level d q z = {u : S d | ∀ v : Address, v.IsPrefix q →
      readout v u.val ∈ projection d q v z} := by
  ext u
  constructor
  · intro hu v _; exact ⟨u,hu,rfl⟩
  · intro h
    rcases hc with ⟨_,test,proj⟩ | ⟨i,b,_,_,test,proj⟩ | ⟨i,_,_,_,test,pl,pr⟩
    · exact (test u).mpr (by simpa [proj] using h q List.prefix_rfl)
    · exact (test u).mpr (by simpa [proj] using h (q.take i) (List.take_prefix i q))
    · exact (test u).mpr ⟨by simpa [pl] using h (q.take i) (List.take_prefix i q),
        by simpa [pr] using h (q.take (i+1)) (List.take_prefix (i+1) q)⟩

private theorem factor_guard (q : Address) (u : Source) :
    (gamma q u).2 = true → 2 ≤ (gamma q u).1 := by
  induction q generalizing u with
  | nil => cases u with
    | of b => cases b <;> simp [gamma, leafFactor, pathCost]
    | mul l r => simp [gamma]
  | cons a q ih => cases u with
    | of b =>
        have hp : 0 < pathCost (a :: q) := by cases a <;> simp [pathCost] <;> omega
        cases b <;> simp [gamma, leafFactor] <;> omega
    | mul l r => cases a <;> simpa [gamma] using ih _

/-- Every attained blocking factor has exactly its actual relative prefix box,
with all cylinders and both collision alternatives realized canonically. -/
theorem canonical_factor_levels (d : Nat) (q : Address)
    (hq : q.length < d) (z : Factor) (attained : ∃ u : S d, gamma q u.val = z) :
    level d q z = {u : S d | ∀ v : Address, v.IsPrefix q →
      readout v u.val ∈ projection d q v z} ∧
    Classified d q z ∧
    (∀ (i j : Nat) (b c : Bool), i ≤ q.length → j ≤ q.length → i < j →
      (descriptor q i b = descriptor q j c ↔
        b = false ∧ c = true ∧ j = i+1 ∧ DoubleAt q i)) ∧
    (∀ i : Nat, i ≤ q.length → ∀ b : Bool,
      ∃ u : S d, readout (q.take i) u.val = leafReply b) ∧
    (∃ u : S d, readout q u.val = .branch) ∧
    (∀ u : Source, (gamma q u).2 = true → 2 ≤ (gamma q u).1) ∧
    (∀ u : Source, readout q u = .absent →
      ∃ i : Nat, i < q.length ∧ ∃ b : Bool,
        readout (q.take i) u = leafReply b ∧ gamma q u = descriptor q i b) := by
  have hc := classify_level d q hq z attained
  have wa := cylinders_attained d q hq
  refine ⟨box_from_classification d q z hc,hc,?_,wa.1,wa.2,factor_guard q,?_⟩
  · intro i j b c hi hj hij; exact descriptor_collision q i j b c hi hj hij
  · intro u ha
    rcases actual_blocker q u with ⟨_,hr⟩ | ⟨i,hi,b,hr,hg⟩
    · rw [ha] at hr; cases hr
    · refine ⟨i,?_,b,hr,hg⟩
      by_contra h
      have he : i = q.length := by omega
      rw [he, List.take_length, ha] at hr
      cases b <;> cases hr

#print axioms canonical_factor_levels

end D5.S3.Arith.FibonacciAtomic.Observer.NativeRelativePrefixBoxes
