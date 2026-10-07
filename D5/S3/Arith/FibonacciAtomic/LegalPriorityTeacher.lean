/- GID: D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LegalPriorityTeacher
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Two effective position pairs classify priority teachers on every seam-legal history. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import Mathlib.Data.List.ChainOfFn
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher

open LiteralWindowEnd (Window first last bits flatten)
open D5.S3.Arith.ZeckendorfFutureKernel (legal)

abbrev Input (n : ℕ) := Fin n → Window

structure Roles (n : ℕ) where
  p : Fin n
  q : Fin n
  r : Fin n
  pq : p < q
  qr : q < r

def Legal {n : ℕ} (x : Input n) : Prop := legal false (flatten (List.ofFn x))

def edge {n : ℕ} (i j : Fin n) : Option (Fin n × Fin n) :=
  if i.val + 1 < j.val then some (i, j) else none

def signature {n : ℕ} (t : Roles n) := (edge t.p t.q, edge t.q t.r)

def gate {n : ℕ} (x : Input n) (i j : Fin n) : Bool := last (x i) && first (x j)

def teacher {n : ℕ} (t : Roles n) (x : Input n) : Fin 3 :=
  if gate x t.p t.q then 1 else if gate x t.q t.r then 2 else 0

/-- A sparse probe uses actual windows and retains all intervening null positions. -/
def probe {n : ℕ} (i j : Fin n) : Input n :=
  fun a => if a = i then .high else if a = j then .low else .zero

/-- Flattened-bit legality is exactly the absence of occupied adjacent seams. -/
theorem legal_iff {n : ℕ} (x : Input n) : Legal x ↔
      ∀ i j : Fin n, i.val + 1 = j.val → ¬ (last (x i) = true ∧ first (x j) = true) := by
  have legal_list (w : List Window) (s : Bool) :
      legal s (flatten w) ↔
        (∀ b ∈ w.head?, ¬ (s = true ∧ first b = true)) ∧
        w.IsChain (fun a b => ¬ (last a = true ∧ first b = true)) := by
    induction w generalizing s with
    | nil => simp [flatten, legal]
    | cons a w ih =>
      have ha : legal s (bits a ++ flatten w) ↔
          ¬ (s = true ∧ first a = true) ∧ legal (last a) (flatten w) := by
        cases s <;> cases a <;> simp [bits, first, last, legal]
      change legal s (bits a ++ flatten w) ↔ _
      rw [ha, ih]
      cases w <;> simp [List.isChain_cons]
  rw [Legal, legal_list]
  simp only [Bool.false_eq_true, false_and, not_false_eq_true, implies_true,
    true_and, List.isChain_ofFn]
  constructor
  · intro h i j hij
    have hj : i.val + 1 < n := hij ▸ j.isLt
    simpa only [Fin.eta, Fin.ext_iff, hij] using h i.val hj
  · intro h i hi
    exact h ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl

/-- Equality on the complete legal input language is exactly equality of the
two ordered effective edges, including their separate absent values. -/
theorem result {n : ℕ} (t u : Roles n) :
    (∀ x : Input n, Legal x → teacher t x = teacher u x) ↔
      signature t = signature u := by
  have probe_legal (i j : Fin n) (hij : i.val + 1 < j.val) : Legal (probe i j) := by
    have hji : j ≠ i := by intro h; have := congrArg Fin.val h; omega
    apply (legal_iff _).2
    intro a b hab hbad
    have hp : last (probe i j a) = true ↔ a = i := by
      by_cases ha : a = i <;> by_cases hj : a = j <;>
        simp_all [probe, first, last]
    have hq : first (probe i j b) = true ↔ b = j := by
      by_cases hb : b = i <;> by_cases hj : b = j <;>
        simp_all [probe, first, last]
    have ha := hp.mp hbad.1
    have hb := hq.mp hbad.2
    subst a; subst b
    omega
  have probe_gate (i j a b : Fin n) (hij : i.val < j.val) :
      gate (probe i j) a b = true ↔ a = i ∧ b = j := by
    have hji : j ≠ i := by intro h; have := congrArg Fin.val h; omega
    by_cases ha : a = i <;> by_cases haj : a = j <;>
      by_cases hb : b = i <;> by_cases hbj : b = j <;>
      simp_all [gate, probe, first, last]
  have teacher_one (v : Roles n) (x : Input n) :
      teacher v x = 1 ↔ gate x v.p v.q = true := by
    cases h : gate x v.p v.q <;> cases h' : gate x v.q v.r <;>
      simp [teacher, h, h']
  have teacher_two (v : Roles n) (x : Input n) :
      teacher v x = 2 ↔ gate x v.p v.q = false ∧ gate x v.q v.r = true := by
    cases h : gate x v.p v.q <;> cases h' : gate x v.q v.r <;>
      simp [teacher, h, h']
  constructor
  · intro h
    have first_edge (v w : Roles n)
        (hh : ∀ x, Legal x → teacher v x = teacher w x)
        (hv : v.p.val + 1 < v.q.val) : edge v.p v.q = edge w.p w.q := by
      have hx := probe_legal v.p v.q hv
      have hon : teacher v (probe v.p v.q) = 1 :=
        (teacher_one _ _).2 ((probe_gate _ _ _ _ v.pq).2 ⟨rfl, rfl⟩)
      have hw : teacher w (probe v.p v.q) = 1 := (hh _ hx).symm.trans hon
      obtain ⟨hp, hq⟩ := (probe_gate _ _ _ _ v.pq).1 ((teacher_one _ _).1 hw)
      simp [edge, hp, hq, hv]
    have second_edge (v w : Roles n)
        (hh : ∀ x, Legal x → teacher v x = teacher w x)
        (hv : v.q.val + 1 < v.r.val) : edge v.q v.r = edge w.q w.r := by
      have hx := probe_legal v.q v.r hv
      have hoff : gate (probe v.q v.r) v.p v.q = false := by
        apply Bool.eq_false_iff.mpr
        intro hz
        have he := (probe_gate _ _ _ _ v.qr).1 hz
        have := congrArg Fin.val he.1
        have := v.pq
        omega
      have hon : teacher v (probe v.q v.r) = 2 :=
        (teacher_two _ _).2 ⟨hoff, (probe_gate _ _ _ _ v.qr).2 ⟨rfl, rfl⟩⟩
      have hw : teacher w (probe v.q v.r) = 2 := (hh _ hx).symm.trans hon
      obtain ⟨hq, hr⟩ := (probe_gate _ _ _ _ v.qr).1 ((teacher_two _ _).1 hw).2
      simp [edge, hq, hr, hv]
    have he₁ : edge t.p t.q = edge u.p u.q := by
      by_cases ht : t.p.val + 1 < t.q.val
      · exact first_edge t u h ht
      · by_cases hu : u.p.val + 1 < u.q.val
        · exact (first_edge u t (fun x hx => (h x hx).symm) hu).symm
        · simp [edge, ht, hu]
    have he₂ : edge t.q t.r = edge u.q u.r := by
      by_cases ht : t.q.val + 1 < t.r.val
      · exact second_edge t u h ht
      · by_cases hu : u.q.val + 1 < u.r.val
        · exact (second_edge u t (fun x hx => (h x hx).symm) hu).symm
        · simp [edge, ht, hu]
    exact Prod.ext he₁ he₂
  · intro h x hx
    have gate_eq (a b c d : Fin n) (hab : a < b) (hcd : c < d)
        (he : edge a b = edge c d) : gate x a b = gate x c d := by
      by_cases hg : a.val + 1 < b.val
      · have hgd : c.val + 1 < d.val := by
          by_contra hn
          simp [edge, hg, hn] at he
        have hp : a = c ∧ b = d := by simpa [edge, hg, hgd] using he
        rw [hp.1, hp.2]
      · have hgd : ¬ c.val + 1 < d.val := by
          intro hd
          simp [edge, hg, hd] at he
        have hzero (i j : Fin n) (hlt : i < j) (hn : ¬ i.val + 1 < j.val) :
            gate x i j = false := by
          have hij : i.val + 1 = j.val := by change i.val < j.val at hlt; omega
          have hz := (legal_iff x).1 hx i j hij
          cases hi : last (x i) <;> cases hj : first (x j) <;> simp_all [gate]
        rw [hzero a b hab hg, hzero c d hcd hgd]
    have hp := gate_eq t.p t.q u.p u.q t.pq u.pq (congrArg Prod.fst h)
    have hq := gate_eq t.q t.r u.q u.r t.qr u.qr (congrArg Prod.snd h)
    simp only [teacher, hp, hq]

end D5.S3.Arith.FibonacciAtomic.LegalPriorityTeacher
