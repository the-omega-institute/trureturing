/- GID: D5/S3/Combinatorics/Partitions/BinaryWordFan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/BinaryWordFan
   mirror-E: none(waiver:list-recursion-proof)
   anchors: []
   utility: none
   digest: Actual positive binary paths have signed fan moments compatible with concatenation and reversal. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.BinaryWordFan
open scoped BigOperators

abbrev Plane := ℝ × ℝ

structure Five where
  u : ℝ
  v : ℝ
  d : ℝ
  e : ℝ
  f : ℝ

@[ext] theorem Five.ext (x y : Five) (hu : x.u = y.u) (hv : x.v = y.v)
    (hd : x.d = y.d) (he : x.e = y.e) (hf : x.f = y.f) : x = y := by
  cases x; cases y; simp_all

def step (c : Bool) : Plane := if c then (1,0) else (0,1)
def det (x y : Plane) : ℝ := x.1*y.2-x.2*y.1
def edgeArea (x y : Plane) : ℝ := det x y / 2
def edgeRaw (x y : Plane) : Plane :=
  (edgeArea x y*(x.1+y.1)/3, edgeArea x y*(x.2+y.2)/3)
def steps (h : List Bool) : List Plane := h.map step
def p (h : List Bool) (i : ℕ) : Plane := ((steps h).take i).sum
def q (h : List Bool) : Plane := (steps h).sum
def A (h : List Bool) : ℝ :=
  ∑ i ∈ Finset.range h.length, edgeArea (p h i) (p h (i+1))
def S (h : List Bool) : Plane :=
  ∑ i ∈ Finset.range h.length, edgeRaw (p h i) (p h (i+1))
def m (h : List Bool) : Plane := S h - (A h / 2) • q h
def G (h : List Bool) : Five :=
  ⟨(q h).1, (q h).2, 2*A h, 12*(m h).1, 12*(m h).2⟩
def zeroFive : Five := ⟨0,0,0,0,0⟩
def star (x y : Five) : Five :=
  let c := x.u*y.v-x.v*y.u
  ⟨x.u+y.u, x.v+y.v, x.d+y.d+c,
    x.e+y.e+3*(y.d*x.u-x.d*y.u)+c*(x.u-y.u),
    x.f+y.f+3*(y.d*x.v-x.d*y.v)+c*(x.v-y.v)⟩
def U (x : Five) (c : Bool) : Five :=
  if c then ⟨x.u+1,x.v,x.d-x.v,x.e-3*x.d-x.u*x.v+x.v,x.f-x.v^2⟩
  else ⟨x.u,x.v+1,x.d+x.u,x.e+x.u^2,x.f-3*x.d+x.u*x.v-x.u⟩

@[simp] theorem p_last (h : List Bool) : p h h.length = q h := by
  simp [p,q,steps,← List.map_take]
@[simp] theorem q_append (h k : List Bool) : q (h++k) = q h + q k := by
  simp [q,steps]
@[simp] theorem q_single (c : Bool) : q [c] = step c := by simp [q,steps]

theorem p_append_left (h k : List Bool) (i : ℕ) (hi : i ≤ h.length) :
    p (h++k) i = p h i := by
  simp only [p,steps,List.map_append]
  rw [List.take_append_of_le_length (by simpa using hi)]

theorem fan_append (edge : Plane → Plane → ℝ) (h : List Bool) (c : Bool) :
    (∑ i ∈ Finset.range (h++[c]).length,
      edge (p (h++[c]) i) (p (h++[c]) (i+1))) =
    (∑ i ∈ Finset.range h.length, edge (p h i) (p h (i+1))) +
      edge (q h) (q h + step c) := by
  simp only [List.length_append,List.length_singleton,Finset.sum_range_succ]
  have old : (∑ i ∈ Finset.range h.length,
      edge (p (h++[c]) i) (p (h++[c]) (i+1))) =
      ∑ i ∈ Finset.range h.length, edge (p h i) (p h (i+1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [p_append_left _ _ _ (Nat.le_of_lt (Finset.mem_range.mp hi)),
        p_append_left _ _ _ (Nat.add_one_le_iff.mpr (Finset.mem_range.mp hi))]
  rw [old,p_append_left _ _ _ (le_refl _),p_last]
  have last : p (h++[c]) (h.length+1) = q h + step c := by
    rw [← show (h++[c]).length = h.length+1 by simp,p_last,q_append,q_single]
  rw [last]

theorem direct_raw_append (h : List Bool) (c : Bool) :
    A (h++[c]) = A h + det (q h) (step c)/2 ∧
    (S (h++[c])).1 = (S h).1 + det (q h) (step c)*(2*(q h).1+(step c).1)/6 ∧
    (S (h++[c])).2 = (S h).2 + det (q h) (step c)*(2*(q h).2+(step c).2)/6 := by
  have ha := fan_append edgeArea h c
  have hx := fan_append (fun x y => (edgeRaw x y).1) h c
  have hy := fan_append (fun x y => (edgeRaw x y).2) h c
  simp only [A,S,Prod.fst_sum,Prod.snd_sum] at *
  constructor
  · rw [ha]; dsimp [edgeArea,det]; ring
  constructor
  · rw [hx]; dsimp [det,edgeRaw,edgeArea]; ring
  · rw [hy]; dsimp [det,edgeRaw,edgeArea]; ring

@[simp] theorem G_nil : G [] = zeroFive := by
  apply Five.ext <;> simp [G,q,steps,A,S,m,zeroFive]

theorem G_append (h : List Bool) (c : Bool) : G (h++[c]) = U (G h) c := by
  obtain ⟨ha,hx,hy⟩ := direct_raw_append h c
  cases c <;> apply Five.ext <;>
    simp [G,U,m,q_append,q_single,ha,hx,hy,step,det] <;> ring

theorem direct_accumulator (h : List Bool) : G h = h.foldl U zeroFive := by
  have transport := List.foldl_hom G
    (g₁ := fun w c => w++[c]) (g₂ := U) (l := h) (init := [])
    (fun w c => (G_append w c).symm)
  have hfold : h.foldl (fun w c => w++[c]) [] = h := by
    rw [List.foldl_append_eq_append]
    change h.flatMap (fun c => [c]) = h
    exact List.flatMap_singleton' h
  rw [G_nil,hfold] at transport
  exact transport.symm

theorem G_concat (h k : List Bool) : G (h++k) = star (G h) (G k) := by
  rw [direct_accumulator, List.foldl_append, ← direct_accumulator h, direct_accumulator k]
  have transport := List.foldl_hom (star (G h))
    (g₁ := U) (g₂ := U) (l := k) (init := zeroFive) (by
      intro z c
      cases c <;> apply Five.ext <;> simp [U,star] <;> ring)
  have hz : star (G h) zeroFive = G h := by
    apply Five.ext <;> simp [star,zeroFive]
  simpa only [hz] using transport

theorem G_reverse (w : List Bool) :
    G w.reverse = ⟨(G w).u,(G w).v,-(G w).d,(G w).e,(G w).f⟩ := by
  induction w using List.reverseRecOn with
  | nil => apply Five.ext <;> simp [G_nil,zeroFive]
  | append_singleton w c ih =>
    rw [List.reverse_append, List.reverse_singleton, G_concat, ih, G_append]
    have hs : G [c] = U zeroFive c := by simpa using G_append [] c
    rw [hs]
    cases c <;> apply Five.ext <;> simp [star,U,zeroFive] <;> ring

end D5.S3.Combinatorics.Partitions.BinaryWordFan
