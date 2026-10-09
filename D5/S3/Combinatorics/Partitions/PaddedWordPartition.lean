/- GID: D5/S3/Combinatorics/Partitions/PaddedWordPartition
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/PaddedWordPartition
   mirror-E: none(waiver:list-recursion-proof)
   anchors: []
   utility: none
   digest: Direct prefix rows and their actual transpose determine both signed fan moments. -/

import D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace D5.S3.Combinatorics.Partitions.PaddedWordPartition
open scoped BigOperators
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge

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


def rows : List Bool → List ℕ
  | [] => []
  | true :: w => (rows w).map (fun x => x + 1)
  | false :: w => rows w ++ [0]

theorem rows_length (w : List Bool) : (rows w).length = w.count false := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp [rows, ih]

theorem rows_bound (w : List Bool) : ∀ x ∈ rows w, x ≤ w.count true := by
  induction w with
  | nil => simp [rows]
  | cons c w ih =>
    cases c
    · simpa [rows] using (show ∀ x ∈ rows w ++ [0], x ≤ w.count true from by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ih x hx
        · simp only [List.mem_singleton] at hx
          subst x
          exact Nat.zero_le _)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      simpa using Nat.add_le_add_right (ih y hy) 1

theorem rows_sorted (w : List Bool) : (rows w).SortedGE := by
  apply List.Pairwise.sortedGE
  induction w with
  | nil => simp [rows]
  | cons c w ih =>
    cases c
    · simpa [rows, List.pairwise_append] using ih
    · exact ih.map (fun x => x + 1) (by intro a b hab; omega)

theorem rows_sum (w : List Bool) : (rows w).sum = scatteredTrueFalseCount w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    cases c <;>
      simp [rows, scatteredTrueFalseCount, List.sum_map_add, ih, rows_length, add_comm]

theorem rows_append_true (w : List Bool) : rows (w ++ [true]) = rows w := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp [rows, ih]

theorem rows_append_false (w : List Bool) :
    rows (w ++ [false]) = w.count true :: rows w := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp [rows, ih]

def oddRows : List ℕ → ℝ
  | [] => 0
  | a :: l => a + oddRows l + 2 * (l.sum : ℝ)

def squareRows (l : List ℕ) : ℝ := (l.map fun x : ℕ => (x : ℝ)^2).sum

theorem list_cast_sum (l : List ℕ) :
    (l.sum : ℝ) = ∑ i : Fin l.length, (l[i.val] : ℝ) := by
  have hs : l.sum = ∑ i : Fin l.length, l[i.val] := by
    conv_lhs => rw [← List.ofFn_getElem (xs := l)]
    rw [List.sum_ofFn]
  exact_mod_cast hs

theorem oddRows_fin (l : List ℕ) :
    oddRows l = ∑ i : Fin l.length, ((2*i.val+1 : ℕ) : ℝ)*(l[i.val] : ℝ) := by
  induction l with
  | nil => simp [oddRows]
  | cons a l ih =>
    rw [oddRows, ih]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
      mul_zero, zero_add, one_mul]
    simp_rw [show ∀ i : Fin l.length,
      (2*((i.val : ℝ)+1)+1)*(l[i.val] : ℝ) =
        (2*(i.val : ℝ)+1)*(l[i.val] : ℝ)+2*(l[i.val] : ℝ) from by intro i; ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← list_cast_sum]
    push_cast
    ring

theorem odd_range (n : ℕ) :
    (∑ i ∈ Finset.range n, ((2*i+1 : ℕ) : ℝ)) = (n : ℝ)^2 := by
  have hs : (∑ i ∈ Finset.range n, (2*i+1)) = n^2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Nat.mul_comm 2,
      Finset.sum_range_id_mul_two]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]; ring
  exact_mod_cast hs

theorem filtered_odd_range (m n : ℕ) (hmn : m ≤ n) :
    (∑ i ∈ Finset.range n, if i < m then ((2*i+1 : ℕ) : ℝ) else 0) =
      (m : ℝ)^2 := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun i => i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, odd_range]

def diagram (w : List Bool) : YoungDiagram := YoungDiagram.ofRowLens (rows w) (rows_sorted w)
def P (w : List Bool) : ℝ :=
  ∑ i : Fin (rows w).length, ((diagram w).rowLen i : ℝ)^2
def R (w : List Bool) : ℝ :=
  ∑ j ∈ Finset.range (w.count true), ((diagram w).transpose.rowLen j : ℝ)^2

theorem diagram_row (w : List Bool) (i : Fin (rows w).length) :
    (diagram w).rowLen i = (rows w)[i] := YoungDiagram.rowLen_ofRowLens i

theorem diagram_row_bound (w : List Bool) (i : ℕ) :
    (diagram w).rowLen i ≤ w.count true := by
  apply Nat.le_of_not_gt
  change ¬ w.count true < (diagram w).rowLen i
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  intro h
  obtain ⟨hi, hj⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.not_lt_of_ge (rows_bound w _ (List.getElem_mem hi))) hj

theorem diagram_col_bound (w : List Bool) (j : ℕ) :
    (diagram w).colLen j ≤ (rows w).length := by
  apply Nat.le_of_not_gt
  change ¬ (rows w).length < (diagram w).colLen j
  rw [← YoungDiagram.mem_iff_lt_colLen]
  intro h
  obtain ⟨hi, _⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact Nat.lt_irrefl _ hi

theorem same_diagram_columns (w : List Bool) : R w = oddRows (rows w) := by
  let μ := diagram w
  let v := (rows w).length
  let u := w.count true
  have hv : ∀ j, μ.colLen j ≤ v := diagram_col_bound w
  have hu : ∀ i, μ.rowLen i ≤ u := diagram_row_bound w
  have hcol : ∀ j,
      (μ.colLen j : ℝ)^2 =
        ∑ i ∈ Finset.range v, if (i,j) ∈ μ then ((2*i+1 : ℕ) : ℝ) else 0 := by
    intro j
    simp_rw [YoungDiagram.mem_iff_lt_colLen]
    exact (filtered_odd_range _ _ (hv j)).symm
  have hrow : ∀ i,
      (∑ j ∈ Finset.range u, if (i,j) ∈ μ then ((2*i+1 : ℕ) : ℝ) else 0) =
        ((2*i+1 : ℕ) : ℝ)*(μ.rowLen i : ℝ) := by
    intro i
    simp_rw [YoungDiagram.mem_iff_lt_rowLen]
    rw [← Finset.sum_filter]
    have hf : (Finset.range u).filter (fun j => j < μ.rowLen i) =
        Finset.range (μ.rowLen i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      have := hu i
      omega
    rw [hf]
    simp [nsmul_eq_mul, mul_comm]
    ring
  unfold R
  simp only [YoungDiagram.rowLen_transpose]
  change (∑ j ∈ Finset.range u, (μ.colLen j : ℝ)^2) = _
  simp_rw [hcol]
  rw [Finset.sum_comm]
  simp_rw [hrow]
  rw [oddRows_fin, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagram_row]
  simp only [Fin.getElem_fin]

theorem same_diagram_rows (w : List Bool) : P w = squareRows (rows w) := by
  unfold P squareRows
  simp_rw [diagram_row]
  rw [← List.ofFn_getElem_eq_map (rows w) (fun x : ℕ => (x : ℝ)^2), List.sum_ofFn]
  simp only [Fin.getElem_fin]

theorem direct_list_fan (w : List Bool) :
    G w = ⟨w.count true, w.count false,
      2*(scatteredTrueFalseCount w : ℝ)-(w.count true : ℝ)*(w.count false : ℝ),
      (w.count true : ℝ)^2*(w.count false : ℝ)-
        6*(w.count true : ℝ)*(scatteredTrueFalseCount w : ℝ)+6*squareRows (rows w),
      -(w.count true : ℝ)*(w.count false : ℝ)^2+
        6*(w.count false : ℝ)*(scatteredTrueFalseCount w : ℝ)-6*oddRows (rows w)⟩ := by
  induction w using List.reverseRecOn with
  | nil => apply Five.ext <;> simp [G_nil, zeroFive,
      squareRows, oddRows, rows, scatteredTrueFalseCount]
  | append_singleton w c ih =>
    rw [G_append, ih]
    cases c <;> apply Five.ext <;>
      simp [U, List.count_append, scattered_true_false_count_append_letter,
        rows_append_true, rows_append_false, squareRows, oddRows, rows_sum,
        Nat.cast_add] <;> ring

theorem all_word_direct (w : List Bool) :
    G w = ⟨w.count true, w.count false,
      2*(scatteredTrueFalseCount w : ℝ)-(w.count true : ℝ)*(w.count false : ℝ),
      (w.count true : ℝ)^2*(w.count false : ℝ)-
        6*(w.count true : ℝ)*(scatteredTrueFalseCount w : ℝ)+6*P w,
      -(w.count true : ℝ)*(w.count false : ℝ)^2+
        6*(w.count false : ℝ)*(scatteredTrueFalseCount w : ℝ)-6*R w⟩ := by
  rw [same_diagram_rows, same_diagram_columns]
  exact direct_list_fan w
end D5.S3.Combinatorics.Partitions.PaddedWordPartition
