/- GID: D5/S3/Combinatorics/Graph/ThreeColorReciprocal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ThreeColorReciprocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/DUFReciprocal.reciprocal_bound; instance=D5/S3/Combinatorics/Graph/ThreeColorReciprocal.population_bound
   digest: Unrestricted reciprocal lower bound for properly three-colored graphs with mixed degree two. -/

import D5.S3.Combinatorics.Graph.ThreeColorIncidence
import Mathlib.Data.Fin.Tuple.Sort

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ThreeColorReciprocal

open Finset
open scoped Classical

variable {W : Type*} [DecidableEq W]

/-! Polynomial regions for the small mixed-population cases. -/
namespace Certificate
open Lean.Grind.CommRing
def nonnegativeCoefficients : Poly → Bool
  | .num k => decide (0 ≤ k)
  | .add k _ p => decide (0 ≤ k) && nonnegativeCoefficients p

inductive Choice where
  | thin (x : Nat)
  | full (reverse : Bool)
  deriving Inhabited, DecidableEq, Repr

def choices (a b : Nat) : List Choice :=
  (if a = b then [.thin 0] else ((List.range (b-a)).map fun x => .thin (x+1))) ++
    [.full false, .full true]

def sizes (i : Nat) : Choice → Expr × Expr
  | .thin x => (.num x, .num 0)
  | .full reverse =>
    let x := Expr.add (.var (2*i)) (.num 1)
    let y := Expr.add x (.var (2*i+1))
    if reverse then (y,x) else (x,y)

def isFull : Choice → Bool
  | .full _ => true
  | _ => false

def charge (a b i : Nat) (linear : Bool) (choice : Choice) : List (Expr × Expr) :=
  let (x,y) := sizes i choice
  match choice with
  | .thin 0 => []
  | .thin t => if linear then [(.mul (.num 6) x, .num (b-a+1))]
      else [(.num (6*t*t), .num (t+b-a))]
  | .full _ =>
    if linear then
      [(.mul (.num 6) x, .add y (.num (b+1))),
       (.mul (.num 6) y, .add x (.num (a+1)))]
    else
      [(.mul (.num 6) (.pow x 2), .add (.mul x (.add y (.num 1))) (.num b)),
       (.mul (.num 6) (.pow y 2), .add (.mul y (.add x (.num 1))) (.num a))]

def numerator (a b c : Nat) (p q r : Choice) : Expr :=
  let (x,y) := sizes 0 p
  let (z,w) := sizes 1 q
  let (s,t) := sizes 2 r
  let lin := isFull p && isFull q && isFull r
  let terms := [(.num 12, .add (.num (a+1)) (.add x z)),
                (.num 12, .add (.num (b+1)) (.add y s)),
                (.num 12, .add (.num (c+1)) (.add w t))] ++
    charge a b 0 lin p ++ charge a c 1 lin q ++ charge b c 2 lin r
  let ds := terms.map Prod.snd
  let base := Expr.mul (.num (2*(a+b+c : Int)-23)) (ds.foldr Expr.mul (.num 1))
  ((List.range terms.length).map fun i =>
    Expr.mul (terms[i]!).1 ((ds.take i ++ ds.drop (i+1)).foldr Expr.mul (.num 1))).foldl
      Expr.add base

noncomputable def checkMixed (a b c : Nat) : Bool :=
  (choices a b).all fun p => (choices a c).all fun q => (choices b c).all fun r =>
    if isFull p && isFull q && isFull r then true
    else nonnegativeCoefficients (numerator a b c p q r).toPoly_k

noncomputable def checkTotal (m : Nat) : Bool :=
  (List.range (m+1)).all fun a => (List.range (m+1)).all fun b =>
    (List.range (m+1)).all fun c =>
      if a≤b ∧ b≤c ∧ a+b+c=m then checkMixed a b c else true

def side : Choice → Nat → Nat → Nat × Nat
  | .thin t, _, _ => (t,0)
  | .full rev, u, v => if rev then (u+1+v,u+1) else (u+1,u+1+v)

def context (u v w z s t : Nat) : Lean.RArray ℚ :=
  .branch 1 (.leaf u) (.branch 2 (.leaf v)
    (.branch 3 (.leaf w) (.branch 4 (.leaf z) (.branch 5 (.leaf s) (.leaf t)))))

def assembled (b : Int) (terms : List (Expr × Expr)) : Expr :=
  let ds := terms.map Prod.snd
  let base := Expr.mul (.num b) (ds.foldr Expr.mul (.num 1))
  ((List.range terms.length).map fun i =>
    Expr.mul (terms[i]!).1 ((ds.take i ++ ds.drop (i+1)).foldr Expr.mul (.num 1))).foldl
      Expr.add base
end Certificate

open Certificate Lean.Grind.CommRing

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Every feasible population has reciprocal lower expression at least 23/12. -/
theorem population_bound (m : Fin 3 → Nat) (x : Fin 3 → Fin 3 → Nat)
    (hdiag : ∀ i, x i i = 0)
    (hvalid : ∀ i j, i ≠ j → x i j = 0 → m j + x j i ≤ m i)
    :
    (23/12 : ℚ) ≤ max (chargedLower m x) (quadraticLower m x) := by
  have choice_exists (a b x y : Nat) (hab : a ≤ b)
      (hx : x=0 → b+y ≤ a) (hy : y=0 → a+x ≤ b) :
      ∃ p ∈ choices a b, ∃ u v : Nat, side p u v = (x,y) := by
    by_cases hx0 : x=0
    · have hy0 : y=0 := by omega
      have he : a=b := by omega
      refine ⟨.thin 0, ?_, 0, 0, ?_⟩
      · simp [choices, he]
      · simp [side, hx0, hy0]
    by_cases hy0 : y=0
    · refine ⟨.thin x, ?_, 0, 0, ?_⟩
      · have hne : a ≠ b := by omega
        simp only [choices, hne, ↓reduceIte, List.mem_append, List.mem_map]
        left
        exact ⟨x-1, by simp only [List.mem_range]; omega, by congr 1; omega⟩
      · simp [side, hy0]
    by_cases hxy : x ≤ y
    · refine ⟨.full false, ?_, x-1, y-x, ?_⟩
      · simp [choices]
      · simp only [side, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
        omega
    · refine ⟨.full true, ?_, y-1, x-y, ?_⟩
      · simp [choices]
      · simp only [side, ↓reduceIte, Prod.mk.injEq]
        omega

  have context_nonneg (u v w z s t : Nat) (i : Nat) : 0 ≤ (context u v w z s t).get i := by
    simp only [context, Lean.RArray.get]
    cases Nat.ble 1 i <;> cases Nat.ble 2 i <;> cases Nat.ble 3 i <;> cases Nat.ble 4 i <;> cases Nat.ble 5 i <;> exact Nat.cast_nonneg _

  have size_zero (p : Choice) (u v w z s t : Nat) :
      (sizes 0 p).1.denote (context u v w z s t) = ((side p u v).1 : ℚ) ∧
      (sizes 0 p).2.denote (context u v w z s t) = ((side p u v).2 : ℚ) := by
    cases p with
    | thin x => simp [sizes, side, Expr.denote, denoteInt_eq]
    | full r => cases r <;> simp [sizes, side, Expr.denote, Var.denote, context, Lean.RArray.get, Nat.ble, denoteInt_eq]

  have charge_value (a b i u v : Nat) (hab : a ≤ b) (p : Choice) (ctx : Lean.RArray ℚ)
      (hsx : (sizes i p).1.denote ctx = ((side p u v).1 : ℚ))
      (hsy : (sizes i p).2.denote ctx = ((side p u v).2 : ℚ)) :
      (∀ z ∈ charge a b i false p, 0 < z.2.denote ctx) ∧
      ((charge a b i false p).map fun z => z.1.denote ctx / z.2.denote ctx).sum =
        6 * ((side p u v).1 : ℚ)^2 /
          (((side p u v).1 * ((side p u v).2 + 1) +
            if (side p u v).2 = 0 then b-a else b : Nat) : ℚ) +
        6 * ((side p u v).2 : ℚ)^2 /
          (((side p u v).2 * ((side p u v).1 + 1) +
            if (side p u v).1 = 0 then a-b else a : Nat) : ℚ) := by
    have da (x y : Expr) : (x.add y).denote ctx = x.denote ctx + y.denote ctx := rfl
    have dm (x y : Expr) : (x.mul y).denote ctx = x.denote ctx * y.denote ctx := rfl
    have dp (x : Expr) (n : Nat) : (x.pow n).denote ctx = x.denote ctx ^ n := rfl
    have dn (k : Int) : (Expr.num k).denote ctx = (k : ℚ) := denoteInt_eq k
    cases p with
    | thin t =>
      cases t with
      | zero => simp [charge, side]
      | succ t =>
        have he : t+1+b-a = t+1+(b-a) := by omega
        simp only [charge, sizes, Bool.false_eq_true, ↓reduceIte, side,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, dn]
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
          Nat.succ_ne_zero, zero_add, mul_zero, zero_pow (by decide : 2 ≠ 0),
          zero_div, add_zero, zero_mul, zero_add, Nat.cast_zero, zero_add]
        constructor
        · push_cast
          have habQ : (a : ℚ) ≤ b := by exact_mod_cast hab
          linarith [Nat.cast_nonneg (α := ℚ) t]
        · push_cast
          rw [Nat.cast_sub hab]
          ring
    | full r =>
      have hp1 : 0 < (side (.full r) u v).1 := by cases r <;> simp [side] <;> omega
      have hp2 : 0 < (side (.full r) u v).2 := by cases r <;> simp [side] <;> omega
      have hx : (side (.full r) u v).1 ≠ 0 := by omega
      have hy : (side (.full r) u v).2 ≠ 0 := by omega
      simp only [charge, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
        or_false, forall_eq_or_imp, forall_eq, dm, da, dp, dn, hsx, hsy,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hx, hy]
      push_cast
      constructor
      · constructor <;> positivity
      · rfl

  have assembled_sound (b : Int) (terms : List (Expr × Expr)) (ctx : Lean.RArray ℚ)
      (hp : ∀ t ∈ terms, 0 < t.2.denote ctx)
      (h : 0 ≤ (assembled b terms).denote ctx) :
      0 ≤ (b : ℚ) + (terms.map fun t => t.1.denote ctx / t.2.denote ctx).sum := by
    have product (l : List Expr) :
        (l.foldr Expr.mul (.num 1)).denote ctx = (l.map fun e => e.denote ctx).prod := by
      induction l with
      | nil => rfl
      | cons e l ih => simpa [Expr.denote] using congrArg (e.denote ctx * ·) ih
    have summation (l : List Expr) (init : Expr) :
        (l.foldl Expr.add init).denote ctx = init.denote ctx + (l.map fun e => e.denote ctx).sum := by
      induction l generalizing init with
      | nil => simp
      | cons e l ih =>
        change (l.foldl Expr.add (init.add e)).denote ctx = _
        rw [ih]
        change (init.denote ctx + e.denote ctx) + _ = _
        simp only [List.map_cons, List.sum_cons, add_assoc]
    let ds := terms.map fun t => t.2.denote ctx
    have hds : ∀ d ∈ ds, 0 < d := by
      intro d hd
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hd
      exact hp t ht
    have hd : 0 < ds.prod := List.prod_pos hds
    have one (i : Nat) (hi : i < terms.length) :
        (terms[i]!).1.denote ctx * (((terms.map Prod.snd).take i ++
          (terms.map Prod.snd).drop (i+1)).map (fun e => e.denote ctx)).prod =
        ds.prod * ((terms[i]!).1.denote ctx / (terms[i]!).2.denote ctx) := by
      simp only [List.map_append, List.map_take, List.map_drop, List.map_map]
      change (terms[i]!).1.denote ctx * (ds.take i ++ ds.drop (i+1)).prod = _
      rw [← List.eraseIdx_eq_take_drop_succ]
      have hi' : i < ds.length := by simpa [ds] using hi
      have he := List.CommMonoid.mul_prod_eraseIdx (l := ds) hi'
      have hz : ds[i] ≠ 0 := ne_of_gt (hds _ (List.getElem_mem hi'))
      have hv : (terms[i]!).2.denote ctx = ds[i] := by simp [ds, List.getElem?_eq_getElem hi]
      rw [hv, ← he]
      field_simp
    have enum : ((List.range terms.length).map fun i =>
        (terms[i]!).1.denote ctx / (terms[i]!).2.denote ctx) =
        terms.map fun t => t.1.denote ctx / t.2.denote ctx := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp only [List.length_map, List.length_range] at hi
        simp [List.getElem?_eq_getElem hi]
    have he : (assembled b terms).denote ctx =
        ds.prod * ((b : ℚ) + (terms.map fun t => t.1.denote ctx / t.2.denote ctx).sum) := by
      unfold assembled
      rw [summation]
      have dm (a c : Expr) : (a.mul c).denote ctx = a.denote ctx * c.denote ctx := rfl
      have dn (k : Int) : (Expr.num k).denote ctx = (k : ℚ) := denoteInt_eq k
      simp only [List.map_map, Function.comp_def, dm, dn, product]
      change (b : ℚ) * ds.prod + _ = _
      have hr : ((List.range terms.length).map fun i =>
          (terms[i]!).1.denote ctx * (((terms.map Prod.snd).take i ++
            (terms.map Prod.snd).drop (i+1)).map fun e => e.denote ctx).prod) =
          (List.range terms.length).map fun i =>
            ds.prod * ((terms[i]!).1.denote ctx / (terms[i]!).2.denote ctx) := by
        apply List.map_congr_left
        intro i hi
        exact one i (List.mem_range.mp hi)
      rw [hr]
      rw [List.sum_map_mul_left, enum]
      ring
    rw [he] at h
    exact nonneg_of_mul_nonneg_right h hd

  have reflection_sound (e : Expr) (ctx : Lean.RArray ℚ)
      (hc : nonnegativeCoefficients e.toPoly_k = true)
      (hn : ∀ i, 0 ≤ ctx.get i) : 0 ≤ e.denote ctx := by
    have mon (m : Mon) : 0 ≤ m.denote ctx := by
      induction m with
      | unit => norm_num [Mon.denote]
      | mult p m ih =>
        rw [Mon.denote, Power.denote_eq]
        exact mul_nonneg (pow_nonneg (hn _) _) ih
    have poly (p : Poly) : nonnegativeCoefficients p = true → 0 ≤ p.denote ctx := by
      induction p with
      | num k =>
        intro h
        have hk : (0 : ℤ) ≤ k := of_decide_eq_true h
        change (0 : ℚ) ≤ (k : ℚ)
        exact_mod_cast hk
      | add k m p ih =>
        intro h
        obtain ⟨hk, hp⟩ := Bool.and_eq_true_iff.mp h
        have hk' : (0 : ℤ) ≤ k := of_decide_eq_true hk
        change 0 ≤ k • m.denote ctx + p.denote ctx
        exact add_nonneg (smul_nonneg hk' (mon m)) (ih hp)
    rw [Expr.toPoly_k_eq_toPoly] at hc
    rw [← Expr.denote_toPoly]
    exact poly _ hc

  have small_bound (m : Fin 3 → Nat) (x : Fin 3 → Fin 3 → Nat)
      (hdiag : ∀ i, x i i = 0)
      (hvalid : ∀ i j, i ≠ j → x i j = 0 → m j + x j i ≤ m i)
      (hm01 : m 0 ≤ m 1) (hm12 : m 1 ≤ m 2)
      (hsmall : ∑ i, m i ≤ 5)
      (hnfull : ¬ ∀ i j, i ≠ j → 1 ≤ x i j)
      (checked : ∀ t ≤ 5, checkTotal t = true) :
      (23/12 : ℚ) ≤ quadraticLower m x := by
    obtain ⟨p,hp,u,v,ep⟩ := choice_exists (m 0) (m 1) (x 0 1) (x 1 0) hm01
      (hvalid 0 1 (by decide)) (hvalid 1 0 (by decide))
    obtain ⟨q,hq,w,z,eq⟩ := choice_exists (m 0) (m 2) (x 0 2) (x 2 0) (hm01.trans hm12)
      (hvalid 0 2 (by decide)) (hvalid 2 0 (by decide))
    obtain ⟨r,hr,s,t,er⟩ := choice_exists (m 1) (m 2) (x 1 2) (x 2 1) hm12
      (hvalid 1 2 (by decide)) (hvalid 2 1 (by decide))
    have nf : (isFull p && isFull q && isFull r) = false := by
      by_contra hn
      have hf : (isFull p && isFull q && isFull r) = true := Bool.eq_true_of_not_eq_false hn
      obtain ⟨⟨hp',hq'⟩,hr'⟩ := Bool.and_eq_true_iff.mp hf |>.imp_left Bool.and_eq_true_iff.mp
      have positive (k : Choice) (a b : Nat) (hk : isFull k = true) :
          1 ≤ (side k a b).1 ∧ 1 ≤ (side k a b).2 := by
        cases k with
        | thin n => simp [isFull] at hk
        | full rev => cases rev <;> simp [side] <;> omega
      have pp := positive p u v hp'
      have pq := positive q w z hq'
      have pr := positive r s t hr'
      rw [ep] at pp
      rw [eq] at pq
      rw [er] at pr
      apply hnfull
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | simpa using pp.1 | simpa using pp.2 | simpa using pq.1 | simpa using pq.2 | simpa using pr.1 | simpa using pr.2
    let ctx := context u v w z s t
    have sp : (sizes 0 p).1.denote ctx = (x 0 1 : ℚ) ∧
        (sizes 0 p).2.denote ctx = (x 1 0 : ℚ) := by
      have h := size_zero p u v w z s t
      simpa only [ep] using h
    have sq : (sizes 1 q).1.denote ctx = (x 0 2 : ℚ) ∧
        (sizes 1 q).2.denote ctx = (x 2 0 : ℚ) := by
      have h : (sizes 1 q).1.denote ctx = ((side q w z).1 : ℚ) ∧
          (sizes 1 q).2.denote ctx = ((side q w z).2 : ℚ) := by
        cases q with
        | thin n => simp [sizes, side, Expr.denote, denoteInt_eq]
        | full rev => cases rev <;> simp [sizes, side, Expr.denote, Var.denote, ctx, context, Lean.RArray.get, Nat.ble, denoteInt_eq]
      simpa only [eq] using h
    have sr : (sizes 2 r).1.denote ctx = (x 1 2 : ℚ) ∧
        (sizes 2 r).2.denote ctx = (x 2 1 : ℚ) := by
      have h : (sizes 2 r).1.denote ctx = ((side r s t).1 : ℚ) ∧
          (sizes 2 r).2.denote ctx = ((side r s t).2 : ℚ) := by
        cases r with
        | thin n => simp [sizes, side, Expr.denote, denoteInt_eq]
        | full rev => cases rev <;> simp [sizes, side, Expr.denote, Var.denote, ctx, context, Lean.RArray.get, Nat.ble, denoteInt_eq]
      simpa only [er] using h
    have cp := charge_value (m 0) (m 1) 0 u v hm01 p ctx
      (by simpa only [ep] using sp.1) (by simpa only [ep] using sp.2)
    have cq := charge_value (m 0) (m 2) 1 w z (hm01.trans hm12) q ctx
      (by simpa only [eq] using sq.1) (by simpa only [eq] using sq.2)
    have cr := charge_value (m 1) (m 2) 2 s t hm12 r ctx
      (by simpa only [er] using sr.1) (by simpa only [er] using sr.2)
    simp only [ep] at cp
    simp only [eq] at cq
    simp only [er] at cr
    have hM : m 0 + m 1 + m 2 ≤ 5 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hsmall
    have check : nonnegativeCoefficients (numerator (m 0) (m 1) (m 2) p q r).toPoly_k = true := by
      have hall := checked (m 0 + m 1 + m 2) hM
      simp only [checkTotal, List.all_eq_true] at hall
      have h := hall (m 0) (by simp only [List.mem_range]; omega)
        (m 1) (by simp only [List.mem_range]; omega)
        (m 2) (by simp only [List.mem_range]; omega)
      simp only [hm01, hm12, and_self, ↓reduceIte] at h
      simp only [checkMixed, List.all_eq_true] at h
      simpa only [nf, Bool.false_eq_true, ↓reduceIte] using h p hp q hq r hr
    have hn := reflection_sound _ ctx check (context_nonneg u v w z s t)
    let terms : List (Expr × Expr) :=
      [(.num 12, .add (.num (m 0+1)) (.add (sizes 0 p).1 (sizes 1 q).1)),
       (.num 12, .add (.num (m 1+1)) (.add (sizes 0 p).2 (sizes 2 r).1)),
       (.num 12, .add (.num (m 2+1)) (.add (sizes 1 q).2 (sizes 2 r).2))] ++
        charge (m 0) (m 1) 0 false p ++ charge (m 0) (m 2) 1 false q ++
        charge (m 1) (m 2) 2 false r
    have he : numerator (m 0) (m 1) (m 2) p q r =
        assembled (2*(m 0+m 1+m 2 : Int)-23) terms := by
      simp only [numerator, nf, terms, assembled]
    rw [he] at hn
    have da (a b : Expr) : (a.add b).denote ctx = a.denote ctx + b.denote ctx := rfl
    have dn (k : Int) : (Expr.num k).denote ctx = (k : ℚ) := denoteInt_eq k
    have ht : ∀ v ∈ terms, 0 < v.2.denote ctx := by
      intro v hv
      simp only [terms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        or_assoc] at hv
      rcases hv with rfl | rfl | rfl | hv | hv | hv
      · simp only [da, dn, sp.1, sq.1]; positivity
      · simp only [da, dn, sp.2, sr.1]; positivity
      · simp only [da, dn, sq.2, sr.2]; positivity
      · exact cp.1 v hv
      · exact cq.1 v hv
      · exact cr.1 v hv
    have hh := assembled_sound _ terms ctx ht hn
    have hpv := cp.2
    have hqv := cq.2
    have hrv := cr.2
    simp only [terms, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, da, dn, sp.1, sp.2, sq.1, sq.2, sr.1, sr.2,
      hpv, hqv, hrv] at hh
    push_cast at hh
    have diag_in (i : Fin 3) : incoming m x i i = 0 := by simp [incoming, hdiag]
    unfold quadraticLower
    norm_num [Fin.sum_univ_succ, hdiag, diag_in, incoming]
    push_cast
    ring_nf at hh ⊢
    linarith only [hh]

  have region_checked (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c)
      (hs : a+b+c ≤ 5) (p q r : Choice) (hp : p ∈ choices a b)
      (hq : q ∈ choices a c) (hr : r ∈ choices b c)
      (nf : (isFull p && isFull q && isFull r) = false) :
      nonnegativeCoefficients (numerator a b c p q r).toPoly_k = true := by
    have ha : a ≤ 5 := by omega
    have hb : b ≤ 5 := by omega
    have hc : c ≤ 5 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> try omega
    all_goals
      fin_cases hp <;> fin_cases hq <;> fin_cases hr <;>
        simp only [isFull, Bool.true_and, Bool.false_and, Bool.and_true,
          Bool.and_false, Bool.true_eq_false] at nf
    all_goals decide +kernel
  have checked (t : Nat) (ht : t ≤ 5) : checkTotal t = true := by
    simp only [checkTotal, List.all_eq_true]
    intro a ha b hb c hc
    split
    · rename_i h
      obtain ⟨hab,hbc,hs⟩ := h
      simp only [checkMixed, List.all_eq_true]
      intro p hp q hq r hr
      split
      · rfl
      · rename_i hf
        exact region_checked a b c hab hbc (by omega) p q r hp hq hr
          (Bool.eq_false_of_not_eq_true hf)
    · rfl
  have large (m : Fin 3 → ℕ) (x : Fin 3 → Fin 3 → ℕ)
      (hdiag : ∀ i, x i i = 0) (hM : 6 ≤ ∑ i, m i) :
      (23 / 12 : ℚ) ≤ quadraticLower m x := by
    let M : ℚ := ∑ i, (m i : ℚ)
    let N : ℚ := ∑ i, ∑ j, (x i j : ℚ)
    have hN : 0 ≤ N := sum_nonneg fun i hi => sum_nonneg fun j hj => Nat.cast_nonneg _
    have hm6 : 6 ≤ M := by dsimp [M]; exact_mod_cast hM
    have cls : 9 / (N + M + 3) ≤
        ∑ i : Fin 3, 1 / ((m i + ∑ j, x i j : ℕ) + 1 : ℚ) := by
      have hc := sq_sum_div_le_sum_sq_div (univ : Finset (Fin 3))
        (fun _ => (1 : ℚ))
        (g := fun i => ((m i + ∑ j, x i j : ℕ) : ℚ) + 1)
        (fun i hi => by positivity)
      simpa [show (3 : ℚ)^2 = 9 by norm_num, M, N, sum_add_distrib, add_comm, add_left_comm, add_assoc] using hc
    have prod_bound : (∑ i : Fin 3, ∑ j : Fin 3, (x i j : ℚ) * (x j i : ℚ)) ≤ N^2/2 := by
      let a : ℚ := x 0 1
      let b : ℚ := x 1 0
      let c : ℚ := x 0 2
      let d : ℚ := x 2 0
      let e : ℚ := x 1 2
      let f : ℚ := x 2 1
      have hp : 0 ≤ a*d+a*f+c*b+c*f+e*b+e*d := by
        dsimp [a,b,c,d,e,f]; positivity
      have hs := sq_nonneg ((a+c+e)-(b+d+f))
      dsimp [N]
      norm_num [Fin.sum_univ_succ, hdiag]
      dsimp [a,b,c,d,e,f] at hp hs
      nlinarith only [hp, hs]
    have inc_bound : (∑ i : Fin 3, ∑ j : Fin 3, (incoming m x i j : ℚ)) ≤ 2*M := by
      have hi (i j : Fin 3) : (incoming m x i j : ℚ) ≤ if i = j then 0 else (m j : ℚ) := by
        by_cases hij : i = j
        · subst j; simp [incoming, hdiag]
        · simp only [hij, if_false]
          exact_mod_cast (show incoming m x i j ≤ m j by
            unfold incoming; split <;> omega)
      have hs := sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin 3))) =>
        sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin 3))) => hi i j
      have he : (∑ i : Fin 3, ∑ j : Fin 3, if i = j then (0 : ℚ) else (m j : ℚ)) = 2*M := by
        simp [M, Fin.sum_univ_succ]
        ring
      exact hs.trans_eq he
    let q := fun p : Fin 3 × Fin 3 =>
      ((x p.1 p.2 * (x p.2 p.1 + 1) + incoming m x p.1 p.2 : ℕ) : ℚ)
    let f := fun p : Fin 3 × Fin 3 => (x p.1 p.2 : ℚ)
    let A := (univ : Finset (Fin 3 × Fin 3)).filter fun p => x p.1 p.2 ≠ 0
    have hq (p : Fin 3 × Fin 3) : f p ≤ q p := by
      dsimp [f,q]
      exact_mod_cast (show x p.1 p.2 ≤ x p.1 p.2 * (x p.2 p.1 + 1) + incoming m x p.1 p.2 by
        nlinarith [Nat.zero_le (incoming m x p.1 p.2)])
    have hsumf : (∑ p ∈ A, f p) = N := by
      rw [show N = ∑ p : Fin 3 × Fin 3, f p by simp [N, f, Fintype.sum_prod_type]]
      apply sum_subset (filter_subset _ _)
      intro p hp hn
      simp only [A, mem_filter, mem_univ, true_and, not_not] at hn
      simp [f, hn]
    have hsumq : (∑ p ∈ A, q p) ≤ N^2/2 + N + 2*M := by
      have hsub : (∑ p ∈ A, q p) ≤ ∑ p : Fin 3 × Fin 3, q p :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p hp hn => by dsimp [q]; positivity)
      apply hsub.trans
      have he : (∑ p : Fin 3 × Fin 3, q p) =
          (∑ i : Fin 3, ∑ j : Fin 3, (x i j : ℚ)*(x j i : ℚ)) + N +
            ∑ i : Fin 3, ∑ j : Fin 3, (incoming m x i j : ℚ) := by
        simp [q, N, Fintype.sum_prod_type, mul_add, sum_add_distrib]
      rw [he]
      linarith
    have hrec : N^2/(N^2+2*N+4*M) ≤
        (1/2 : ℚ) * ∑ i : Fin 3, ∑ j : Fin 3,
          (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ) := by
      have he : (∑ p ∈ A, (f p)^2 / q p) =
          ∑ i : Fin 3, ∑ j : Fin 3,
            (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ) := by
        rw [show (∑ i : Fin 3, ∑ j : Fin 3,
            (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ)) =
            ∑ p : Fin 3 × Fin 3, (f p)^2/q p by simp [f,q,Fintype.sum_prod_type]]
        apply sum_subset (filter_subset _ _)
        intro p hp hn
        simp only [A, mem_filter, mem_univ, true_and, not_not] at hn
        simp [f, hn]
      rw [← he]
      by_cases hz : N = 0
      · simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
        apply mul_nonneg (by norm_num)
        exact sum_nonneg fun p hp => div_nonneg (sq_nonneg _) (by dsimp [q]; positivity)
      have hp : 0 < ∑ p ∈ A, q p := by
        have hsum := sum_le_sum (s := A) fun p hp => hq p
        rw [hsumf] at hsum
        exact lt_of_lt_of_le (lt_of_le_of_ne hN (Ne.symm hz)) hsum
      have hc := sq_sum_div_le_sum_sq_div A f (g := q) (fun p hp => by
        have hx : (0 : ℚ) < f p := by
          dsimp [f]
          exact_mod_cast Nat.pos_of_ne_zero (mem_filter.mp hp).2
        exact lt_of_lt_of_le hx (hq p))
      rw [hsumf] at hc
      have hb : 2 * (∑ p ∈ A, q p) ≤ N^2+2*N+4*M := by linarith
      have hdiv := div_le_div_of_nonneg_left (sq_nonneg N) (show 0 < 2*(∑ p ∈ A,q p) by positivity) hb
      have hh : N^2 / (2*(∑ p ∈ A,q p)) = (1/2 : ℚ)*(N^2/(∑ p ∈ A,q p)) := by ring
      rw [hh] at hdiv
      exact hdiv.trans (mul_le_mul_of_nonneg_left hc (by norm_num))
    have numeric : (23/12 : ℚ) ≤ M/6 + 9/(N+M+3) + N^2/(N^2+2*N+4*M) := by
      let t := M-6
      have ht : 0 ≤ t := sub_nonneg.mpr hm6
      have hden1 : 0 < N+M+3 := by linarith
      have hden2 : 0 < N^2+2*N+4*M := by nlinarith [sq_nonneg N]
      apply (le_of_mul_le_mul_left (a := 12*(N+M+3)*(N^2+2*N+4*M)) ?_ (by positivity))
      have hp : 0 ≤ N^3+(95*N-123)^2/95+5391/95+
          t*(2*N^3+23*N^2+18*N+204)+t^2*(2*N^2+12*N+76)+8*t^3 := by positivity
      dsimp [t] at hp
      field_simp
      nlinarith only [hp]
    unfold quadraticLower
    change 23/12 ≤ _ + M/6 + _
    linarith
  have three (m : Fin 3 → ℕ) (x : Fin 3 → Fin 3 → ℕ)
      (hdiag : ∀ i, x i i = 0) (hM : ∑ i, m i ≤ 5)
      (hpos : ∀ i j, i ≠ j → 1 ≤ x i j) :
      (23/12 : ℚ) ≤ chargedLower m x := by
    have color_loss (a b k : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hk : k ≤ 5) :
        -(1/4 : ℚ) - (k : ℚ)/36 ≤
          1/((k+a+b : ℕ)+1 : ℚ) - 1/(2*((a : ℚ)+1)) - 1/(2*((b : ℚ)+1)) := by
      obtain ⟨u, rfl⟩ : ∃ u, a = u+1 := ⟨a-1, by omega⟩
      obtain ⟨v, rfl⟩ : ∃ v, b = v+1 := ⟨b-1, by omega⟩
      interval_cases k <;> push_cast <;> apply le_of_sub_nonneg <;>
        field_simp <;> ring_nf <;> positivity
    have pair_bound (a b : ℕ) :
        (2 : ℚ) - 1/((a : ℚ)+1) - 1/((b : ℚ)+1) ≤
          (a : ℚ)/((b : ℚ)+1) + (b : ℚ)/((a : ℚ)+1) := by
      apply (le_of_mul_le_mul_left (a := ((a : ℚ)+1)*((b : ℚ)+1)) ?_ (by positivity))
      field_simp
      nlinarith [sq_nonneg ((a : ℚ)-(b : ℚ))]
    have loss (i j : Fin 3) (hij : i ≠ j) :
        (m j : ℚ)/(((x j i : ℚ)+1)*((x j i : ℚ)+2)) ≤ (m j : ℚ)/6 := by
      have hp : (1 : ℚ) ≤ x j i := by exact_mod_cast hpos j i hij.symm
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num)
      nlinarith
    have small (i : Fin 3) : m i ≤ 5 :=
      (single_le_sum (fun j hj => Nat.zero_le (m j)) (mem_univ i)).trans hM
    have c0 := color_loss (x 0 1) (x 0 2) (m 0)
      (hpos 0 1 (by decide)) (hpos 0 2 (by decide)) (small 0)
    have c1 := color_loss (x 1 0) (x 1 2) (m 1)
      (hpos 1 0 (by decide)) (hpos 1 2 (by decide)) (small 1)
    have c2 := color_loss (x 2 0) (x 2 1) (m 2)
      (hpos 2 0 (by decide)) (hpos 2 1 (by decide)) (small 2)
    have p01 := pair_bound (x 0 1) (x 1 0)
    have p02 := pair_bound (x 0 2) (x 2 0)
    have p12 := pair_bound (x 1 2) (x 2 1)
    have l01 := loss 0 1 (by decide)
    have l02 := loss 0 2 (by decide)
    have l10 := loss 1 0 (by decide)
    have l12 := loss 1 2 (by decide)
    have l20 := loss 2 0 (by decide)
    have l21 := loss 2 1 (by decide)
    have hm : (m 0 : ℚ)+(m 1 : ℚ)+(m 2 : ℚ) ≤ 5 := by
      have h := hM
      norm_num [Fin.sum_univ_succ] at h
      exact_mod_cast (show m 0 + m 1 + m 2 ≤ 5 by omega)
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    norm_num [chargedLower, Fin.sum_univ_succ, hdiag, h02, h12, h21]
    push_cast at c0 c1 c2
    simp only [one_div, mul_inv_rev, add_assoc] at c0 c1 c2 ⊢
    simp only [one_div] at p01 p02 p12
    norm_num at c0 c1 c2 ⊢
    linarith
  have permutation (m : Fin 3 → Nat) (x : Fin 3 → Fin 3 → Nat) (e : Equiv.Perm (Fin 3)) :
      quadraticLower (fun i => m (e i)) (fun i j => x (e i) (e j)) = quadraticLower m x := by
    have inner (i : Fin 3) : (∑ j, x (e i) (e j)) = ∑ j, x (e i) j := Equiv.sum_comp e _
    have cls : (∑ i : Fin 3, 1 / ((m (e i) + ∑ j, x (e i) (e j) : Nat) + 1 : ℚ)) =
        ∑ i : Fin 3, 1 / ((m i + ∑ j, x i j : Nat) + 1 : ℚ) := by
      simp_rw [inner]
      exact Equiv.sum_comp e (fun i => 1 / ((m i + ∑ j, x i j : Nat) + 1 : ℚ))
    have mid : (∑ i : Fin 3, (m (e i) : ℚ)) = ∑ i, (m i : ℚ) := Equiv.sum_comp e (fun i => (m i : ℚ))
    have dbl (f : Fin 3 → Fin 3 → ℚ) : (∑ i, ∑ j, f (e i) (e j)) = ∑ i, ∑ j, f i j := by
      have row (i : Fin 3) : (∑ j, f (e i) (e j)) = ∑ j, f (e i) j := Equiv.sum_comp e _
      simp_rw [row]
      exact Equiv.sum_comp e (fun i => ∑ j, f i j)
    unfold quadraticLower
    rw [cls, mid]
    congr 2
    exact dbl fun i j => (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : Nat) : ℚ)
  by_cases hlarge : 6 ≤ ∑ i, m i
  · exact (large m x hdiag hlarge).trans (le_max_right _ _)
  have hsmall : ∑ i, m i ≤ 5 := by omega
  by_cases hfull : ∀ i j, i ≠ j → 1 ≤ x i j
  · exact (three m x hdiag hsmall hfull).trans (le_max_left _ _)
  let e := Tuple.sort m
  have ordered := Tuple.monotone_sort m
  have hd' : ∀ i, x (e i) (e i)=0 := fun i => hdiag (e i)
  have hv' : ∀ i j, i ≠ j → x (e i) (e j)=0 → m (e j)+x (e j) (e i) ≤ m (e i) := by
    intro i j hij hx
    exact hvalid (e i) (e j) (fun h => hij (e.injective h)) hx
  have hm' : ∑ i, m (e i) ≤ 5 := by
    rw [Equiv.sum_comp e m]
    exact hsmall
  have hn' : ¬ ∀ i j, i ≠ j → 1 ≤ x (e i) (e j) := by
    intro h
    apply hfull
    intro i j hij
    simpa only [e.apply_symm_apply] using h (e.symm i) (e.symm j)
      (fun he => hij (e.symm.injective he))
  have h := small_bound (fun i => m (e i)) (fun i j => x (e i) (e j)) hd' hv'
    (ordered (by decide : (0 : Fin 3) ≤ 1)) (ordered (by decide : (1 : Fin 3) ≤ 2))
    hm' hn' checked
  rw [permutation m x e] at h
  exact h.trans (le_max_right _ _)

set_option maxHeartbeats 1000000 in
/-- The unrestricted reciprocal bound for a properly three-colored graph whose mixed vertices have degree two. -/
theorem reciprocal_bound (s : Finset W) (adj : W → W → Prop)
    (color : W → Fin 3)
    (hsym : ∀ u ∈ s, ∀ v ∈ s, adj u v → adj v u)
    (hproper : ∀ u ∈ s, ∀ v ∈ s, adj u v → color u ≠ color v)
    (hm : ∀ v ∈ s, Mixed s adj color v → (neighborhood s adj v).card = 2)
    :
    (23/12 : ℚ) ≤ potential s adj color := by
  let t := s.filter fun v => (neighborhood s adj v).Nonempty
  have ts : t ⊆ s := filter_subset _ _
  have neighbors (v : W) (hv : v ∈ s) : neighborhood t adj v = neighborhood s adj v := by
    ext u
    change (u ∈ t.filter (adj v)) ↔ (u ∈ s.filter (adj v))
    simp only [mem_filter]
    constructor
    · rintro ⟨hu,hva⟩; exact ⟨ts hu,hva⟩
    · rintro ⟨hu,hva⟩
      exact ⟨mem_filter.mpr ⟨hu, ⟨v, mem_filter.mpr ⟨hv, hsym v hv u hu hva⟩⟩⟩, hva⟩
  have nt (v : W) (hv : v ∈ t) : (neighborhood t adj v).Nonempty := by
    rw [neighbors v (ts hv)]
    exact (mem_filter.mp hv).2
  have mt (v : W) (hv : v ∈ t) (h : Mixed t adj color v) : (neighborhood t adj v).card = 2 := by
    unfold Mixed at h
    rw [neighbors v (ts hv)] at h ⊢
    exact hm v (ts hv) h
  have red := population_reduction t adj color
    (fun u hu v hv => hsym u (ts hu) v (ts hv))
    (fun u hu v hv => hproper u (ts hu) v (ts hv)) mt nt
  have base := (population_bound _ _ red.1 red.2.1).trans red.2.2
  apply base.trans
  have isolated (v : W) (hv : v ∈ s \ t) : neighborhood s adj v = ∅ := by
    have hn : ¬(neighborhood s adj v).Nonempty := by
      intro hn
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1, hn⟩)
    exact not_nonempty_iff_eq_empty.mp hn
  have scalar (a r : Nat) :
      1 / ((a : ℚ)+1) ≤ 1 / ((a+r : Nat)+1 : ℚ) + (r : ℚ)/2 := by
    cases r with
    | zero => simp
    | succ r =>
      push_cast
      apply le_of_sub_nonneg
      field_simp
      ring_nf
      positivity
  have disj : Disjoint t (s \ t) := disjoint_left.mpr (fun v hv hz => (mem_sdiff.mp hz).2 hv)
  have count (i : Fin 3) : (s.filter fun v => color v=i).card =
      (t.filter fun v => color v=i).card + ((s \ t).filter fun v => color v=i).card := by
    have hs : s = t ∪ (s \ t) := (union_sdiff_of_subset ts).symm
    conv_lhs => rw [hs, filter_union]
    exact card_union_of_disjoint (disj.mono (filter_subset _ _) (filter_subset _ _))
  have cardz : ((s \ t).card : ℚ) = ∑ i : Fin 3, (((s \ t).filter fun v => color v=i).card : ℚ) := by
    exact_mod_cast (card_eq_sum_card_fiberwise (s := s \ t) (t := univ)
      (f := color) (fun v hv => mem_univ _))
  have classes :
      (∑ i : Fin 3, 1/(((t.filter fun v => color v=i).card : ℚ)+1)) ≤
      (∑ i : Fin 3, 1/(((s.filter fun v => color v=i).card : ℚ)+1)) + ((s \ t).card : ℚ)/2 := by
    rw [cardz, sum_div, ← sum_add_distrib]
    apply sum_le_sum
    intro i hi
    rw [count]
    exact scalar _ _
  have weights : (∑ v ∈ s, 1/((neighborhood s adj v).card+1 : ℚ)) =
      (∑ v ∈ t, 1/((neighborhood t adj v).card+1 : ℚ)) + ((s \ t).card : ℚ) := by
    have live : (∑ v ∈ t, 1/((neighborhood s adj v).card+1 : ℚ)) =
        ∑ v ∈ t, 1/((neighborhood t adj v).card+1 : ℚ) := by
      apply sum_congr rfl
      intro v hv
      rw [neighbors v (ts hv)]
    have dead : (∑ v ∈ s \ t, 1/((neighborhood s adj v).card+1 : ℚ)) = ((s \ t).card : ℚ) := by
      simp only [sum_congr rfl (fun v hv => congrArg (fun a : Nat => 1/(a+1 : ℚ))
        (congrArg Finset.card (isolated v hv))), card_empty]
      simp
    calc
      _ = (∑ v ∈ t, 1/((neighborhood s adj v).card+1 : ℚ)) +
          ∑ v ∈ s \ t, 1/((neighborhood s adj v).card+1 : ℚ) := by
        rw [← sum_union disj, union_sdiff_of_subset ts]
      _ = _ := by rw [live, dead]
  unfold potential
  rw [weights]
  linarith

end D5.S3.Combinatorics.Graph.ThreeColorReciprocal
