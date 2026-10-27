/- GID: D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/QuiverTreePhysicalE8
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.claim; result=D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.result; claim=D5/S3/Zeros/LeeYang/QuiverTreePhysicalE8.claim
   digest: The complete all-vertex physical eight-edge coefficient has an off-circle root. -/
/- Proof-shape and admission record for the candidate (CLAUDE 3.2).
   Proposed admission_basis: open-problem-resolution (#17677; Refuted).
   The original issue predates the probe and supplies the published prose anchor,
   complete all-vertex claim, tier and literature screen. Whether its external
   prose anchor meets the named-problem rule remains an independent review duty.
   No escape witness is claimed. Every theorem has proof_shape: bind-only.
   physical_factor: consumer physical_reduce.
   F_pos: consumer F_not_splits.
   F_not_splits: consumer nonreal.
   nonreal: consumer result.
   degrees: consumer rho_alloc.
   src_fiber: consumer mass_vec.
   tgt_fiber: consumer mass_vec.
   mass_vec: consumer allocation_factor.
   rho_alloc: consumer allocation_factor.
   tree_ok: consumer result.
   spin_sign: consumer spin_product.
   spin_product: consumer physical_reduce.
   sum_alloc: consumer physical_reduce.
   sum_cons: consumers sum_blocks, branch_sum.
   sum_blocks: consumer physical_reduce.
   allocation_factor: consumer physical_reduce.
   branch_sum: consumer physical_reduce.
   physical_reduce: consumer physical_roots.
   physical_roots: consumer result.
   reciprocal_lift: consumer lift_root.
   lift_root: consumer result.
   result: the designated literal refutation, exempt from escape registration.
   The physical all-vertex source is (2.15), (2.17), (2.19). Printed (2.31)
   has upper bound m, whereas (2.19) has m+1. No erratum, intended correction,
   full-tree-ensemble result or priority assertion is made here.
-/

import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
open Finset Polynomial
namespace D5.S3.Zeros.LeeYang.QuiverTreePhysicalE8
open QuiverTreeIsingRefutation
open D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport

def deg {V E : Type} [Fintype E] [DecidableEq V] (src tgt : E → V) (v : V) : ℕ :=
  (univ.filter (fun i => src i = v)).card + (univ.filter (fun i => tgt i = v)).card

noncomputable def fEnd (a : ℕ) : ℝ := (Nat.factorial (2*a) : ℝ) /
  ((Nat.factorial (a-1) : ℝ) * (Nat.factorial a : ℝ))

noncomputable def cVert (d a : ℕ) : ℝ := (Nat.factorial (d-1) : ℝ) / (Nat.factorial (d-a+2) : ℝ)

noncomputable def physRho {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (n k : E → ℕ) : ℝ :=
  (∏ i, (Nat.choose (2*n i) (2*k i) : ℝ)) *
  ∏ v, (cVert (mass src tgt n k v) (deg src tgt v) *
    (∏ i ∈ univ.filter (fun i => src i = v), fEnd (k i)) *
    (∏ i ∈ univ.filter (fun i => tgt i = v), fEnd (n i-k i)))

def claim : Prop := ∀ (V E : Type) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V),
  NamedSpanningTree src tgt Set.univ → 2 ≤ Fintype.card E →
  ∀ n : E → ℕ, (∀ i, 2 ≤ n i) → ∀ z : ℂ,
    ((treePoly src tgt n (physRho src tgt n) (-1)).map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1

private noncomputable def rhoFactored {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (n k : E → ℕ) : ℝ :=
  (∏ i, (Nat.choose (2*n i) (2*k i) : ℝ) * fEnd (k i) * fEnd (n i-k i)) *
  ∏ v, cVert (mass src tgt n k v) (deg src tgt v)

private theorem physical_factor {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (s t : E → V) (n k : E → ℕ) :
    physRho s t n k = rhoFactored s t n k := by
  classical
  simp only [physRho, rhoFactored, Finset.prod_mul_distrib,
    Finset.prod_fiberwise]
  ring

private noncomputable def p : ℝ[X] := 112*X^3-40*X^2-281*X+26
private noncomputable def q : ℝ[X] := 400*X^4+264*X^3-1543*X^2-788*X+686
private noncomputable def F : ℝ[X] :=
  X*q^2+4*(X+2)*(X-1)*p*q+C (9/2)*(X+2)*(X^2-2)*p^2

private theorem F_pos (y : ℝ) (hy : 16 / 9 ≤ y) : 0 < F.eval y := by
  have hy0 : 0 < y := by linarith
  have hd : 0 ≤ y-16 / 9 := sub_nonneg.mpr hy
  have hp : 0 < p.eval y := by
    have he : p.eval y = 112*(y-16 / 9)^3 + (1672/3)*(y-16 / 9)^2 +
        (17245/27)*(y-16 / 9) + 21370/729 := by
      simp [p]; ring
    rw [he]
    positivity
  have hh : 0 < y^3+6*y-16 := by
    have he : y^3+6*y-16 = (y-16 / 9)^3 + (16/3)*(y-16 / 9)^2 +
        (418/27)*(y-16 / 9) + 208/729 := by ring
    rw [he]
    positivity
  have he : F.eval y = y*(q.eval y+(2*y+2-4/y)*p.eval y)^2 +
      (1/2+1/y)*(y^3+6*y-16)*(p.eval y)^2 := by
    simp [F, p, q]
    field_simp [ne_of_gt hy0]
    ring
  rw [he]
  exact add_pos_of_nonneg_of_pos (mul_nonneg hy0.le (sq_nonneg _))
    (mul_pos (mul_pos (by positivity) hh) (sq_pos_of_pos hp))

private theorem F_not_splits : ¬ F.Splits := by
  intro hs
  have ht : 0 < F.eval (16 / 9) := F_pos _ le_rfl
  have hn : F.eval (16 / 9) ≠ 0 := ne_of_gt ht
  have hr : ∀ r ∈ F.roots, r < (16 / 9 : ℝ) := by
    intro r hr
    by_contra h
    have hz := Polynomial.isRoot_of_mem_roots hr
    exact (ne_of_gt (F_pos r (le_of_not_gt h))) hz
  have hlog := hs.eval_derivative_eq_eval_mul_sum hn
  have hsum : 0 ≤ (F.roots.map (fun r => 1 / ((16 / 9 : ℝ)-r))).sum := by
    apply Multiset.sum_nonneg
    intro a ha
    obtain ⟨r, hr', rfl⟩ := Multiset.mem_map.mp ha
    exact le_of_lt (one_div_pos.mpr (sub_pos.mpr (hr r hr')))
  have hd : F.derivative.eval (16 / 9) < 0 := by
    norm_num [F, p, q, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have : 0 ≤ F.derivative.eval (16 / 9) := by rw [hlog]; exact mul_nonneg ht.le hsum
  linarith

private theorem nonreal : ∃ w : ℂ, (F.map (algebraMap ℝ ℂ)).IsRoot w ∧ w.im ≠ 0 := by
  let f := F.map (algebraMap ℝ ℂ)
  by_contra h
  push Not at h
  have hrange : ∀ a ∈ f.roots, a ∈ (algebraMap ℝ ℂ).range := by
    intro a ha
    have him : a.im = 0 := h a (Polynomial.isRoot_of_mem_roots ha)
    refine ⟨a.re, ?_⟩
    apply Complex.ext <;> simp [him]
  exact F_not_splits (Polynomial.Splits.of_splits_map_of_injective
    Complex.ofReal_injective (IsAlgClosed.splits f) hrange)


private def src : Fin 8 → Fin 9 := ![0,0,1,1,1,2,2,2]
private def tgt : Fin 8 → Fin 9 := ![1,2,3,4,5,6,7,8]
private def totals : Fin 8 → ℕ := fun _ => 3
private def ds : Fin 9 → ℕ := ![2,4,4,1,1,1,1,1,1]
private def alloc (a : Fin 8 → Fin 2) : Fin 8 → ℕ := fun i => (a i).val+1
private noncomputable def S0 : ℝ[X] :=
  let a := (1+X)*C (1/3)
  (a+1)^2*(a+2)+X^4*(a+X)^2*(a+2*X)
private noncomputable def S1 : ℝ[X] :=
  let a := (1+X)*C (1/3)
  ((a+1)^2*(4*a+7)+X^5*(a+X)^2*(4*a+7*X))*C (1/3)
private noncomputable def R : ℝ[X] :=
  (1-X)^6*((1+X^2)*S1^2+C (4/3)*(1+X^3)*S0*S1+C (1/2)*(1+X^4)*S0^2)

private theorem degrees : ∀ v, deg src tgt v = ds v := by decide

private theorem src_fiber : ∀ v : Fin 9,
    univ.filter (fun i : Fin 8 => src i = v) =
      ![{0,1}, {2,3,4}, {5,6,7}, ∅, ∅, ∅, ∅, ∅, ∅] v := by decide

private theorem tgt_fiber : ∀ v : Fin 9,
    univ.filter (fun i : Fin 8 => tgt i = v) =
      ![∅, {0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}] v := by decide

private theorem mass_vec (k : Fin 8 → ℕ) : mass src tgt totals k =
    ![k 0 + k 1, k 2 + k 3 + k 4 + (3 - k 0),
      k 5 + k 6 + k 7 + (3 - k 1), 3 - k 2, 3 - k 3, 3 - k 4,
      3 - k 5, 3 - k 6, 3 - k 7] := by
  funext v
  simp only [mass, src_fiber, tgt_fiber]
  fin_cases v <;> simp [totals] <;> omega

private theorem rho_alloc (a : Fin 8 → Fin 2) :
    rhoFactored src tgt totals (alloc a) =
      (360 : ℝ)^8 * ∏ v, cVert (mass src tgt totals (alloc a) v) (ds v) := by
  have he (i : Fin 8) :
      (Nat.choose (2 * totals i) (2 * alloc a i) : ℝ) * fEnd (alloc a i) *
        fEnd (totals i - alloc a i) = 360 := by
    simp only [totals, alloc]
    generalize h : a i = b
    fin_cases b <;> norm_num [fEnd, Nat.choose]
  simp only [rhoFactored, he, degrees, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

private theorem tree_ok : NamedSpanningTree src tgt Set.univ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e _; fin_cases e <;> decide
  · intro i j h
    apply Subtype.ext
    have hh : ∀ i j : Fin 8, s(src i,tgt i) = s(src j,tgt j) → i = j := by decide
    exact hh i j h
  · let G := treeSupport src tgt Set.univ
    have hadj (i : Fin 8) : G.Adj (src i) (tgt i) := by
      apply (SimpleGraph.fromEdgeSet_adj _).mpr
      exact ⟨⟨⟨i, Set.mem_univ _⟩, rfl⟩, by fin_cases i <;> decide⟩
    have hr : ∀ v, G.Reachable 0 v := by
      intro v
      fin_cases v
      · exact SimpleGraph.Reachable.refl _
      · exact (hadj 0).reachable
      · exact (hadj 1).reachable
      · exact (hadj 0).reachable.trans (hadj 2).reachable
      · exact (hadj 0).reachable.trans (hadj 3).reachable
      · exact (hadj 0).reachable.trans (hadj 4).reachable
      · exact (hadj 1).reachable.trans (hadj 5).reachable
      · exact (hadj 1).reachable.trans (hadj 6).reachable
      · exact (hadj 1).reachable.trans (hadj 7).reachable
    have hc : G.Connected := ⟨fun u v => (hr u).symm.trans (hr v)⟩
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨hc, ?_⟩
    have hset : G.edgeSet = {s(0,1),s(0,2),s(1,3),s(1,4),s(1,5),
        s(2,6),s(2,7),s(2,8)} := by
      ext e
      simp only [G, treeSupport, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff]
      constructor
      · rintro ⟨⟨⟨i,hi⟩, rfl⟩, hn⟩
        fin_cases i <;> simp [src,tgt]
      · intro he
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
        rcases he with h|h|h|h|h|h|h|h <;> subst e
        · exact ⟨⟨⟨0, Set.mem_univ _⟩, rfl⟩, by decide⟩
        · exact ⟨⟨⟨1, Set.mem_univ _⟩, rfl⟩, by decide⟩
        · exact ⟨⟨⟨2, Set.mem_univ _⟩, rfl⟩, by decide⟩
        · exact ⟨⟨⟨3, Set.mem_univ _⟩, rfl⟩, by decide⟩
        · exact ⟨⟨⟨4, Set.mem_univ _⟩, rfl⟩, by decide⟩
        · exact ⟨⟨⟨5, Set.mem_univ _⟩, rfl⟩, by decide⟩
        · exact ⟨⟨⟨6, Set.mem_univ _⟩, rfl⟩, by decide⟩
        · exact ⟨⟨⟨7, Set.mem_univ _⟩, rfl⟩, by decide⟩
    rw [hset]
    rw [Nat.card_coe_set_eq]
    norm_num [Nat.card_eq_fintype_card, Set.ncard_insert_of_notMem, Sym2.eq_iff]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation checks the cut parity of all 512 spin assignments.
private theorem spin_sign : ∀ st : Fin 9 → Bool,
    (-1 : ℤ)^(univ.filter (fun i : Fin 8 => st (src i) ≠ st (tgt i))).card =
      ∏ v, if st v then (-1 : ℤ)^(ds v) else 1 := by decide

private theorem spin_product (k : Fin 8 → ℕ) :
    (∑ st : Fin 9 → Bool,
      C ((-1 : ℝ)^(univ.filter (fun i => st (src i) ≠ st (tgt i))).card) *
      X^(∑ v ∈ univ.filter (fun v => st v = true), mass src tgt totals k v)) =
    ∏ v, (1 + C ((-1 : ℝ)^(ds v)) * X^(mass src tgt totals k v)) := by
  classical
  have h (st : Fin 9 → Bool) :
      C ((-1 : ℝ)^(univ.filter (fun i => st (src i) ≠ st (tgt i))).card) *
        X^(∑ v ∈ univ.filter (fun v => st v = true), mass src tgt totals k v) =
      ∏ v, (if st v then C ((-1 : ℝ)^(ds v)) * X^(mass src tgt totals k v) else 1) := by
    have hs : (-1 : ℝ)^(univ.filter (fun i => st (src i) ≠ st (tgt i))).card =
        ∏ v, if st v then (-1 : ℝ)^(ds v) else 1 := by
      exact_mod_cast spin_sign st
    rw [hs]
    simp only [Finset.sum_filter]
    simp_rw [show ∀ v, (if st v then C ((-1 : ℝ)^(ds v)) *
        X^(mass src tgt totals k v) else 1) =
        C (if st v then (-1 : ℝ)^(ds v) else 1) *
        X^(if st v then mass src tgt totals k v else 0) by
          intro v; cases st v <;> simp]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun v (b : Bool) =>
    if b then C ((-1 : ℝ)^(ds v)) * X^(mass src tgt totals k v) else 1)]
  apply Finset.prod_congr rfl
  intro v _
  simp [add_comm]

private theorem sum_alloc (f : (Fin 8 → ℕ) → ℝ[X]) :
    (∑ k ∈ splits totals, f k) = ∑ a : Fin 8 → Fin 2, f (alloc a) := by
  classical
  symm
  apply Finset.sum_bij (fun a _ => alloc a)
  · intro a _
    simp only [splits, Fintype.mem_piFinset, Finset.mem_Icc, totals]
    intro i
    have := (a i).isLt
    simp only [alloc]
    omega
  · intro a _ b _ h
    funext i
    apply Fin.ext
    have hi := congrFun h i
    simp only [alloc] at hi
    omega
  · intro k hk
    have hki : ∀ i, 1 ≤ k i ∧ k i ≤ 2 := by
      simpa only [splits, totals, Fintype.mem_piFinset, Finset.mem_Icc] using hk
    refine ⟨fun i => ⟨k i-1, by have := hki i; omega⟩, mem_univ _, ?_⟩
    funext i
    have := hki i
    simp only [alloc]
    omega
  · intro a _; rfl

private theorem sum_cons {M : Type} [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n + 1) → Fin 2) → M) :
    (∑ a, f a) = ∑ b : Fin 2, ∑ a : Fin n → Fin 2, f (Fin.cons b a) := by
  calc
    (∑ a, f a) = ∑ p : Fin 2 × (Fin n → Fin 2), f (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).symm
      intro a
      simp
    _ = _ := by rw [Fintype.sum_prod_type]


set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
private noncomputable def center (a b : Fin 2) (x : ℝ) : ℝ :=
  cVert (a.val+b.val+2) 2 * (1+x^(a.val+b.val+2))

private noncomputable def branch (a : Fin 2) (l : Fin 3 → Fin 2) (x : ℝ) : ℝ :=
  let m := (l 0).val+(l 1).val+(l 2).val+(5-a.val)
  cVert m 4 * (1+x^m) *
    ∏ j, (cVert (2-(l j).val) 1 * (1-x^(2-(l j).val)))

private theorem sum_blocks (f : (Fin 8 → Fin 2) → ℝ) :
    (∑ a, f a) = ∑ a : Fin 2, ∑ b : Fin 2,
      ∑ l : Fin 3 → Fin 2, ∑ r : Fin 3 → Fin 2,
        f (Fin.cons a (Fin.cons b (Fin.append l r))) := by
  rw [sum_cons]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_cons]
  apply Finset.sum_congr rfl
  intro b _
  calc
    (∑ c : Fin 6 → Fin 2, f (Fin.cons a (Fin.cons b c))) =
        ∑ p : (Fin 3 → Fin 2) × (Fin 3 → Fin 2),
          f (Fin.cons a (Fin.cons b (Fin.append p.1 p.2))) := by
      apply Fintype.sum_equiv (Fin.appendEquiv 3 3).symm
      intro c
      exact congrArg (fun z => f (Fin.cons a (Fin.cons b z)))
        ((Fin.appendEquiv 3 3).apply_symm_apply c).symm
    _ = _ := by rw [Fintype.sum_prod_type]

private theorem allocation_factor (a b : Fin 2) (l r : Fin 3 → Fin 2) (x : ℝ) :
    rhoFactored src tgt totals (alloc (Fin.cons a (Fin.cons b (Fin.append l r)))) *
      (∏ v, (1 + (-1 : ℝ)^(ds v) *
        x^(mass src tgt totals (alloc (Fin.cons a (Fin.cons b (Fin.append l r)))) v))) =
    (360 : ℝ)^8*center a b x*branch a l x*branch b r x := by
  have hf : Fin.cons a (Fin.cons b (Fin.append l r)) =
      ![a,b,l 0,l 1,l 2,r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  have hm : mass src tgt totals (alloc (Fin.cons a (Fin.cons b (Fin.append l r)))) =
      ![a.val+b.val+2,
        (l 0).val+(l 1).val+(l 2).val+(5-a.val),
        (r 0).val+(r 1).val+(r 2).val+(5-b.val),
        2-(l 0).val, 2-(l 1).val, 2-(l 2).val,
        2-(r 0).val, 2-(r 1).val, 2-(r 2).val] := by
    rw [hf, mass_vec]
    funext v
    have ha := a.isLt
    have hb := b.isLt
    fin_cases v <;> simp [alloc] <;> omega
  rw [rho_alloc]
  simp only [hm]
  norm_num [center, branch, ds, Fin.prod_univ_succ]
  ring

private theorem branch_sum (a : Fin 2) (x : ℝ) :
    (∑ l : Fin 3 → Fin 2, branch a l x) =
      (3/8 : ℝ)*(1-x)^3*(if a = 0 then S1.eval x else S0.eval x) := by
  have hc {n : ℕ} (b : Fin 2) (l : Fin n → Fin 2) :
      Fin.cons b l = Matrix.vecCons b l := rfl
  fin_cases a <;>
    simp only [sum_cons, Fin.sum_univ_two, hc] <;>
    norm_num [branch, cVert, Fin.prod_univ_succ, S0, S1] <;> ring

-- All 256 allocations are retained by the 2 × 2 × 8 × 8 sum equivalence.
-- Distributivity contracts the two independent pendant sums before normalization.
private theorem physical_reduce :
    treePoly src tgt totals (physRho src tgt totals) (-1) =
    C ((360 : ℝ)^8*36/512)*R := by
  classical
  unfold treePoly
  simp_rw [spin_product, physical_factor]
  rw [sum_alloc]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [sum_blocks]
  simp_rw [allocation_factor]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [branch_sum]
  norm_num [center, cVert, Fin.sum_univ_two, R, S0, S1]
  ring

private theorem physical_roots (z : ℂ) :
    ((treePoly src tgt totals (physRho src tgt totals) (-1)).map
      (algebraMap ℝ ℂ)).IsRoot z ↔ (R.map (algebraMap ℝ ℂ)).IsRoot z := by
  rw [physical_reduce]
  norm_num [Polynomial.IsRoot, Polynomial.map_mul, Polynomial.eval_mul]

private theorem reciprocal_lift (z : ℂ) (hz : z ≠ 0) :
    (R.map (algebraMap ℝ ℂ)).eval z =
    (1-z)^6*z^9*(F.map (algebraMap ℝ ℂ)).eval (z+z⁻¹)/6561 := by
  simp [R,S0,S1,F,p,q]
  field_simp [hz]
  ring

private theorem lift_root (w : ℂ) (hw : (F.map (algebraMap ℝ ℂ)).IsRoot w)
    (hi : w.im ≠ 0) : ∃ z : ℂ,
      (R.map (algebraMap ℝ ℂ)).IsRoot z ∧
      (R.map (algebraMap ℝ ℂ)).IsRoot z⁻¹ ∧ 0 < ‖z‖ ∧ ‖z‖ < 1 ∧ 1 < ‖z⁻¹‖ := by
  let r : ℂ[X] := X^2-C w*X+1
  have hd : r.degree ≠ 0 := by
    intro h
    have hc := Polynomial.coeff_eq_zero_of_degree_lt (p := r) (n := 2)
      (by rw [h]; norm_num)
    norm_num [r, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_one] at hc
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root r hd
  have he : z^2-w*z+1=0 := by simpa [r, Polynomial.IsRoot] using hz
  have hz0 : z ≠ 0 := by intro h; subst z; norm_num at he
  have hy : w = z+z⁻¹ := by
    field_simp [hz0]
    linear_combination -he
  have hr : (R.map (algebraMap ℝ ℂ)).IsRoot z := by
    change (R.map (algebraMap ℝ ℂ)).eval z = 0
    rw [reciprocal_lift z hz0, ← hy, hw]
    ring
  have hir : (R.map (algebraMap ℝ ℂ)).IsRoot z⁻¹ := by
    change (R.map (algebraMap ℝ ℂ)).eval z⁻¹ = 0
    rw [reciprocal_lift z⁻¹ (inv_ne_zero hz0), inv_inv, add_comm z⁻¹ z, ← hy, hw]
    ring
  have hu : ‖z‖ ≠ 1 := by
    intro hu
    have hconj := Complex.inv_eq_conj hu
    exact hi (by rw [hy]; simp [hconj])
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rcases lt_or_gt_of_ne hu with hlt | hgt
  · exact ⟨z, hr, hir, hp, hlt, by simpa using (one_lt_inv₀ hp).mpr hlt⟩
  · refine ⟨z⁻¹, hir, by simpa using hr, norm_pos_iff.mpr (inv_ne_zero hz0), ?_, ?_⟩
    · simpa using (inv_lt_one₀ hp).mpr hgt
    · simpa using hgt

theorem result : ¬ claim := by
  intro h
  obtain ⟨w,hw,hi⟩ := nonreal
  obtain ⟨z,hz,_,_,hlt,_⟩ := lift_root w hw hi
  apply ne_of_lt hlt
  apply h (Fin 9) (Fin 8) src tgt tree_ok (by decide) totals (by intro i; norm_num [totals]) z
  exact (physical_roots z).mpr hz

end D5.S3.Zeros.LeeYang.QuiverTreePhysicalE8
