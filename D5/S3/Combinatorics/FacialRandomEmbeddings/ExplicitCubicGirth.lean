/- GID: D5/S3/Combinatorics/FacialRandomEmbeddings/ExplicitCubicGirth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FacialRandomEmbeddings/ExplicitCubicGirth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: An explicit finite residue-ring orbit yields bridgeless bipartite cubic graphs of arbitrary prescribed girth with named matching neighbors. -/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A residue-ring construction of cubic graphs of prescribed girth

The three moves have the explicit matrices `[[c, 1-c²], [1, -c]]` for
`c = -2, 0, 2`. A separated-cone estimate for reduced words over the integers
survives reduction modulo `5^g + 1`. Applying the moves on their tagged
permutation orbit gives a connected bipartite cubic graph with no bridge.
Its elements are determined by two columns (the determinant forces the tag),
so the construction uses at most `(5^g + 1)^4` vertices.

See N. Biggs, *Constructions for Cubic Graphs with Large Girth* (1998), doi:10.37236/1386, for
the general Cayley construction method and sharper bounds. This file
certifies the particular residue-ring family and matching presentation;
it does not assert optimality or a new general existence result.
-/

namespace D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth

namespace ColorData
abbrev Color := Fin 3

private def alternate (i : Color) : Color := if i = 0 then 1 else 0

private theorem alternate_ne (i : Color) : alternate i ≠ i := by
  by_cases h : i = 0
  · subst i
    decide
  · simpa [alternate, h] using Ne.symm h

private structure MatchingColoring {V : Type*} (G : SimpleGraph V) where
  next : Color → V → V
  adj : ∀ i x, G.Adj x (next i x)
  invol : ∀ i x, next i (next i x) = x
  unique : ∀ x, Function.Injective (fun i => next i x)
  covers : ∀ {x y}, G.Adj x y → ∃ i, next i x = y

private def Reduced {V : Type*} {G : SimpleGraph V} :
    ∀ {x y : V}, G.Walk x y → Prop
  | _, _, .nil => True
  | x, _, .cons _ q => q.getVert 1 ≠ x ∧ Reduced q

end ColorData

section
namespace IntegralMoves

private def center (c : Fin 3) : ℤ := 2 * (c.val : ℤ) - 2

private def act {R : Type*} [Ring R] (c : Fin 3) (z : R × R) : R × R :=
  ((center c : R) * z.1 + (1 - (center c : R)^2) * z.2,
    z.1 - (center c : R) * z.2)

private def wordEval {R : Type*} [Ring R] (w : List (Fin 3)) : R × R :=
  w.foldl (fun z c => act c z) (1, 0)

private theorem act_coord (c : Fin 3) (z : ℤ × ℤ) :
    (act c z).1 - center c * (act c z).2 = z.2 := by
  simp only [act, Int.cast_id]
  ring

private theorem act_involutive (R : Type*) [CommRing R] (c : Fin 3) :
    Function.Involutive (act (R := R) c) := by
  intro z
  apply Prod.ext <;> simp only [act] <;> ring

private theorem color_separation {c d : Fin 3} (h : c ≠ d) :
    2 ≤ |center d - center c| := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have hc : (c.val : ℤ) < d.val := by exact_mod_cast hlt
    rw [abs_of_nonneg (by unfold center; omega)]
    unfold center
    omega
  · have hc : (d.val : ℤ) < c.val := by exact_mod_cast hlt
    rw [abs_of_nonpos (by unfold center; omega)]
    unfold center
    omega

private theorem move_cone {c d : Fin 3} {z : ℤ × ℤ} (hcd : c ≠ d)
    (hz : |z.1 - center d * z.2| < |z.2|) :
    |(act c z).1 - center c * (act c z).2| < |(act c z).2| := by
  rw [act_coord]
  have ht := abs_add_le (z.1 - center c * z.2) (-(z.1 - center d * z.2))
  rw [abs_neg] at ht
  have he : z.1 - center c * z.2 + -(z.1 - center d * z.2) =
      (center d - center c) * z.2 := by ring
  rw [he, abs_mul] at ht
  have hh := mul_le_mul_of_nonneg_right (color_separation hcd) (abs_nonneg z.2)
  simp only [act, Int.cast_id]
  linarith

private theorem start_cone (c : Fin 3) :
    |(act c (1, 0) : ℤ × ℤ).1 - center c * (act c (1, 0) : ℤ × ℤ).2| <
      |(act c (1, 0) : ℤ × ℤ).2| := by
  rw [act_coord]
  norm_num [act]

private theorem cone_foldr (c : Fin 3) (w : List (Fin 3))
    (hr : (c :: w).IsChain (· ≠ ·)) :
    let z := (c :: w).foldr (act (R := ℤ)) (1, 0)
    |z.1 - center c * z.2| < |z.2| := by
  induction w generalizing c with
  | nil => exact start_cone c
  | cons d w ih =>
    rw [List.isChain_cons_cons] at hr
    exact move_cone hr.1 (ih d hr.2)

private theorem abs_center (c : Fin 3) : |center c| ≤ 2 := by
  have hc := c.isLt
  apply abs_le.mpr
  unfold center
  omega

private theorem abs_center_sq (c : Fin 3) : |1 - center c ^ 2| ≤ 3 := by
  have hc : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  rcases hc with h | h | h <;> norm_num [center, h]

private theorem act_bound (c : Fin 3) (z : ℤ × ℤ) (B : ℤ)
    (hx : |z.1| ≤ B) (hy : |z.2| ≤ B) :
    |(act c z).1| ≤ 5 * B ∧ |(act c z).2| ≤ 5 * B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) hx
  constructor
  · simp only [act, Int.cast_id]
    calc
      _ ≤ |center c * z.1| + |(1 - center c ^ 2) * z.2| := abs_add_le _ _
      _ ≤ 2 * B + 3 * B := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (abs_center c) hx (abs_nonneg _) zero_le_two)
          (mul_le_mul (abs_center_sq c) hy (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  · simp only [act, Int.cast_id, sub_eq_add_neg]
    calc
      _ ≤ |z.1| + |-(center c * z.2)| := abs_add_le _ _
      _ ≤ B + 2 * B := by
        rw [abs_neg, abs_mul]
        exact add_le_add hx (mul_le_mul (abs_center c) hy (abs_nonneg _) zero_le_two)
      _ ≤ _ := by linarith

private theorem bound_foldr (w : List (Fin 3)) :
    let z := w.foldr (act (R := ℤ)) (1, 0)
    |z.1| ≤ 5 ^ w.length ∧ |z.2| ≤ 5 ^ w.length := by
  induction w with
  | nil => norm_num
  | cons c w ih =>
    have hb := act_bound c _ _ ih.1 ih.2
    simpa [List.foldr_cons, pow_succ, mul_comm] using hb

private theorem wordEval_int_bound (w : List (Fin 3)) (hne : w ≠ [])
    (hr : w.IsChain (· ≠ ·)) :
    0 < |(wordEval (R := ℤ) w).2| ∧ |(wordEval (R := ℤ) w).2| ≤ 5 ^ w.length := by
  have hr' : w.reverse.IsChain (· ≠ ·) := List.isChain_reverse.mpr (by
    simpa only [ne_comm] using hr)
  have hne' := mt List.reverse_eq_nil_iff.mp hne
  have he : w.reverse.foldr (act (R := ℤ)) (1, 0) = wordEval w := List.foldr_reverse
  constructor
  · rw [← he]
    generalize hwr : w.reverse = w' at hr' hne' ⊢
    cases w' with
    | nil => exact (hne' rfl).elim
    | cons c l => exact lt_of_le_of_lt (abs_nonneg _) (cone_foldr c l hr')
  · rw [← he, ← List.length_reverse (as := w)]
    exact (bound_foldr w.reverse).2

private def pairCast (R : Type*) [Ring R] (z : ℤ × ℤ) : R × R := (z.1, z.2)

private theorem act_pairCast (R : Type*) [Ring R] (c : Fin 3) (z : ℤ × ℤ) :
    pairCast R (act c z) = act c (pairCast R z) := by
  apply Prod.ext <;> simp [pairCast, act]

private theorem foldr_pairCast (R : Type*) [Ring R] (w : List (Fin 3)) :
    pairCast R (w.foldr (act (R := ℤ)) (1, 0)) = w.foldr (act (R := R)) (1, 0) := by
  induction w with
  | nil => simp [pairCast]
  | cons c w ih => simp only [List.foldr_cons, act_pairCast, ih]

private theorem wordEval_zmod_snd (m : ℕ) (w : List (Fin 3)) :
    (wordEval (R := ZMod m) w).2 = ((wordEval (R := ℤ) w).2 : ZMod m) := by
  simpa only [wordEval, List.foldr_reverse, pairCast] using
    (congrArg Prod.snd (foldr_pairCast (ZMod m) w.reverse)).symm

private theorem wordEval_mod_nonzero (g : ℕ) (w : List (Fin 3)) (hne : w ≠ [])
    (hr : w.IsChain (· ≠ ·)) (hlen : w.length ≤ g) :
    (wordEval (R := ZMod (5^g+1)) w).2 ≠ 0 := by
  rw [wordEval_zmod_snd, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
  let v := (wordEval (R := ℤ) w).2
  have hv := wordEval_int_bound w hne hr
  have ha : (v.natAbs : ℤ) = |v| := Int.natCast_natAbs v
  have hpos : 0 < v.natAbs := by
    exact_mod_cast (ha ▸ hv.1)
  have hle : v.natAbs ≤ 5^w.length := by
    have h : (v.natAbs : ℤ) ≤ (5 : ℤ)^w.length := ha ▸ hv.2
    exact_mod_cast h
  intro hd
  have hg := calc
    5^g + 1 ≤ v.natAbs := Nat.le_of_dvd hpos hd
    _ ≤ 5^w.length := hle
    _ ≤ 5^g := pow_le_pow_right' (by norm_num) hlen
  omega

end IntegralMoves
end

section
namespace ColorData
open SimpleGraph
open ColorData
namespace MatchingColoring
variable {V : Type} {G : SimpleGraph V}

private noncomputable def colorPair (C : MatchingColoring G) (x y : V) : Color := by
  classical
  exact if h : G.Adj x y then (C.covers h).choose else 0

private theorem follows_colorPair (C : MatchingColoring G) {x y : V} (h : G.Adj x y) :
    C.next (C.colorPair x y) x = y := by
  classical
  unfold colorPair
  rw [dite_eq_left h]
  exact (C.covers h).choose_spec

private noncomputable def graphWord (C : MatchingColoring G) :
    ∀ {x y : V}, G.Walk x y → List Color
  | _,_,.nil => []
  | x,_,.cons (v:=z) _ p => C.colorPair x z :: C.graphWord p

private theorem graphWord_length (C : MatchingColoring G) {x y : V} (p : G.Walk x y) :
    (C.graphWord p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [graphWord,List.length_cons,Walk.length_cons,ih]

private theorem graphWord_end (C : MatchingColoring G) {x y : V} (p : G.Walk x y) :
    (C.graphWord p).foldl (fun z i => C.next i z) x = y := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [graphWord,List.foldl_cons,C.follows_colorPair h,ih]

private theorem graphWord_chain (C : MatchingColoring G) {x y : V} (p : G.Walk x y)
    (hp : Reduced p) : (C.graphWord p).IsChain (· ≠ ·) := by
  induction p with
  | nil => exact List.IsChain.nil
  | @cons x z y h p ih =>
    have hp' : p.getVert 1 ≠ x ∧ Reduced p := hp
    have ht := ih hp'.2
    cases p with
    | nil => exact List.IsChain.singleton _
    | @cons z t y j q =>
      rw [graphWord,graphWord,List.isChain_cons_cons]
      refine ⟨?_,ht⟩
      intro hs
      have hxt := C.follows_colorPair j
      have hzx := C.follows_colorPair h
      have hback := C.invol (C.colorPair x z) x
      rw [hzx,hs,hxt] at hback
      have pget : (Walk.cons j q).getVert (0+1) = t := by
        rw [Walk.getVert_cons_succ,Walk.getVert_zero]
      exact hp'.1 (pget.trans hback)

private theorem trail_reduced {x y : V} {p : G.Walk x y} (hp : p.IsTrail) : Reduced p := by
  induction p with
  | nil => exact trivial
  | @cons x z y h p ih =>
    have a := (Walk.isTrail_cons h p).mp hp
    have hred := ih a.1
    refine ⟨?_,hred⟩
    cases p with
    | nil => exact h.ne.symm
    | @cons z t y j q =>
      intro heq
      have pget : (Walk.cons j q).getVert (0+1) = t := by
        rw [Walk.getVert_cons_succ,Walk.getVert_zero]
      have ht := pget.symm.trans heq
      apply a.2
      rw [← ht,Sym2.eq_swap]
      exact List.Mem.head _

private theorem egirth_of_reduced_word_separation (C : MatchingColoring G) (g : ℕ)
    (hsep : ∀ (x : V) (cs : List Color), cs ≠ [] → cs.IsChain (· ≠ ·) →
      cs.length ≤ g → cs.foldl (fun z i => C.next i z) x ≠ x) :
    (g:ℕ∞) < G.egirth := by
  have hz : ((g+1 : ℕ):ℕ∞) ≤ G.egirth := by
    apply SimpleGraph.le_egirth.mpr
    intro x p hp
    apply ENat.natCast_le_natCast.mpr
    by_contra! hs
    have hlen : (C.graphWord p).length ≤ g := by
      rw [C.graphWord_length]
      omega
    have hnel : C.graphWord p ≠ [] := by
      intro h
      have hz := C.graphWord_length p
      rw [h,List.length_nil] at hz
      exact hp.not_nil (Walk.length_eq_zero_iff.mp hz.symm)
    exact hsep x (C.graphWord p) hnel (C.graphWord_chain p (trail_reduced hp.isTrail)) hlen
      (C.graphWord_end p)
  exact (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self g)).trans_le hz

end MatchingColoring
end ColorData
end

section
namespace ColorData
open SimpleGraph
open ColorData
namespace MatchingColoring
variable {V : Type} {G : SimpleGraph V}

private theorem colorPair_next (C : MatchingColoring G) (x : V) (i : Color) :
    C.colorPair x (C.next i x) = i := by
  classical
  unfold colorPair
  rw [dite_eq_left (C.adj i x)]
  exact C.unique x (C.covers (C.adj i x)).choose_spec

private theorem colorPair_symm (C : MatchingColoring G) (x y : V) :
    C.colorPair x y = C.colorPair y x := by
  classical
  by_cases h : G.Adj x y
  · obtain ⟨i,hi⟩ := C.covers h
    subst y
    rw [colorPair_next]
    simpa only [C.invol i x] using (C.colorPair_next (C.next i x) i).symm
  · have hn : ¬G.Adj y x := fun hy => h hy.symm
    simp [colorPair, h, hn]

private noncomputable def colorEdge (C : MatchingColoring G) : Sym2 V → Color :=
  Sym2.lift ⟨C.colorPair,C.colorPair_symm⟩

private theorem colorEdge_next (C : MatchingColoring G) (x : V) (i : Color) :
    C.colorEdge s(x,C.next i x) = i := C.colorPair_next x i

private def matchingPerm (C : MatchingColoring G) (i : Color) : Equiv.Perm V :=
  ⟨C.next i,C.next i,C.invol i,C.invol i⟩

private def permPair (C : MatchingColoring G) (i j : Color) : Equiv.Perm V :=
  C.matchingPerm j * C.matchingPerm i

private theorem permPair_apply (C : MatchingColoring G) (i j : Color) (x : V) :
    C.permPair i j x = C.next j (C.next i x) := rfl

private theorem permPair_pow_succ (C : MatchingColoring G) (i j : Color) (n : ℕ) (x : V) :
    (C.permPair i j ^ (n+1)) x =
      (C.permPair i j ^ n) (C.next j (C.next i x)) := by
  rw [pow_succ, Equiv.Perm.mul_apply,permPair_apply]

private def alternating (C : MatchingColoring G) (i j : Color) :
    (n : ℕ) → (x : V) → G.Walk x ((C.permPair i j ^ n) x)
  | 0,_ => .nil
  | n+1,x =>
    .cons (C.adj i x) (.cons (C.adj j (C.next i x))
      ((C.alternating i j n (C.next j (C.next i x))).copy rfl
        (C.permPair_pow_succ i j n x).symm))

private theorem alternating_edge (C : MatchingColoring G) (i j : Color)
    (n : ℕ) (x : V) (e : Sym2 V) (h : e ∈ (C.alternating i j n x).edges) :
    ∃ k : ℕ, k < n ∧
      (e = s((C.permPair i j ^ k) x,C.next i ((C.permPair i j ^ k) x)) ∨
       e = s(C.next i ((C.permPair i j ^ k) x),C.next j (C.next i ((C.permPair i j ^ k) x)))) := by
  induction n generalizing x with
  | zero => change e ∈ ([] : List (Sym2 V)) at h; exact (List.not_mem_nil h).elim
  | succ n ih =>
    change e ∈ s(x,C.next i x)::s(C.next i x,C.next j (C.next i x))::
      ((C.alternating i j n (C.next j (C.next i x))).copy rfl
        (C.permPair_pow_succ i j n x).symm).edges at h
    rw [Walk.edges_copy,List.mem_cons,List.mem_cons] at h
    rcases h with ha|hb|hc
    · exact ⟨0, Nat.zero_lt_succ _, Or.inl (by simpa using ha)⟩
    · exact ⟨0, Nat.zero_lt_succ _, Or.inr (by simpa using hb)⟩
    · obtain ⟨k,hk,h⟩ := ih _ hc
      exact ⟨k+1, Nat.succ_lt_succ hk, by simpa only [permPair_pow_succ] using h⟩

private theorem pair_parity (C : MatchingColoring G) (side : V → Bool)
    (hside : ∀ i x, side (C.next i x) = ! side x)
    (i j : Color) (k : ℕ) (x : V) : side ((C.permPair i j ^ k) x) = side x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [permPair_pow_succ,ih,hside,hside]
    simp

private theorem edge_not_bridge_of_two_matchings (C : MatchingColoring G) [Finite V]
    (side : V → Bool) (hside : ∀ i x, side (C.next i x) = ! side x)
    (i j : Color) (hji : j ≠ i) (x : V) :
    ¬G.IsBridge s(x,C.next i x) := by
  classical
  let σ := C.permPair i j
  have hex : ∃ n : ℕ, 0<n ∧ (σ^n) x = x := by
    exact ⟨orderOf σ,orderOf_pos σ,by rw [pow_orderOf_eq_one]; rfl⟩
  let m := Nat.find hex
  have hm : 0<m ∧ (σ^m) x=x := Nat.find_spec hex
  let y := C.next i x
  let p := C.alternating i j (m-1) (C.next j y)
  have hmend : (σ^(m-1)) (C.next j y)=x := by
    have hs : m-1+1=m := by omega
    have hq := C.permPair_pow_succ i j (m-1) x
    rw [hs] at hq
    exact hq.symm.trans hm.2
  let w : G.Walk y x := .cons (C.adj j y) (p.copy rfl hmend)
  have hje (a : V) : s(a,C.next j a) ≠ s(x,y) := by
    intro he
    have ah := C.colorEdge_next a j
    have hx := C.colorEdge_next x i
    rw [he] at ah
    exact hji (ah.symm.trans hx)
  have havoid : s(x,y) ∉ w.edges := by
    intro hw
    change s(x,y) ∈ s(y,C.next j y)::(p.copy rfl hmend).edges at hw
    rw [Walk.edges_copy,List.mem_cons] at hw
    rcases hw with h | hp
    · exact hje y h.symm
    obtain ⟨k,hk,hkedge⟩ := C.alternating_edge i j (m-1) (C.next j y) _ hp
    rcases hkedge with h | h
    · let z := (σ^k) (C.next j y)
      have hs : side z=side x := by
        rw [C.pair_parity side hside i j k (C.next j y),hside,hside]
        simp
      rcases Sym2.eq_iff.mp h with ⟨h₁,_⟩ | ⟨_,h₂⟩
      · have hloop : (σ^(k+1)) x=x := by rw [C.permPair_pow_succ]; exact h₁.symm
        have hmin : m ≤ k+1 := Nat.find_min' hex ⟨Nat.zero_lt_succ _,hloop⟩
        omega
      · have hs' : side y=side x := by rw [h₂]; exact hs
        have hn : (!side x) ≠ side x := by cases side x <;> decide
        exact hn ((hside i x).symm.trans hs')
    · exact hje _ h.symm
  intro hb
  have hmem := SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hb w.reverse
  rw [Walk.edges_reverse,List.mem_reverse] at hmem
  exact havoid hmem

private theorem no_bridge (C : MatchingColoring G) [Finite V] (side : V → Bool)
    (hside : ∀ i x, side (C.next i x) = ! side x) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ¬G.IsBridge e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨i,hi⟩ := C.covers he
    change C.next i x = y at hi
    subst y
    exact C.edge_not_bridge_of_two_matchings side hside i (alternate i) (alternate_ne i) x

end MatchingColoring
end ColorData
end

section
set_option maxHeartbeats 700000

namespace OrbitModel
open ColorData

private abbrev Tagged (α : Type*) := Equiv.Perm α × Equiv.Perm Bool

private def tagSwap : Equiv.Perm Bool := Equiv.swap false true

private def generator {α : Type*} (s : Color → Equiv.Perm α) (i : Color) : Tagged α :=
  (s i, tagSwap)

private def word {α : Type*} (s : Color → Equiv.Perm α) (x : Tagged α) (cs : List Color) : Tagged α :=
  cs.foldl (fun z i => generator s i * z) x

private theorem word_right_translate {α : Type*} (s : Color → Equiv.Perm α)
    (x y : Tagged α) (cs : List Color) : word s (x*y) cs=word s x cs*y := by
  induction cs generalizing x with
  | nil => rfl
  | cons i cs ih =>
    change word s (generator s i*(x*y)) cs=word s (generator s i*x) cs*y
    rw [←mul_assoc,ih]

/-- The physical action and multiplication by the tagged permutations use
the same left-to-right order on words. -/
private theorem word_action {α : Type*} (s : Color → Equiv.Perm α)
    (x : Tagged α) (a : α) (cs : List Color) :
    (word s x cs).1 a = cs.foldl (fun z i => s i z) (x.1 a) := by
  induction cs generalizing x with
  | nil => rfl
  | cons i cs ih =>
    change (word s (generator s i*x) cs).1 a =
      cs.foldl (fun z i => s i z) (s i (x.1 a))
    rw [ih]
    rfl

private def Orbit {α : Type*} (s : Color → Equiv.Perm α) :=
  {x : Tagged α // ∃ cs : List Color, word s 1 cs=x}

noncomputable instance orbitFintype {α : Type*} [Fintype α] [DecidableEq α]
    (s : Color → Equiv.Perm α) : Fintype (Orbit s) := by
  classical
  letI : Finite (Orbit s) := Finite.of_injective (fun x : Orbit s => x.val) Subtype.val_injective
  exact Fintype.ofFinite _

private def origin {α : Type*} (s : Color → Equiv.Perm α) : Orbit s :=
  ⟨1, [], rfl⟩

instance orbitNonempty {α : Type*} (s : Color → Equiv.Perm α) : Nonempty (Orbit s) :=
  ⟨origin s⟩

private def next {α : Type*} (s : Color → Equiv.Perm α) (i : Color) (x : Orbit s) : Orbit s :=
  ⟨generator s i*x.val, by
    obtain ⟨cs,hcs⟩ := x.property
    refine ⟨cs++[i],?_⟩
    unfold word at *
    rw [List.foldl_append,hcs]
    rfl⟩

@[simp] private theorem next_val {α : Type*} (s : Color → Equiv.Perm α) (i : Color) (x : Orbit s) :
    (next s i x).val = generator s i*x.val := rfl

private theorem next_involutive {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) (i : Color) (x : Orbit s) : next s i (next s i x)=x := by
  apply Subtype.ext
  rw [next_val,next_val,←mul_assoc]
  have hg : generator s i*generator s i=1 := by
    change (s i*s i,tagSwap*tagSwap)=(1,1)
    rw [hs i,tagSwap,Equiv.swap_mul_self]
  rw [hg,one_mul]

private def parity {α : Type*} {s : Color → Equiv.Perm α} (x : Orbit s) : Bool := x.val.2 false

private theorem parity_flip {α : Type*} (s : Color → Equiv.Perm α) (i : Color)
    (x : Orbit s) : parity (next s i x)= !(parity x) := by
  change (tagSwap*x.val.2) false = !(x.val.2 false)
  rw [Equiv.Perm.mul_apply]
  cases x.val.2 false <;> decide

private theorem bool_ne_not (b : Bool) : b ≠ !b := by cases b <;> decide

/-- Simplicity follows already from the parity tag; distinctness of the
three kinds of neighbors is needed to give a proper cubic coloring. -/
private def graph {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) : SimpleGraph (Orbit s) where
  Adj x y := ∃ i, next s i x=y
  symm := ⟨by
    intro x y h
    obtain ⟨i,hi⟩ := h
    rw [←hi]
    exact ⟨i,next_involutive s hs i x⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨i,hi⟩ := h
    have hp := congrArg parity hi
    rw [parity_flip] at hp
    exact bool_ne_not (parity x) hp.symm⟩

private theorem adjacent_opposite_parity {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) {x y : Orbit s} (h : (graph s hs).Adj x y) :
    parity y= !(parity x) := by
  obtain ⟨i,rfl⟩ := h
  exact parity_flip s i x

private def bitColor (b : Bool) : Fin 2 := if b then 1 else 0

private theorem bitColor_ne_not (b : Bool) : bitColor b≠bitColor (!b) := by
  cases b <;> decide

private theorem isBipartite {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) : (graph s hs).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => bitColor (parity x)) ?_⟩
  intro x y hadj
  rw [adjacent_opposite_parity s hs hadj]
  exact bitColor_ne_not (parity x)


private theorem next_color_injective {α : Type*} (s : Color → Equiv.Perm α)
    (hinj : Function.Injective s) (x : Orbit s) : Function.Injective (fun i => next s i x) := by
  intro i j h
  have hv := congrArg Subtype.val h
  rw [next_val,next_val,mul_right_cancel_iff] at hv
  exact hinj (congrArg Prod.fst hv)

private def matchingColoring {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) (hinj : Function.Injective s) :
    MatchingColoring (graph s hs) where
  next := next s
  adj i _ := ⟨i,rfl⟩
  invol := next_involutive s hs
  unique := next_color_injective s hinj
  covers h := h

/-- The proper color matching really enumerates exactly three neighbors. -/
private theorem fold_next_val {α : Type*} (s : Color → Equiv.Perm α) (x : Orbit s)
    (cs : List Color) : (cs.foldl (fun z i => next s i z) x).val=word s x.val cs := by
  induction cs generalizing x with
  | nil => rfl
  | cons i cs ih =>
    change (cs.foldl _ (next s i x)).val=word s (generator s i*x.val) cs
    rw [ih,next_val]

private theorem walk_to_fold {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) (x : Orbit s) (cs : List Color) :
    (graph s hs).Reachable x (cs.foldl (fun z i => next s i z) x) := by
  induction cs generalizing x with
  | nil => exact ⟨.nil⟩
  | cons i cs ih =>
    have h : (graph s hs).Adj x (next s i x) := ⟨i,rfl⟩
    exact (show (graph s hs).Reachable x (next s i x) from ⟨.cons h .nil⟩).trans
      (ih (next s i x))

private theorem connected {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) : (graph s hs).Connected := by
  have hall (x : Orbit s) : (graph s hs).Reachable (origin s) x := by
    obtain ⟨cs,hcs⟩ := x.property
    have h : cs.foldl (fun z i => next s i z) (origin s)=x := by
      apply Subtype.ext
      rw [fold_next_val]
      exact hcs
    simpa only [h] using walk_to_fold s hs (origin s) cs
  exact ⟨fun x y => (hall x).symm.trans (hall y)⟩

/-- A short-word test only needs a single observation point. -/
private def NoShortMoves {α : Type*} (s : Color → Equiv.Perm α) (a : α) (g : ℕ) : Prop :=
  ∀ cs : List Color, cs≠[] → cs.IsChain (· ≠ ·) → cs.length≤g →
    cs.foldl (fun x i => s i x) a ≠ a

private theorem injective_of_no_short_moves {α : Type*} (s : Color → Equiv.Perm α)
    (hs : ∀ i, s i*s i=1) (a : α) {g : ℕ} (hg : 2≤g) (h : NoShortMoves s a g) :
    Function.Injective s := by
  intro i j hij
  by_contra hn
  have hc : [i,j].IsChain (· ≠ ·) := by
    rw [List.isChain_cons_cons]
    exact ⟨hn,List.isChain_singleton _⟩
  apply h [i,j] (List.cons_ne_nil _ _) hc hg
  have he := congrArg (fun p : Equiv.Perm α => p a) (hs i)
  change s j (s i a)=a
  rw [←hij]
  exact he

/-- A nontrivial evaluation at one point forbids return at every vertex
of the finite orbit, through right cancellation in the tagged group. -/
private theorem fold_no_short_return {α : Type*} (s : Color → Equiv.Perm α) (a : α) {g : ℕ}
    (h : NoShortMoves s a g) (x : Orbit s) (cs : List Color)
    (hne : cs≠[]) (hred : cs.IsChain (· ≠ ·)) (hlen : cs.length≤g) :
    cs.foldl (fun z i => next s i z) x≠x := by
  intro he
  have hv := congrArg Subtype.val he
  rw [fold_next_val,←one_mul x.val,word_right_translate,mul_right_cancel_iff] at hv
  have hp := word_action s 1 a cs
  rw [hv] at hp
  exact h cs hne hred hlen hp.symm

end OrbitModel
end

section
namespace Construction

open SimpleGraph ColorData

private abbrev Scalar (g : ℕ) := ZMod (5^g+1)
private abbrev Space (g : ℕ) := Scalar g × Scalar g

private def move (g : ℕ) (i : Color) : Equiv.Perm (Space g) where
  toFun := IntegralMoves.act i
  invFun := IntegralMoves.act i
  left_inv := IntegralMoves.act_involutive (Scalar g) i
  right_inv := IntegralMoves.act_involutive (Scalar g) i

private theorem move_square (g : ℕ) (i : Color) : move g i * move g i = 1 := by
  apply Equiv.ext
  intro z
  exact IntegralMoves.act_involutive (Scalar g) i z

private theorem no_short_moves (g : ℕ) : OrbitModel.NoShortMoves (move g) (1,0) g := by
  intro cs hn hc hl he
  exact IntegralMoves.wordEval_mod_nonzero g cs hn hc hl (congrArg Prod.snd he)

abbrev Vertices (g : ℕ) := OrbitModel.Orbit (move g)
def explicitGraph (g : ℕ) : SimpleGraph (Vertices g) := OrbitModel.graph (move g) (move_square g)

private def explicitMatching (g : ℕ) (hg : 2 ≤ g) : MatchingColoring (explicitGraph g) :=
  OrbitModel.matchingColoring (move g) (move_square g)
    (OrbitModel.injective_of_no_short_moves (move g) (move_square g) (1,0) hg
      (no_short_moves g))

private theorem explicitGraph_girth (g : ℕ) (hg : 2 ≤ g) : (g:ℕ∞) < (explicitGraph g).egirth := by
  apply (explicitMatching g hg).egirth_of_reduced_word_separation
  exact OrbitModel.fold_no_short_return (move g) (1,0) (no_short_moves g)

private theorem explicitGraph_connected (g : ℕ) : (explicitGraph g).Connected :=
  OrbitModel.connected (move g) (move_square g)

def side (g : ℕ) : Vertices g → Bool := OrbitModel.parity

private theorem explicitGraph_isBipartite (g : ℕ) : (explicitGraph g).IsBipartite :=
  OrbitModel.isBipartite (move g) (move_square g)

private theorem explicitGraph_no_bridge (g : ℕ) (hg : 2 ≤ g) (e : Sym2 (Vertices g))
    (he : e ∈ (explicitGraph g).edgeSet) : ¬(explicitGraph g).IsBridge e :=
  (explicitMatching g hg).no_bridge (side g) (OrbitModel.parity_flip (move g)) e he

private noncomputable def neighborsFromMatching {V : Type} {G : SimpleGraph V}
    (C : MatchingColoring G) (x : V) : Color ≃ G.neighborSet x :=
  Equiv.ofBijective (fun i => ⟨C.next i x,C.adj i x⟩)
    ⟨fun _ _ h => C.unique x (congrArg Subtype.val h),
      fun z => let ⟨i,hi⟩:=C.covers z.property; ⟨i,Subtype.ext hi⟩⟩

private theorem explicitGraph_cubic (g : ℕ) (hg : 2 ≤ g) (x : Vertices g) :
    Nat.card ((explicitGraph g).neighborSet x) = 3 := by
  rw [← Nat.card_congr (neighborsFromMatching (explicitMatching g hg) x),Nat.card_fin]

end Construction
end

section
namespace Construction
open OrbitModel ColorData

private def lin {R : Type*} [Ring R] (a b : R) (x y : R × R) : R × R :=
  (a*x.1+b*y.1,a*x.2+b*y.2)

private theorem act_lin {R : Type*} [CommRing R] (i : Color) (a b : R) (x y : R × R) :
    IntegralMoves.act i (lin a b x y) =
      lin a b (IntegralMoves.act i x) (IntegralMoves.act i y) := by
  apply Prod.ext <;> simp only [lin,IntegralMoves.act] <;> ring

private theorem apply_folds_lin {R : Type*} [CommRing R] (w : List Color) (a b : R) (x y : R × R) :
    w.foldl (fun z i => IntegralMoves.act i z) (lin a b x y) =
      lin a b (w.foldl (fun z i => IntegralMoves.act i z) x)
        (w.foldl (fun z i => IntegralMoves.act i z) y) := by
  induction w generalizing x y with
  | nil => rfl
  | cons i w ih =>
    simp only [List.foldl_cons,act_lin,ih]

private theorem orbit_linear (g : ℕ) (p : Vertices g) (a b : ZMod (5^g+1)) :
    p.val.1 (a,b) = lin a b (p.val.1 (1,0)) (p.val.1 (0,1)) := by
  obtain ⟨w,hw⟩ := p.property
  rw [←hw,word_action,word_action,word_action]
  have h := apply_folds_lin w a b (1,0) (0,1)
  have hzero : lin a b (1,0) (0,1) = (a,b) := by simp [lin]
  rw [hzero] at h
  exact h

private def witnessCols (g : ℕ) (p : Vertices g) :
    (ZMod (5^g+1) × ZMod (5^g+1)) × (ZMod (5^g+1) × ZMod (5^g+1)) :=
  (p.val.1 (1,0),p.val.1 (0,1))

private theorem perm_from_columns (g : ℕ) (p q : Vertices g)
    (h : witnessCols g p=witnessCols g q) : p.val.1=q.val.1 := by
  apply Equiv.ext
  intro ab
  obtain ⟨a,b⟩ := ab
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  change p.val.1 (1,0) = q.val.1 (1,0) at h₁
  change p.val.1 (0,1) = q.val.1 (0,1) at h₂
  rw [orbit_linear g p a b,orbit_linear g q a b,h₁,h₂]

private def detPair {R : Type*} [Ring R] (x y : R × R) : R :=
  x.1*y.2-x.2*y.1

private theorem det_pair_neg {R : Type*} [CommRing R] (i : Color) (x y : R × R) :
    detPair (IntegralMoves.act i x) (IntegralMoves.act i y) = -detPair x y := by
  simp only [detPair,IntegralMoves.act]
  ring

private theorem word_snoc (g : ℕ) (w : List Color) (i : Color) :
    word (move g) 1 (w++[i]) = generator (move g) i * word (move g) 1 w := by
  simp [word,List.foldl_append]

private theorem basis_det_word (g : ℕ) (w : List Color) :
    let p := word (move g) 1 w
    detPair (p.1 (1,0)) (p.1 (0,1)) = if p.2 false then -1 else 1 := by
  induction w using List.reverseRecOn with
  | nil => simp [word,detPair]
  | append_singleton w i ih =>
    simp only [word_snoc]
    let p := word (move g) 1 w
    change detPair (IntegralMoves.act i (p.1 (1,0))) (IntegralMoves.act i (p.1 (0,1))) =
      if (tagSwap * p.2) false then -1 else 1
    change detPair (p.1 (1,0)) (p.1 (0,1)) = _ at ih
    rw [det_pair_neg,ih,Equiv.Perm.mul_apply]
    cases h : p.2 false <;> simp [tagSwap]

private theorem orbit_det_tag (g : ℕ) (p : Vertices g) :
    detPair (p.val.1 (1,0)) (p.val.1 (0,1)) = if p.val.2 false then -1 else 1 := by
  obtain ⟨w,hw⟩ := p.property
  rw [←hw]
  exact basis_det_word g w

private theorem bit_perm_at_true (p : Equiv.Perm Bool) : p true = !p false := by
  have h : p true ≠ p false := fun he => (by decide : true ≠ false) (p.injective he)
  cases a : p true <;> cases b : p false <;> simp_all

private theorem exact_size_bound (g : ℕ) (hg : 1≤g) : Nat.card (Vertices g) ≤ (5^g+1)^4 := by
  have hneg : (-1:ZMod (5^g+1)) ≠ 1 := by
    intro h
    have hm : 5^g+1=1 ∨ 5^g+1=2 := ZMod.neg_one_eq_one_iff.mp h
    have hpow : 5^1 ≤ (5:ℕ)^g := Nat.pow_le_pow_right (by decide) hg
    norm_num at hpow
    omega
  have hi : Function.Injective (witnessCols g) := by
    intro p q h
    have hd := orbit_det_tag g p
    have he := orbit_det_tag g q
    have hd' := congrArg (fun col : (ZMod (5^g+1) × ZMod (5^g+1)) ×
        (ZMod (5^g+1) × ZMod (5^g+1)) => detPair col.1 col.2) h
    change detPair (p.val.1 (1,0)) (p.val.1 (0,1)) =
      detPair (q.val.1 (1,0)) (q.val.1 (0,1)) at hd'
    rw [hd,he] at hd'
    have hb : p.val.2 false = q.val.2 false := by
      cases hp : p.val.2 false <;> cases hq : q.val.2 false
      · rfl
      · exact (hneg (by simpa [hp,hq] using hd'.symm)).elim
      · exact (hneg (by simpa [hp,hq] using hd')).elim
      · rfl
    have he' : p.val.2=q.val.2 := by
      apply Equiv.ext
      intro b
      cases b with
      | false => exact hb
      | true => rw [bit_perm_at_true,bit_perm_at_true,hb]
    apply Subtype.ext
    exact Prod.ext (perm_from_columns g p q h) he'
  have h := Fintype.card_le_of_injective (witnessCols g) hi
  simpa [Nat.card_eq_fintype_card,Fintype.card_prod,ZMod.card,pow_succ,Nat.mul_assoc] using h

end Construction
end

open Construction

/-- The neighbor reached by the selected arithmetic generator. -/
def nextVertex (g : ℕ) (hg : 2 ≤ g) (i : Fin 3) (x : Vertices g) : Vertices g :=
  (explicitMatching g hg).next i x

/-- For every `g ≥ 2`, the specified modular graph is finite, connected,
bipartite, cubic and bridgeless, with girth strictly above `g`. The explicit
three matching involutions supply the colors, and the order is at most
`(5^g+1)^4`. -/
theorem result :
    let parity := fun a : (g : ℕ) × Vertices g => side a.1 a.2
    ∀ (g : ℕ) (hg : 2 ≤ g),
    Finite (Vertices g) ∧
    (explicitGraph g).Connected ∧
    (explicitGraph g).IsBipartite ∧
    (g : ℕ∞) < (explicitGraph g).egirth ∧
    Nat.card (Vertices g) ≤ (5^g+1)^4 ∧
    (∀ x, Nat.card ((explicitGraph g).neighborSet x) = 3) ∧
    (∀ e ∈ (explicitGraph g).edgeSet, ¬(explicitGraph g).IsBridge e) ∧
    (∀ i x, nextVertex g hg i (nextVertex g hg i x) = x) ∧
    (∀ x, Function.Injective (fun i => nextVertex g hg i x)) ∧
    (∀ i x, parity ⟨g, nextVertex g hg i x⟩ = !parity ⟨g, x⟩) ∧
    (∀ x y, (explicitGraph g).Adj x y ↔ ∃ i, nextVertex g hg i x = y) := by
  intro parity g hg
  exact ⟨inferInstance, explicitGraph_connected g, explicitGraph_isBipartite g,
    explicitGraph_girth g hg, exact_size_bound g (by omega), explicitGraph_cubic g hg,
    explicitGraph_no_bridge g hg, (explicitMatching g hg).invol,
    (explicitMatching g hg).unique, OrbitModel.parity_flip (move g),
    fun x y => ⟨(explicitMatching g hg).covers,
      fun ⟨i, hi⟩ => hi ▸ (explicitMatching g hg).adj i x⟩⟩

end D5.S3.Combinatorics.FacialRandomEmbeddings.ExplicitCubicGirth
