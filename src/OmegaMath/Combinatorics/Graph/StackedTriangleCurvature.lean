import OmegaBuild.Commands
import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

compile_only_with_mathlib

/-! Omega original.

Linear functionals on bounded curvatures of successively stacked tetrahedra
attain their maxima at sign curvatures.
-/

namespace StackedTriangleCurvature

open Finset

/-- The root face and the three faces created by each insertion. -/
abbrev Face : ℕ → Type
  | 0 => Unit
  | n + 1 => Face n ⊕ Fin 3

instance (n : ℕ) : Fintype (Face n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Face n ⊕ Fin 3))

/-- Each insertion is attached to a triangle of the previous graph. -/
inductive Build : ℕ → Type
  | root : Build 0
  | attach {n} : Build n → Face n → Build (n + 1)

/-- Orient the three new faces so their sum has boundary equal to the parent face. -/
def Build.Valid : {n : ℕ} → Build n → (Face n → ℝ) → Prop
  | _, .root, x => |x ()| ≤ 1
  | _, .attach b p, x => b.Valid (x ∘ Sum.inl) ∧
      (∀ j : Fin 3, |x (Sum.inr j)| ≤ 1) ∧ ∑ j : Fin 3, x (Sum.inr j) = x (Sum.inl p)

theorem Build.abs_le_one {n : ℕ} {b : Build n} {x : Face n → ℝ} (hx : b.Valid x) :
    ∀ i, |x i| ≤ 1 := by
  induction b with
  | root => rintro ⟨⟩; exact hx
  | attach b p ih =>
    rintro (i | j)
    · exact ih hx.1 i
    · exact hx.2.1 j

private theorem ordered_coordinates (w : Fin 3 → ℝ) :
    ∃ σ : Equiv.Perm (Fin 3), w (σ 0) ≤ w (σ 1) ∧ w (σ 1) ≤ w (σ 2) := by
  let σ₁ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let σ₂ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let σ₃ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  have hs₁ : σ₁ 0 = 1 ∧ σ₁ 1 = 0 ∧ σ₁ 2 = 2 := by decide
  have hs₂ : σ₂ 0 = 0 ∧ σ₂ 1 = 2 ∧ σ₂ 2 = 1 := by decide
  have hs₃ : σ₃ 0 = 2 ∧ σ₃ 1 = 1 ∧ σ₃ 2 = 0 := by decide
  rcases le_total (w 0) (w 1) with h₀₁ | h₁₀
  · rcases le_total (w 1) (w 2) with h₁₂ | h₂₁
    · exact ⟨Equiv.refl _, h₀₁, h₁₂⟩
    · rcases le_total (w 0) (w 2) with h₀₂ | h₂₀
      · refine ⟨σ₂, ?_, ?_⟩ <;> simpa only [hs₂.1, hs₂.2.1, hs₂.2.2]
      · refine ⟨σ₃.trans σ₁, ?_, ?_⟩
        · simpa only [Equiv.trans_apply, hs₁.1, hs₁.2.1, hs₁.2.2,
            hs₃.1, hs₃.2.1, hs₃.2.2] using h₂₀
        · simpa only [Equiv.trans_apply, hs₁.1, hs₁.2.1, hs₁.2.2,
            hs₃.1, hs₃.2.1, hs₃.2.2] using h₀₁
  · rcases le_total (w 0) (w 2) with h₀₂ | h₂₀
    · refine ⟨σ₁, ?_, ?_⟩ <;> simpa only [hs₁.1, hs₁.2.1, hs₁.2.2]
    · rcases le_total (w 1) (w 2) with h₁₂ | h₂₁
      · refine ⟨σ₂.trans σ₁, ?_, ?_⟩
        · simpa only [Equiv.trans_apply, hs₂.1, hs₂.2.1, hs₂.2.2,
            hs₁.1, hs₁.2.1, hs₁.2.2] using h₁₂
        · simpa only [Equiv.trans_apply, hs₂.1, hs₂.2.1, hs₂.2.2,
            hs₁.1, hs₁.2.1, hs₁.2.2] using h₂₀
      · refine ⟨σ₃, ?_, ?_⟩
        · simpa only [hs₃.1, hs₃.2.1, hs₃.2.2] using h₂₁
        · simpa only [hs₃.1, hs₃.2.1, hs₃.2.2] using h₁₀

/-- A finite tetrahedron slice has an affine support function in its parent curvature. -/
private theorem slice (w : Fin 3 → ℝ) :
    ∃ (f : ℝ → Fin 3 → ℝ) (m c : ℝ),
      (∀ t, |t| ≤ 1 → (∀ j, |f t j| ≤ 1) ∧ ∑ j, f t j = t) ∧
      (∀ t, (t = -1 ∨ t = 1) → ∀ j, f t j = -1 ∨ f t j = 1) ∧
      (∀ t, ∑ j, w j * f t j = c + m * t) ∧
      ∀ y : Fin 3 → ℝ, (∀ j, |y j| ≤ 1) →
        ∑ j, w j * y j ≤ c + m * ∑ j, y j := by
  classical
  obtain ⟨σ, h₀, h₁⟩ := ordered_coordinates w
  let f (t : ℝ) (j : Fin 3) := (![(-1 : ℝ), t, 1] : Fin 3 → ℝ) (σ.symm j)
  have hf (t : ℝ) (i : Fin 3) : f t (σ i) = (![(-1 : ℝ), t, 1] : Fin 3 → ℝ) i := by
    simp [f]
  refine ⟨f, w (σ 1), w (σ 2) - w (σ 0), ?_, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro i
      obtain ⟨j, rfl⟩ := σ.surjective i
      rw [hf]
      fin_cases j <;> simp [ht]
    · rw [← Equiv.sum_comp σ (f t)]
      simp only [hf, Fin.sum_univ_three]
      norm_num
  · intro t ht i
    obtain ⟨j, rfl⟩ := σ.surjective i
    rw [hf]
    fin_cases j
    · exact Or.inl rfl
    · exact ht
    · exact Or.inr rfl
  · intro t
    rw [← Equiv.sum_comp σ (fun j => w j * f t j)]
    simp only [hf, Fin.sum_univ_three]
    norm_num
    ring
  · intro y hy
    rw [← Equiv.sum_comp σ (fun j => w j * y j), ← Equiv.sum_comp σ y]
    simp only [Fin.sum_univ_three]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h₀)
      (show 0 ≤ y (σ 0) + 1 by linarith [(abs_le.mp (hy (σ 0))).1]),
      mul_nonneg (sub_nonneg.mpr h₁)
      (show 0 ≤ 1 - y (σ 2) by linarith [(abs_le.mp (hy (σ 2))).2])]

/-- Every linear objective on the bounded stack-curvature polytope has a
maximizer with all face curvatures equal to plus or minus one. -/
theorem Build.exists_sign_maximizer {n : ℕ} (b : Build n) (w : Face n → ℝ) :
    ∃ x : Face n → ℝ, b.Valid x ∧ (∀ i, x i = -1 ∨ x i = 1) ∧
      ∀ y, b.Valid y → (∑ i, w i * y i) ≤ ∑ i, w i * x i := by
  classical
  induction b with
  | root =>
    by_cases h : 0 ≤ w ()
    · refine ⟨fun _ => 1, by norm_num [Build.Valid], fun _ => Or.inr rfl, ?_⟩
      intro y hy
      simpa using mul_le_mul_of_nonneg_left (abs_le.mp hy).2 h
    · refine ⟨fun _ => -1, by norm_num [Build.Valid], fun _ => Or.inl rfl, ?_⟩
      intro y hy
      simpa using mul_le_mul_of_nonpos_left (abs_le.mp hy).1 (le_of_not_ge h)
  | @attach n b p ih =>
    obtain ⟨f, m, c, hf, hs, hlin, hu⟩ := slice (w ∘ Sum.inr)
    let w' (i : Face n) := w (Sum.inl i) + if i = p then m else 0
    obtain ⟨x, hx, hxs, hmax⟩ := ih w'
    have hsums (y : Face n → ℝ) :
        ∑ i, w' i * y i = (∑ i, w (Sum.inl i) * y i) + m * y p := by
      simp [w', add_mul, sum_add_distrib, ite_mul]
    let x' : Face (n + 1) → ℝ := Sum.elim x (f (x p))
    have hxp := hf _ (b.abs_le_one hx p)
    refine ⟨x', ⟨hx, hxp.1, hxp.2⟩, ?_, ?_⟩
    · rintro (i | j)
      · exact hxs i
      · exact hs _ (hxs p) j
    · intro y hy
      have hbound := hu (y ∘ Sum.inr) hy.2.1
      have hq := hmax (y ∘ Sum.inl) hy.1
      rw [hsums, hsums] at hq
      change (∑ i : Face n ⊕ Fin 3, w i * y i) ≤ (∑ i : Face n ⊕ Fin 3, w i * x' i)
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      change (∑ i, w (Sum.inl i) * y (Sum.inl i)) + (∑ j, (w ∘ Sum.inr) j * (y ∘ Sum.inr) j) ≤
          (∑ i, w (Sum.inl i) * x i) + (∑ j, (w ∘ Sum.inr) j * f (x p) j)
      rw [hlin]
      have he : ∑ j, (y ∘ Sum.inr) j = y (Sum.inl p) := hy.2.2
      rw [he] at hbound
      simp only [Function.comp_apply] at hq
      linarith


/-- The vertices of a 3-tree, starting from the three vertices of the root face. -/
abbrev Vertex : ℕ → Type
  | 0 => Fin 3
  | n + 1 => Vertex n ⊕ Unit

instance (n : ℕ) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 3))
  | succ n ih => exact inferInstanceAs (Fintype (Vertex n ⊕ Unit))

/-- Ordered boundary vertices of each triangle. The three children are oriented
compatibly with the parent, so their boundaries sum to its boundary. -/
def Build.triangle : {n : ℕ} → Build n → Face n → Vertex n × Vertex n × Vertex n
  | _, .root, () => (0, 1, 2)
  | _, .attach b _, .inl i =>
      let (a, u, v) := b.triangle i
      (.inl a, .inl u, .inl v)
  | _, .attach b p, .inr j =>
      let (a, u, v) := b.triangle p
      (![ (.inl a, .inl u, .inr ()), (.inl u, .inl v, .inr ()),
          (.inl v, .inl a, .inr ()) ] : Fin 3 → _) j

theorem Build.triangle_distinct {n : ℕ} (b : Build n) (i : Face n) :
    (b.triangle i).1 ≠ (b.triangle i).2.1 ∧
    (b.triangle i).2.1 ≠ (b.triangle i).2.2 ∧
    (b.triangle i).2.2 ≠ (b.triangle i).1 := by
  induction b with
  | root => cases i; decide
  | attach b p ih =>
    rcases i with i | j
    · simpa [Build.triangle] using ih i
    · have hp := ih p
      fin_cases j
      · simpa [Build.triangle] using hp.1
      · simpa [Build.triangle] using hp.2.1
      · simpa [Build.triangle] using hp.2.2

private noncomputable def arrow (a b : ℝ) : ℝ := if a < b then 1 else -1
private noncomputable def orient (a b c : ℝ) : ℝ := arrow a b + arrow b c + arrow c a

private theorem put_between {a b : ℝ} (h : a < b) (S : Finset ℝ) :
    ∃ x ∉ S, a < x ∧ x < b := by
  obtain ⟨x, hx, hxS⟩ := (Set.Ioo_infinite h).exists_notMem_finset S
  exact ⟨x, hxS, hx.1, hx.2⟩

private theorem put_above (a : ℝ) (S : Finset ℝ) : ∃ x ∉ S, a < x := by
  obtain ⟨x, hx, hax, _⟩ := put_between (lt_add_one a) S
  exact ⟨x, hx, hax⟩

private theorem extensions {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (S : Finset ℝ) (x y z : ℝ)
    (hx : x = -1 ∨ x = 1) (hy : y = -1 ∨ y = 1) (hz : z = -1 ∨ z = 1)
    (hs : x + y + z = orient a b c) :
    ∃ p ∉ S, orient a b p = x ∧ orient b c p = y ∧ orient c a p = z := by
  rcases lt_or_gt_of_ne hab with hab | hba <;>
    rcases lt_or_gt_of_ne hbc with hbc | hcb <;>
    rcases lt_or_gt_of_ne hca with hca | hac
  all_goals try solve | linarith only [hab, hbc, hca] | linarith only [hba, hcb, hac]
  all_goals rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  all_goals simp only [orient, arrow] at hs
  all_goals split_ifs at hs <;> try linarith
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hab S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hbc S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hbig⟩ := put_above (max a (max b c)) S
    have hpa : a < p := (le_max_left ..).trans_lt hbig
    have hpb : b < p := ((le_max_left ..).trans (le_max_right ..)).trans_lt hbig
    have hpc : c < p := ((le_max_right ..).trans (le_max_right ..)).trans_lt hbig
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hab S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hbig⟩ := put_above (max a (max b c)) S
    have hpa : a < p := (le_max_left ..).trans_lt hbig
    have hpb : b < p := ((le_max_left ..).trans (le_max_right ..)).trans_lt hbig
    have hpc : c < p := ((le_max_right ..).trans (le_max_right ..)).trans_lt hbig
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hca S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hac S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hcb S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hbig⟩ := put_above (max a (max b c)) S
    have hpa : a < p := (le_max_left ..).trans_lt hbig
    have hpb : b < p := ((le_max_left ..).trans (le_max_right ..)).trans_lt hbig
    have hpc : c < p := ((le_max_right ..).trans (le_max_right ..)).trans_lt hbig
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hbig⟩ := put_above (max a (max b c)) S
    have hpa : a < p := (le_max_left ..).trans_lt hbig
    have hpb : b < p := ((le_max_left ..).trans (le_max_right ..)).trans_lt hbig
    have hpc : c < p := ((le_max_right ..).trans (le_max_right ..)).trans_lt hbig
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hbc S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hca S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hac S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hbig⟩ := put_above (max a (max b c)) S
    have hpa : a < p := (le_max_left ..).trans_lt hbig
    have hpb : b < p := ((le_max_left ..).trans (le_max_right ..)).trans_lt hbig
    have hpc : c < p := ((le_max_right ..).trans (le_max_right ..)).trans_lt hbig
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hba S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hbig⟩ := put_above (max a (max b c)) S
    have hpa : a < p := (le_max_left ..).trans_lt hbig
    have hpb : b < p := ((le_max_left ..).trans (le_max_right ..)).trans_lt hbig
    have hpc : c < p := ((le_max_right ..).trans (le_max_right ..)).trans_lt hbig
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hcb S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)
  · obtain ⟨p, hp, hlo, hhi⟩ := put_between hba S
    refine ⟨p, hp, ?_, ?_, ?_⟩ <;>
      (simp only [orient, arrow]; split_ifs <;> linarith)

/-- Triangle curvature of the unit gains from a strict real ranking. -/
noncomputable def Build.orderCurvature {n : ℕ} (b : Build n) (s : Vertex n → ℝ) (i : Face n) : ℝ :=
  let (a, u, v) := b.triangle i
  orient (s a) (s u) (s v)

/-- Every feasible sign curvature of a stacked 3-tree is realized by a total
order of its vertices. Inserting a vertex in a specified gap preserves every
older comparison. -/
theorem Build.exists_total_order {n : ℕ} (b : Build n) (x : Face n → ℝ)
    (hx : b.Valid x) (hs : ∀ i, x i = -1 ∨ x i = 1) :
    ∃ rank : Vertex n ↪ ℝ, ∀ i, b.orderCurvature rank i = x i := by
  induction b with
  | root =>
    have hpos : Function.Injective (fun i : Fin 3 => (i.val : ℝ)) := by
      intro a b h
      change (a.val : ℝ) = (b.val : ℝ) at h
      exact Fin.ext (by exact_mod_cast h)
    rcases hs () with h | h
    · let r (i : Fin 3) := -(i.val : ℝ)
      have hinj : Function.Injective r := fun _ _ e => hpos (neg_injective e)
      refine ⟨⟨r, hinj⟩, ?_⟩
      rintro ⟨⟩
      rw [h]
      norm_num [Build.orderCurvature, Build.triangle, orient, arrow, r]
    · refine ⟨⟨fun i : Fin 3 => (i.val : ℝ), hpos⟩, ?_⟩
      rintro ⟨⟩
      rw [h]
      norm_num [Build.orderCurvature, Build.triangle, orient, arrow]
  | @attach n b p ih =>
    classical
    obtain ⟨rank, hro⟩ := ih (x ∘ Sum.inl) hx.1 (fun i => hs (Sum.inl i))
    let S := Finset.univ.image rank
    let a := (b.triangle p).1
    let u := (b.triangle p).2.1
    let v := (b.triangle p).2.2
    have hp := b.triangle_distinct p
    have hsum : x (Sum.inr 0) + x (Sum.inr 1) + x (Sum.inr 2) = orient (rank a) (rank u) (rank v) := by
      have hh := hx.2.2
      rw [Fin.sum_univ_three] at hh
      exact hh.trans (hro p).symm
    obtain ⟨t, ht, ha, hu, hv⟩ := extensions (fun h => hp.1 (rank.injective h))
      (fun h => hp.2.1 (rank.injective h)) (fun h => hp.2.2 (rank.injective h)) S
      _ _ _ (hs (Sum.inr 0)) (hs (Sum.inr 1)) (hs (Sum.inr 2)) hsum
    let e : Vertex (n + 1) ↪ ℝ := ⟨Sum.elim rank (fun _ => t), by
      rintro (i | ⟨⟩) (j | ⟨⟩) he
      · exact congrArg Sum.inl (rank.injective he)
      · exact (ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he⟩)).elim
      · exact (ht (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he.symm⟩)).elim
      · rfl⟩
    refine ⟨e, ?_⟩
    rintro (i | j)
    · exact hro i
    · fin_cases j
      · exact ha
      · exact hu
      · exact hv

/-- The total-order curvature profiles maximize every real linear functional
on the triangle-defect unit ball of a stacked 3-tree. -/
theorem Build.exists_order_maximizer {n : ℕ} (b : Build n) (w : Face n → ℝ) :
    ∃ rank : Vertex n ↪ ℝ, b.Valid (b.orderCurvature rank) ∧
      ∀ y, b.Valid y → (∑ i, w i * y i) ≤ ∑ i, w i * b.orderCurvature rank i := by
  obtain ⟨x, hx, hs, hm⟩ := b.exists_sign_maximizer w
  obtain ⟨rank, he⟩ := b.exists_total_order x hx hs
  have h : b.orderCurvature rank = x := funext he
  exact ⟨rank, h.symm ▸ hx, fun y hy => by rw [h]; exact hm y hy⟩

/-- Sign profiles consist of feasible assignments with every face coordinate saturated. -/
def Build.SignProfiles {n : ℕ} (b : Build n) : Set (Face n → ℝ) :=
  {x | b.Valid x ∧ ∀ i, x i = -1 ∨ x i = 1}

private noncomputable def rootSigns : Bool ≃ Build.root.SignProfiles :=
  Equiv.ofBijective
    (fun j => ⟨fun _ => if j then 1 else -1, by cases j <;> norm_num [Build.SignProfiles, Build.Valid]⟩)
    (by
      constructor
      · intro a b he
        have h := congrArg (fun x : Build.root.SignProfiles => x.val ()) he
        change (if a then 1 else -1 : ℝ) = (if b then 1 else -1) at h
        cases a <;> cases b <;> first | rfl | norm_num at h
      · rintro ⟨x, hx, hs⟩
        rcases hs () with he | he
        · exact ⟨false, Subtype.ext (by funext i; cases i; exact he.symm)⟩
        · exact ⟨true, Subtype.ext (by funext i; cases i; exact he.symm)⟩)

private def childSigns (s : ℝ) (j : Fin 3) (i : Fin 3) : ℝ :=
  if i = j then -s else s

private theorem sum_childSigns (s : ℝ) (j : Fin 3) : ∑ i, childSigns s j i = s := by
  fin_cases j <;> simp [childSigns, Fin.sum_univ_three]

private theorem exists_childSigns (s : ℝ) (hs : s = -1 ∨ s = 1) (y : Fin 3 → ℝ)
    (hy : ∀ j, y j = -1 ∨ y j = 1) (he : ∑ j, y j = s) :
    ∃ j : Fin 3, childSigns s j = y := by
  rw [Fin.sum_univ_three] at he
  rcases hs with rfl | rfl <;> rcases hy 0 with h₀ | h₀ <;>
    rcases hy 1 with h₁ | h₁ <;> rcases hy 2 with h₂ | h₂ <;>
    norm_num [h₀, h₁, h₂] at he
  · refine ⟨2, ?_⟩
    funext i
    fin_cases i <;> norm_num [childSigns, h₀, h₁, h₂]
  · refine ⟨1, ?_⟩
    funext i
    fin_cases i <;> norm_num [childSigns, h₀, h₁, h₂]
  · refine ⟨0, ?_⟩
    funext i
    fin_cases i <;> norm_num [childSigns, h₀, h₁, h₂]
  · refine ⟨0, ?_⟩
    funext i
    fin_cases i <;> norm_num [childSigns, h₀, h₁, h₂]
  · refine ⟨1, ?_⟩
    funext i
    fin_cases i <;> norm_num [childSigns, h₀, h₁, h₂]
  · refine ⟨2, ?_⟩
    funext i
    fin_cases i <;> norm_num [childSigns, h₀, h₁, h₂]

private noncomputable def attachSigns {n : ℕ} (b : Build n) (p : Face n) :
    b.SignProfiles × Fin 3 ≃ (b.attach p).SignProfiles := by
  let f (v : b.SignProfiles × Fin 3) : (b.attach p).SignProfiles :=
    ⟨Sum.elim v.1.val (childSigns (v.1.val p) v.2), by
      have hp := v.1.prop.2 p
      refine ⟨⟨v.1.prop.1, ?_, sum_childSigns _ _⟩, ?_⟩
      · intro j
        have h := b.abs_le_one v.1.prop.1 p
        change |childSigns (v.1.val p) v.2 j| ≤ 1
        unfold childSigns
        split_ifs <;> simpa using h
      · rintro (i | j)
        · exact v.1.prop.2 i
        · change childSigns (v.1.val p) v.2 j = -1 ∨ childSigns (v.1.val p) v.2 j = 1
          rcases hp with hp | hp <;> by_cases h : j = v.2 <;> norm_num [childSigns, h, hp]⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨x, j⟩ ⟨y, l⟩ he
    have hxy : x = y := Subtype.ext (funext fun i =>
      congrArg (fun z : (b.attach p).SignProfiles => z.val (Sum.inl i)) he)
    subst y
    refine Prod.ext rfl (by_contra fun hn => ?_)
    have h := congrArg (fun z : (b.attach p).SignProfiles => z.val (Sum.inr j)) he
    change childSigns (x.val p) j j = childSigns (x.val p) l j at h
    rcases x.prop.2 p with hp | hp <;> norm_num [childSigns, hn, hp] at h
  · rintro ⟨x, hx, hs⟩
    let old : b.SignProfiles := ⟨x ∘ Sum.inl, hx.1, fun i => hs (Sum.inl i)⟩
    obtain ⟨j, hj⟩ := exists_childSigns (old.val p) (old.prop.2 p)
      (x ∘ Sum.inr) (fun i => hs (Sum.inr i)) hx.2.2
    refine ⟨⟨old, j⟩, Subtype.ext (funext fun i => ?_)⟩
    rcases i with i | i
    · rfl
    · exact congrFun hj i

instance {n : ℕ} (b : Build n) : Finite b.SignProfiles := by
  induction b with
  | root => exact Finite.of_equiv Bool rootSigns
  | attach b p => exact Finite.of_equiv (b.SignProfiles × Fin 3) (attachSigns b p)

private theorem card_signProfiles {n : ℕ} (b : Build n) : Nat.card b.SignProfiles = 2 * 3 ^ n := by
  induction b with
  | root => simpa using (Nat.card_congr rootSigns).symm
  | @attach n b p ih =>
    rw [← Nat.card_congr (attachSigns b p), Nat.card_prod, ih, Nat.card_fin, pow_succ, mul_assoc]

/-- The linear constraints on a stacking history define a convex set. -/
theorem Build.convex_valid {n : ℕ} (b : Build n) : Convex ℝ {x | b.Valid x} := by
  induction b with
  | root =>
    intro x hx y hy a d ha hd hab
    change |x ()| ≤ 1 at hx
    change |y ()| ≤ 1 at hy
    change |a * x () + d * y ()| ≤ 1
    rw [abs_le] at *
    constructor <;> nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.1),
      mul_nonneg hd (sub_nonneg.mpr hy.1), mul_nonneg ha (sub_nonneg.mpr hx.2),
      mul_nonneg hd (sub_nonneg.mpr hy.2)]
  | @attach n b p ih =>
    intro x hx y hy a d ha hd hab
    have hxo : b.Valid (x ∘ Sum.inl) ∧ (∀ j : Fin 3, |x (Sum.inr j)| ≤ 1) ∧
        ∑ j : Fin 3, x (Sum.inr j) = x (Sum.inl p) := hx
    have hyo : b.Valid (y ∘ Sum.inl) ∧ (∀ j : Fin 3, |y (Sum.inr j)| ≤ 1) ∧
        ∑ j : Fin 3, y (Sum.inr j) = y (Sum.inl p) := hy
    refine ⟨ih hxo.1 hyo.1 ha hd hab, ?_, ?_⟩
    · intro i
      change |a * x (Sum.inr i) + d * y (Sum.inr i)| ≤ 1
      have hx1 := abs_le.mp (hxo.2.1 i)
      have hy1 := abs_le.mp (hyo.2.1 i)
      apply abs_le.mpr
      constructor <;> nlinarith [mul_nonneg ha (sub_nonneg.mpr hx1.1),
        mul_nonneg hd (sub_nonneg.mpr hy1.1), mul_nonneg ha (sub_nonneg.mpr hx1.2),
        mul_nonneg hd (sub_nonneg.mpr hy1.2)]
    · change (∑ j : Fin 3, (a * x (Sum.inr j) + d * y (Sum.inr j))) =
        a * x (Sum.inl p) + d * y (Sum.inl p)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hxo.2.2, hyo.2.2]

/-- Every compatible bounded curvature profile is a convex combination of sign profiles. -/
theorem Build.valid_eq_convexHull_signProfiles {n : ℕ} (b : Build n) :
    {x | b.Valid x} = convexHull ℝ b.SignProfiles := by
  classical
  have hs : b.SignProfiles.Finite := Set.toFinite _
  apply Set.Subset.antisymm ?_ (convexHull_min (fun _ h => h.1) b.convex_valid)
  intro x hx
  by_contra h
  obtain ⟨f, t, hf, htx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ b.SignProfiles) (hs.isClosed_convexHull ℝ) h
  let w (i : Face n) := f (Pi.single i 1)
  have hf_sum (y : Face n → ℝ) : f y = ∑ i, w i * y i := by
    calc
      f y = f (∑ i, Pi.single i (y i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, f (y i • Pi.single i 1) := by simp [← Pi.single_smul]
      _ = ∑ i, w i * y i := by simp [w, mul_comm]
  obtain ⟨y, hy, hys, hmax⟩ := b.exists_sign_maximizer w
  have hfy := hf y (subset_convexHull ℝ b.SignProfiles ⟨hy, hys⟩)
  exact (hfy.trans htx).not_ge (by simpa only [← hf_sum] using hmax x hx)

/-- The extreme points of the bounded curvature polytope are exactly the sign profiles. -/
theorem Build.extremePoints_eq_signProfiles {n : ℕ} (b : Build n) :
    ({x | b.Valid x} : Set (Face n → ℝ)).extremePoints ℝ = b.SignProfiles := by
  apply Set.Subset.antisymm ?_ ?_
  · rw [b.valid_eq_convexHull_signProfiles]
    exact extremePoints_convexHull_subset
  · intro x hx
    refine mem_extremePoints_iff_left.mpr ⟨hx.1, ?_⟩
    intro y hy z hz hseg
    rcases hseg with ⟨a, d, ha, hd, hsum, hseg⟩
    funext i
    have hyi := abs_le.mp (b.abs_le_one hy i)
    have hzi := abs_le.mp (b.abs_le_one hz i)
    have he : a * y i + d * z i = x i := congrFun hseg i
    rcases hx.2 i with hxi | hxi
    · rw [hxi] at he ⊢
      by_contra! hn
      have hlt : -1 < y i := lt_of_le_of_ne hyi.1 (Ne.symm hn)
      nlinarith [mul_pos ha (sub_pos.mpr hlt), mul_nonneg hd.le (sub_nonneg.mpr hzi.1)]
    · rw [hxi] at he ⊢
      by_contra! hn
      have hlt : y i < 1 := lt_of_le_of_ne hyi.2 hn
      nlinarith [mul_pos ha (sub_pos.mpr hlt), mul_nonneg hd.le (sub_nonneg.mpr hzi.2)]

/-- With the three root vertices and n further insertions, there are exactly two times
three to the nth power extreme curvature profiles. -/
theorem Build.card_extremePoints {n : ℕ} (b : Build n) :
    Nat.card (({x | b.Valid x} : Set (Face n → ℝ)).extremePoints ℝ) = 2 * 3 ^ n := by
  rw [b.extremePoints_eq_signProfiles]
  exact card_signProfiles b

/-- The face coboundary of a skew scalar gain. -/
def Build.curvature {n : ℕ} (b : Build n) (g : Vertex n → Vertex n → ℝ) (i : Face n) : ℝ :=
  let t := b.triangle i
  g t.1 t.2.1 + g t.2.1 t.2.2 + g t.2.2 t.1

private theorem curvature_attach_inl {n : ℕ} (b : Build n) (p : Face n)
    (g : Vertex (n + 1) → Vertex (n + 1) → ℝ) (i : Face n) :
    (b.attach p).curvature g (Sum.inl i) =
      b.curvature (fun u v => g (Sum.inl u) (Sum.inl v)) i := by
  simp [Build.curvature, Build.triangle]

private theorem curvature_attach_sum {n : ℕ} (b : Build n) (p : Face n)
    (g : Vertex (n + 1) → Vertex (n + 1) → ℝ)
    (hg : ∀ u v, g v u = -g u v) :
    (∑ i : Fin 3, (b.attach p).curvature g (Sum.inr i)) =
      (b.attach p).curvature g (Sum.inl p) := by
  rw [Fin.sum_univ_three]
  simp only [Build.curvature, Build.triangle, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  let t := b.triangle p
  change g (.inl t.1) (.inl t.2.1) + g (.inl t.2.1) (.inr ()) + g (.inr ()) (.inl t.1) +
    (g (.inl t.2.1) (.inl t.2.2) + g (.inl t.2.2) (.inr ()) + g (.inr ()) (.inl t.2.1)) +
    (g (.inl t.2.2) (.inl t.1) + g (.inl t.1) (.inr ()) + g (.inr ()) (.inl t.2.2)) =
    g (.inl t.1) (.inl t.2.1) + g (.inl t.2.1) (.inl t.2.2) + g (.inl t.2.2) (.inl t.1)
  rw [hg (.inl t.1) (.inr ()), hg (.inl t.2.1) (.inr ()), hg (.inl t.2.2) (.inr ())]
  ring

/-- Bounded skew gains have feasible curvature profiles. -/
theorem Build.valid_curvature {n : ℕ} (b : Build n) (g : Vertex n → Vertex n → ℝ)
    (hg : ∀ u v, g v u = -g u v) (h : ∀ i, |b.curvature g i| ≤ 1) :
    b.Valid (b.curvature g) := by
  induction b with
  | root => exact h ()
  | attach b p ih =>
    refine ⟨?_, fun i => h (Sum.inr i), curvature_attach_sum b p g hg⟩
    simp only [Function.comp_def, curvature_attach_inl]
    exact ih _ (fun u v => hg _ _) (fun i => by simpa only [curvature_attach_inl] using h (Sum.inl i))

/-- Every feasible curvature profile is realized by skew scalar gains. -/
theorem Build.exists_gain {n : ℕ} (b : Build n) (x : Face n → ℝ) (hx : b.Valid x) :
    ∃ g : Vertex n → Vertex n → ℝ, (∀ u v, g v u = -g u v) ∧ b.curvature g = x := by
  classical
  induction b with
  | root =>
    let g (u v : Fin 3) := if u = 0 ∧ v = 1 then x () else
      if u = 1 ∧ v = 0 then -x () else 0
    refine ⟨g, ?_, ?_⟩
    · intro u v
      fin_cases u <;> fin_cases v <;> simp [g]
    · funext i
      cases i
      simp [Build.curvature, Build.triangle, g]
  | @attach n b p ih =>
    obtain ⟨g, hskew, hg⟩ := ih (x ∘ Sum.inl) hx.1
    let t := b.triangle p
    let a := t.1
    let u := t.2.1
    let v := t.2.2
    have hne : a ≠ u ∧ u ≠ v ∧ v ≠ a := b.triangle_distinct p
    let transport (i : Vertex n) :=
      if i = u then x (Sum.inr 0) - g a u else
      if i = v then x (Sum.inr 0) + x (Sum.inr 1) - g a u - g u v else 0
    have ha : transport a = 0 := by simp [transport, hne.1, hne.2.2.symm]
    have hu : transport u = x (Sum.inr 0) - g a u := by simp [transport]
    have hv : transport v = x (Sum.inr 0) + x (Sum.inr 1) - g a u - g u v := by
      simp [transport, hne.2.1.symm]
    let g' : Vertex (n + 1) → Vertex (n + 1) → ℝ
      | .inl i, .inl j => g i j
      | .inl i, .inr _ => transport i
      | .inr _, .inl j => -transport j
      | .inr _, .inr _ => 0
    have hg' : ∀ i j, g' j i = -g' i j := by
      rintro (i | ⟨⟩) (j | ⟨⟩)
      · exact hskew i j
      · rfl
      · simp [g']
      · simp [g']
    have h0 : (b.attach p).curvature g' (Sum.inr 0) = x (Sum.inr 0) := by
      change g a u + transport u - transport a = x (Sum.inr 0)
      rw [hu, ha]
      ring
    have h1 : (b.attach p).curvature g' (Sum.inr 1) = x (Sum.inr 1) := by
      change g u v + transport v - transport u = x (Sum.inr 1)
      rw [hu, hv]
      ring
    have hold (i : Face n) : (b.attach p).curvature g' (Sum.inl i) = x (Sum.inl i) := by
      rw [curvature_attach_inl]
      exact congrFun hg i
    have h2 : (b.attach p).curvature g' (Sum.inr 2) = x (Sum.inr 2) := by
      have hh := curvature_attach_sum b p g' hg'
      have hxsum := hx.2.2
      rw [Fin.sum_univ_three] at hxsum hh
      rw [h0, h1, hold] at hh
      linarith
    refine ⟨g', hg', funext fun i => ?_⟩
    rcases i with i | i
    · exact hold i
    · fin_cases i <;> assumption

private theorem arrow_skew {a b : ℝ} (h : a ≠ b) : arrow b a = -arrow a b := by
  rcases lt_or_gt_of_ne h with h | h
  · simp [arrow, h, h.not_gt]
  · simp [arrow, h, h.not_gt]

private theorem orient_sign {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    orient a b c = -1 ∨ orient a b c = 1 := by
  rcases lt_or_gt_of_ne hab with hab | hba <;>
    rcases lt_or_gt_of_ne hbc with hbc | hcb <;>
    rcases lt_or_gt_of_ne hca with hca | hac <;>
    (unfold orient arrow; split_ifs <;> norm_num <;> exfalso <;> linarith)

/-- Every total order yields a feasible sign profile, and every such profile comes from a total order. -/
theorem Build.range_orderCurvature_eq_signProfiles {n : ℕ} (b : Build n) :
    Set.range (fun rank : Vertex n ↪ ℝ => b.orderCurvature rank) = b.SignProfiles := by
  classical
  apply Set.Subset.antisymm ?_ ?_
  · rintro x ⟨rank, rfl⟩
    let g (u v : Vertex n) := if u = v then 0 else arrow (rank u) (rank v)
    have hskew (u v : Vertex n) : g v u = -g u v := by
      by_cases h : u = v
      · simp [g, h]
      · simpa [g, h, Ne.symm h] using arrow_skew (fun e => h (rank.injective e))
    have hcurv (i : Face n) : b.curvature g i = b.orderCurvature rank i := by
      have h := b.triangle_distinct i
      simp [Build.curvature, Build.orderCurvature, orient, g, h.1, h.2.1, h.2.2]
    have hs (i : Face n) : b.orderCurvature rank i = -1 ∨ b.orderCurvature rank i = 1 := by
      have h := b.triangle_distinct i
      exact orient_sign (fun e => h.1 (rank.injective e)) (fun e => h.2.1 (rank.injective e))
        (fun e => h.2.2 (rank.injective e))
    refine ⟨?_, hs⟩
    change b.Valid (b.orderCurvature rank)
    rw [← funext hcurv]
    refine b.valid_curvature g hskew fun i => ?_
    rw [hcurv]
    rcases hs i with he | he <;> norm_num [he]
  · intro x hx
    obtain ⟨rank, h⟩ := b.exists_total_order x hx.1 hx.2
    exact ⟨rank, funext h⟩

/-- The scalar triangle-flat gain polytope in face coordinates is the convex hull
of total-order gains. -/
theorem Build.valid_eq_convexHull_orders {n : ℕ} (b : Build n) :
    {x | b.Valid x} = convexHull ℝ (Set.range (fun rank : Vertex n ↪ ℝ => b.orderCurvature rank)) := by
  rw [b.range_orderCurvature_eq_signProfiles]
  exact b.valid_eq_convexHull_signProfiles

/-- Real triangle fillings carry the sum of absolute face coefficients. -/
abbrev FaceChain (n : ℕ) := PiLp 1 (fun _ : Face n => ℝ)

/-- Pair a list of oriented face coefficients with a curvature profile. -/
noncomputable def FaceChain.pair {n : ℕ} (a : FaceChain n) (x : Face n → ℝ) : ℝ :=
  ∑ i, a i * x i

/-- A filling has zero boundary when its pairing vanishes for every skew gain. -/
noncomputable def Build.zeroBoundary {n : ℕ} (b : Build n) : Submodule ℝ (FaceChain n) where
  carrier := {a | ∀ g : Vertex n → Vertex n → ℝ, (∀ u v, g v u = -g u v) →
    a.pair (b.curvature g) = 0}
  zero_mem' := by simp [FaceChain.pair]
  add_mem' := by
    intro a d ha hd g hg
    change (a + d).pair (b.curvature g) = 0
    have he : (a + d).pair (b.curvature g) = a.pair (b.curvature g) + d.pair (b.curvature g) := by
      simp [FaceChain.pair, add_mul, Finset.sum_add_distrib]
    rw [he, ha g hg, hd g hg, add_zero]
  smul_mem' := by
    intro k a ha g hg
    change (k • a).pair (b.curvature g) = 0
    simp only [FaceChain.pair, PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    change k * a.pair (b.curvature g) = 0
    rw [ha g hg, mul_zero]

instance {n : ℕ} (b : Build n) : IsClosed (b.zeroBoundary : Set (FaceChain n)) := by
  let A (g : Vertex n → Vertex n → ℝ) := {a : FaceChain n | a.pair (b.curvature g) = 0}
  have hA (g : Vertex n → Vertex n → ℝ) : IsClosed (A g) := by
    apply isClosed_eq ?_ continuous_const
    unfold FaceChain.pair
    exact continuous_finsetSum _ fun i _ => (PiLp.continuous_apply 1 _ i).mul continuous_const
  have he : (b.zeroBoundary : Set (FaceChain n)) =
      ⋂ g, ⋂ (_ : ∀ u v, g v u = -g u v), A g := by
    ext a
    simp [Build.zeroBoundary, A]
  rw [he]
  exact isClosed_iInter fun g => isClosed_iInter fun _ => hA g

/-- The triangle-filling norm is the quotient of the face ℓ¹ norm by the boundary kernel. -/
abbrev Build.TriangleCycles {n : ℕ} (b : Build n) := FaceChain n ⧸ b.zeroBoundary

private theorem norm_faceChain {n : ℕ} (a : FaceChain n) : ‖a‖ = ∑ i, |a i| := by
  rw [PiLp.norm_eq_sum (by norm_num : 0 < ENNReal.toReal 1)]
  simp [Real.norm_eq_abs]

private theorem pair_le_norm {n : ℕ} (a : FaceChain n) (x : Face n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) : a.pair x ≤ ‖a‖ := by
  rw [FaceChain.pair, norm_faceChain]
  refine Finset.sum_le_sum fun i _ => ?_
  calc
    a i * x i ≤ |a i * x i| := le_abs_self _
    _ = |a i| * |x i| := abs_mul _ _
    _ ≤ |a i| * 1 := mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)
    _ = |a i| := mul_one _

private noncomputable def faceUnit {n : ℕ} (i : Face n) : FaceChain n :=
  haveI := Classical.decEq (Face n)
  PiLp.single 1 i 1

private theorem faceUnit_apply {n : ℕ} (i j : Face n) :
    faceUnit i j = @ite ℝ (j = i) (Classical.propDecidable _) 1 0 := by
  classical
  simp [faceUnit, PiLp.single_apply]

private theorem pair_faceUnit {n : ℕ} (x : Face n → ℝ) (i : Face n) :
    (faceUnit i).pair x = x i := by
  classical
  simp [FaceChain.pair, faceUnit_apply, ite_mul]

private theorem norm_faceUnit {n : ℕ} (i : Face n) : ‖faceUnit i‖ = 1 := by
  classical
  simp [norm_faceChain, faceUnit_apply, apply_ite abs]

private theorem pair_eq_of_same_boundary {n : ℕ} (b : Build n) (a d : FaceChain n)
    (h : (Submodule.Quotient.mk a : b.TriangleCycles) = Submodule.Quotient.mk d)
    (x : Face n → ℝ) (hx : b.Valid x) : a.pair x = d.pair x := by
  obtain ⟨g, hg, he⟩ := b.exists_gain x hx
  have hd : a - d ∈ b.zeroBoundary := (Submodule.Quotient.eq b.zeroBoundary).mp h
  have ht : (a - d).pair x = 0 := by rw [← he]; exact hd g hg
  have hs : (a - d).pair x = a.pair x - d.pair x := by
    simp [FaceChain.pair, sub_mul, Finset.sum_sub_distrib]
  linarith

private theorem pair_le_cycle_norm {n : ℕ} (b : Build n) (a : FaceChain n)
    (x : Face n → ℝ) (hx : b.Valid x) :
    a.pair x ≤ ‖(Submodule.Quotient.mk a : b.TriangleCycles)‖ := by
  let z : b.TriangleCycles := Submodule.Quotient.mk a
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨d, hd, hdn⟩ := Submodule.Quotient.norm_mk_lt z he
  have hp := pair_eq_of_same_boundary b a d hd.symm x hx
  exact (hp.le.trans ((pair_le_norm d x (b.abs_le_one hx)).trans hdn.le))

private theorem valid_of_annihilates_boundary {n : ℕ} (b : Build n) (x : Face n → ℝ)
    (hbound : ∀ i, |x i| ≤ 1)
    (hzero : ∀ a ∈ b.zeroBoundary, FaceChain.pair a x = 0) :
    b.Valid x := by
  induction b with
  | root => exact hbound ()
  | @attach n b p ih =>
    refine ⟨?_, fun i => hbound (Sum.inr i), ?_⟩
    · apply ih (x ∘ Sum.inl) (fun i => hbound (Sum.inl i))
      intro a ha
      let realLift : FaceChain (n + 1) := WithLp.toLp 1 (Sum.elim (WithLp.ofLp a) (fun _ => 0))
      have hz : realLift ∈ (b.attach p).zeroBoundary := by
        intro g hg
        change (∑ i : Face n ⊕ Fin 3, realLift i * (b.attach p).curvature g i) = 0
        rw [Fintype.sum_sum_type]
        simpa [realLift, curvature_attach_inl, FaceChain.pair] using
          ha (fun u v => g (Sum.inl u) (Sum.inl v)) (fun u v => hg _ _)
      have ht := hzero realLift hz
      change (∑ i : Face n ⊕ Fin 3, realLift i * x i) = 0 at ht
      rw [Fintype.sum_sum_type] at ht
      simpa [realLift, FaceChain.pair] using ht
    · let r : FaceChain (n + 1) :=
          ∑ i : Fin 3, faceUnit (Sum.inr i) - faceUnit (Sum.inl p)
      have hrel (y : Face (n + 1) → ℝ) : r.pair y =
          (∑ i : Fin 3, y (Sum.inr i)) - y (Sum.inl p) := by
        change (∑ j, ((∑ i : Fin 3, faceUnit (Sum.inr i)) - faceUnit (Sum.inl p) : FaceChain (n + 1)) j *
          y j) = _
        simp only [PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]
        change (∑ i : Fin 3, (faceUnit (Sum.inr i)).pair y) -
          (faceUnit (Sum.inl p)).pair y = _
        simp only [pair_faceUnit]
      have hr : r ∈ (b.attach p).zeroBoundary := by
        intro g hg
        rw [hrel, curvature_attach_sum b p g hg, sub_self]
      have ht := hzero r hr
      simpa [hrel, sub_eq_zero] using ht

private theorem dual_represents_curvature {n : ℕ} (b : Build n)
    (f : StrongDual ℝ b.TriangleCycles) (hf : ‖f‖ ≤ 1) :
    ∃ x : Face n → ℝ, b.Valid x ∧ ∀ a : FaceChain n,
      f (Submodule.Quotient.mk a) = a.pair x := by
  classical
  let x (i : Face n) := f (Submodule.Quotient.mk (faceUnit i))
  have hbound (i : Face n) : |x i| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖f‖ * ‖(Submodule.Quotient.mk (faceUnit i) : b.TriangleCycles)‖ :=
        f.le_opNorm _
      _ ≤ 1 * ‖faceUnit i‖ := mul_le_mul hf
        (Submodule.Quotient.norm_mk_le b.zeroBoundary _) (norm_nonneg _) zero_le_one
      _ = 1 := by rw [norm_faceUnit, one_mul]
  have hsum (a : FaceChain n) : f (Submodule.Quotient.mk a) = a.pair x := by
    let q := b.zeroBoundary.mkQ
    change f (q a) = a.pair x
    have ha : (∑ i, a i • faceUnit i) = a := by
      apply WithLp.ofLp_injective
      ext j
      simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change (∑ i, a i * faceUnit i j) = a j
      simp [faceUnit_apply, mul_ite]
    calc
      f (q a) = f (q (∑ i, a i • faceUnit i)) := by rw [ha]
      _ = a.pair x := by simp [FaceChain.pair, q, x]
  refine ⟨x, valid_of_annihilates_boundary b x hbound (fun a ha => ?_), hsum⟩
  rw [← hsum, (Submodule.Quotient.mk_eq_zero b.zeroBoundary).mpr ha, map_zero]

/-- The triangle-filling norm of a cycle is attained by a single total-order gain.
Every ranking gives at most that norm when paired with any filling of the cycle. -/
theorem Build.triangleNorm_eq_orderMaximum {n : ℕ} (b : Build n) (a : FaceChain n) :
    ∃ rank : Vertex n ↪ ℝ,
      ‖(Submodule.Quotient.mk a : b.TriangleCycles)‖ = a.pair (b.orderCurvature rank) ∧
      ∀ other : Vertex n ↪ ℝ, a.pair (b.orderCurvature other) ≤ a.pair (b.orderCurvature rank) := by
  obtain ⟨f, hf, hz⟩ := exists_dual_vector'' ℝ (Submodule.Quotient.mk a : b.TriangleCycles)
  obtain ⟨x, hx, he⟩ := dual_represents_curvature b f hf
  obtain ⟨rank, hr, hm⟩ := b.exists_order_maximizer (WithLp.ofLp a)
  have le_norm (other : Vertex n ↪ ℝ) :
      a.pair (b.orderCurvature other) ≤ ‖(Submodule.Quotient.mk a : b.TriangleCycles)‖ := by
    apply pair_le_cycle_norm b a
    have hs : b.orderCurvature other ∈ b.SignProfiles := by
      rw [← b.range_orderCurvature_eq_signProfiles]
      exact ⟨other, rfl⟩
    exact hs.1
  have heq : ‖(Submodule.Quotient.mk a : b.TriangleCycles)‖ =
      a.pair (b.orderCurvature rank) :=
    le_antisymm (by
      have hz' : f (Submodule.Quotient.mk a) = ‖(Submodule.Quotient.mk a : b.TriangleCycles)‖ := by
        simpa using hz
      rw [← hz', he]
      exact hm x hx) (le_norm rank)
  exact ⟨rank, heq, fun other => (le_norm other).trans_eq heq⟩

/-- The quotient norm is the infimum of the summed absolute coefficients over all
fillings with the given boundary. -/
theorem Build.triangleNorm_eq_inf {n : ℕ} (b : Build n) (z : b.TriangleCycles) :
    ‖z‖ = sInf {t | ∃ a : FaceChain n, Submodule.Quotient.mk a = z ∧ (∑ i, |a i|) = t} := by
  let S := {t | ∃ a : FaceChain n, Submodule.Quotient.mk a = z ∧ (∑ i, |a i|) = t}
  have hb : BddBelow S := ⟨0, fun t ⟨a, _, ha⟩ => ha ▸ Finset.sum_nonneg fun i _ => abs_nonneg (a i)⟩
  obtain ⟨a₀, ha₀, _⟩ := Submodule.Quotient.norm_mk_lt z zero_lt_one
  have hS : S.Nonempty := ⟨∑ i, |a₀ i|, a₀, ha₀, rfl⟩
  apply le_antisymm (le_csInf hS ?_) ?_
  · rintro t ⟨a, rfl, rfl⟩
    rw [← norm_faceChain]
    exact Submodule.Quotient.norm_mk_le b.zeroBoundary a
  · refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨a, ha, hlt⟩ := Submodule.Quotient.norm_mk_lt z he
    exact (csInf_le hb ⟨a, ha, rfl⟩).trans (by rw [← norm_faceChain]; exact hlt.le)

end StackedTriangleCurvature
