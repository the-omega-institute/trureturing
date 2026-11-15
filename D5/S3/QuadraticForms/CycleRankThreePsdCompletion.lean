/- GID: D5/S3/QuadraticForms/CycleRankThreePsdCompletion
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/CycleRankThreePsdCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cycle angle inequalities characterize real PSD completions of rank at most three. -/

import Mathlib.Logic.Equiv.Fin.Rotate
import D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! Real rank-three cycle completions and closed spherical polygon inequalities. -/

open scoped RealInnerProductSpace BigOperators
open Real Set

namespace D5.S3.QuadraticForms.CycleRankThreePsdCompletion

variable {I : Type*} [Fintype I] [DecidableEq I]

private def AngleConstraints (θ : I → ℝ) : Prop :=
  ∀ F : Finset I, Odd F.card →
    (∑ i ∈ F, θ i) - (∑ i ∈ Finset.univ \ F, θ i) ≤
      ((F.card : ℝ) - 1) * Real.pi

private noncomputable def cost (θ : I → ℝ) (F : Finset I) : ℝ :=
  ∑ i, if i ∈ F then Real.pi - θ i else θ i

private lemma cost_eq (θ : I → ℝ) (F : Finset I) :
    cost θ F = (F.card : ℝ) * Real.pi - (∑ i ∈ F, θ i) +
      (∑ i ∈ Finset.univ \ F, θ i) := by
  classical
  simp only [cost, Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h : Finset.univ.filter (fun i => i ∉ F) = Finset.univ \ F := by ext; simp
  rw [h, Finset.sum_sub_distrib]
  simp

private lemma constraints_iff (θ : I → ℝ) :
    AngleConstraints θ ↔ ∀ F : Finset I, Odd F.card → Real.pi ≤ cost θ F := by
  simp only [AngleConstraints, cost_eq]
  constructor <;> intro h F hF <;> have hh := h F hF <;> nlinarith

private lemma cost_nonneg (θ : I → ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ Real.pi)
    (F : Finset I) : 0 ≤ cost θ F := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> linarith [(hθ i).1, (hθ i).2]

private lemma cost_pair (θ : I → ℝ) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ Real.pi)
    (F G : Finset I) (hne : F ≠ G) : Real.pi ≤ cost θ F + cost θ G := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ F ↔ i ∈ G) := by
    by_contra h
    apply hne
    ext i
    exact Classical.not_not.mp (not_exists.mp h i)
  have hpos (j : I) : 0 ≤ (if j ∈ F then Real.pi - θ j else θ j) +
      (if j ∈ G then Real.pi - θ j else θ j) := by
    split_ifs <;> linarith [(hθ j).1, (hθ j).2]
  have h := Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
  have heq : (if i ∈ F then Real.pi - θ i else θ i) +
      (if i ∈ G then Real.pi - θ i else θ i) = Real.pi := by
    split_ifs at * <;> first | tauto | ring
  rw [heq] at h
  simpa only [cost, Finset.sum_add_distrib] using h

private lemma cost_option (θ : I → ℝ) (a : ℝ) (F : Finset I) (b : Bool) :
    cost (fun o => Option.elim o a θ) (if b then F.insertNone else F.map Function.Embedding.some) =
      (if b then Real.pi - a else a) + cost θ F := by
  cases b <;> simp [cost, Fintype.sum_option]

private lemma cost_erase (θ : I → ℝ) (a : ℝ) (F : Finset (Option I)) :
    cost (fun o => Option.elim o a θ) F =
      (if none ∈ F then Real.pi - a else a) + cost θ F.eraseNone := by
  simp [cost, Fintype.sum_option]

private theorem simultaneous_elimination
    (θ : I → ℝ) (a b : ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ Real.pi)
    (ha : 0 ≤ a ∧ a ≤ Real.pi) (hb : 0 ≤ b ∧ b ≤ Real.pi)
    (hfull : AngleConstraints (fun o : Option (Option I) =>
      o.elim a (fun p => p.elim b θ))) :
    ∃ γ : ℝ, (0 ≤ γ ∧ γ ≤ Real.pi) ∧
      |a - b| ≤ γ ∧ γ ≤ min (a + b) (2 * Real.pi - a - b) ∧
      AngleConstraints (fun o : Option I => o.elim γ θ) := by
  classical
  have hf := (constraints_iff _).mp hfull
  have h00 (S : Finset I) (hS : Odd S.card) :
      Real.pi ≤ a + b + cost θ S := by
    have hh := hf ((S.map Function.Embedding.some).map Function.Embedding.some)
      (by simpa using hS)
    have h1 := cost_option (fun p : Option I => p.elim b θ) a
      (S.map Function.Embedding.some) false
    have h2 := cost_option θ b S false
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    rw [h1, h2] at hh
    linarith
  have h11 (S : Finset I) (hS : Odd S.card) :
      Real.pi ≤ (Real.pi - a) + (Real.pi - b) + cost θ S := by
    have hh := hf (S.insertNone.insertNone) (by simpa [Nat.odd_add_one] using hS)
    have h1 := cost_option (fun p : Option I => p.elim b θ) a S.insertNone true
    have h2 := cost_option θ b S true
    simp only [↓reduceIte] at h1 h2
    rw [h1, h2] at hh
    linarith
  have h10 (S : Finset I) (hS : ¬ Odd S.card) : a - b ≤ cost θ S := by
    have hh := hf ((S.map Function.Embedding.some).insertNone)
      (by simpa [Nat.odd_add_one] using hS)
    have h1 := cost_option (fun p : Option I => p.elim b θ) a
      (S.map Function.Embedding.some) true
    have h2 := cost_option θ b S false
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    rw [h1, h2] at hh
    linarith
  have h01 (S : Finset I) (hS : ¬ Odd S.card) : b - a ≤ cost θ S := by
    have hh := hf (S.insertNone.map Function.Embedding.some)
      (by simpa [Nat.odd_add_one] using hS)
    have h1 := cost_option (fun p : Option I => p.elim b θ) a S.insertNone false
    have h2 := cost_option θ b S true
    simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
    rw [h1, h2] at hh
    linarith
  let L : Finset I → ℝ := fun S => if Odd S.card then Real.pi - cost θ S else 0
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty L
  have hLM (S : Finset I) : L S ≤ M := Finset.le_sup' L (Finset.mem_univ S)
  have hM (u : ℝ) (hu : ∀ S, L S ≤ u) : M ≤ u :=
    Finset.sup'_le Finset.univ_nonempty L (fun S _ => hu S)
  let γ := max |a - b| M
  have hγ0 : 0 ≤ γ := (abs_nonneg _).trans (le_max_left _ _)
  have hab : |a - b| ≤ a + b := abs_le.mpr ⟨by linarith [ha.1], by linarith [hb.1]⟩
  have hab' : |a - b| ≤ 2 * Real.pi - a - b :=
    abs_le.mpr ⟨by linarith [hb.2], by linarith [ha.2]⟩
  have habpi : |a - b| ≤ Real.pi := abs_le.mpr ⟨by linarith [ha.1, hb.2], by linarith [hb.1, ha.2]⟩
  have hγpi : γ ≤ Real.pi := by
    apply max_le habpi
    apply hM
    intro S
    dsimp [L]
    split_ifs <;> linarith [cost_nonneg θ hθ S, Real.pi_pos]
  have hγsum : γ ≤ a + b := by
    apply max_le hab
    apply hM
    intro S
    dsimp [L]
    split_ifs with hS
    · linarith [h00 S hS]
    · linarith [ha.1, hb.1]
  have hγsum' : γ ≤ 2 * Real.pi - a - b := by
    apply max_le hab'
    apply hM
    intro S
    dsimp [L]
    split_ifs with hS
    · linarith [h11 S hS]
    · linarith [ha.2, hb.2]
  have hlower (S : Finset I) (hS : Odd S.card) : Real.pi - cost θ S ≤ γ := by
    have hh := hLM S
    simp only [L, ite_eq_left hS] at hh
    exact hh.trans (le_max_right _ _)
  have hupper (S : Finset I) (hS : ¬ Odd S.card) : γ ≤ cost θ S := by
    apply max_le
    · exact abs_le.mpr ⟨by linarith [h01 S hS], h10 S hS⟩
    · apply hM
      intro T
      dsimp [L]
      split_ifs with hT
      · have hne : T ≠ S := by intro h; subst T; exact hS hT
        linarith [cost_pair θ hθ T S hne]
      · exact cost_nonneg θ hθ S
  refine ⟨γ, ⟨hγ0, hγpi⟩, le_max_left _ _, le_min hγsum hγsum', ?_⟩
  apply (constraints_iff _).mpr
  intro F hF
  rw [cost_erase]
  by_cases hn : none ∈ F
  · rw [ite_eq_left hn]
    have hc := Finset.card_eraseNone_of_mem hn
    have hS : ¬ Odd F.eraseNone.card := by
      rw [Nat.odd_iff] at hF ⊢
      omega
    linarith [hupper F.eraseNone hS]
  · rw [ite_eq_right hn]
    have hS : Odd F.eraseNone.card := by
      rwa [Finset.card_eraseNone_of_notMem hn]
    linarith [hlower F.eraseNone hS]


noncomputable section
private theorem cos_triangle_bounds {a b c : ℝ}
    (hb : b ∈ Icc 0 π)
    (hab : |a - c| ≤ b) (hadd : b ≤ a + c) (hper : a + b + c ≤ 2 * π) :
    cos (a + c) ≤ cos b ∧ cos b ≤ cos (a - c) := by
  constructor
  · by_cases h : a + c ≤ π
    · exact cos_le_cos_of_nonneg_of_le_pi hb.1 h hadd
    · rw [← cos_two_pi_sub (a + c)]
      exact cos_le_cos_of_nonneg_of_le_pi hb.1 (by linarith) (by linarith)
  · rw [← cos_abs (a - c)]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hb.2 hab
private theorem exists_triangle_parameter {a b c : ℝ}
    (hb : b ∈ Icc 0 π)
    (hab : |a - c| ≤ b) (hadd : b ≤ a + c) (hper : a + b + c ≤ 2 * π) :
    ∃ t : ℝ, cos a * cos c + sin a * sin c * cos t = cos b := by
  obtain ⟨hl, hu⟩ := cos_triangle_bounds hb hab hadd hper
  let f : ℝ → ℝ := fun t => cos a * cos c + sin a * sin c * cos t
  have hf : Continuous f := by fun_prop
  have hh : cos b ∈ Icc (f π) (f 0) := by
    simpa [f, cos_add, cos_sub] using And.intro hl hu
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' pi_pos.le hf.continuousOn hh
  exact ⟨t, he⟩
private def point (a t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![cos a, sin a * cos t, sin a * sin t]
private theorem point_inner_self (a t : ℝ) : ⟪point a t, point a t⟫ = 1 := by
  simp only [point, PiLp.inner_apply, Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    RCLike.inner_apply, conj_trivial]
  nlinarith [sin_sq_add_cos_sq a, sin_sq_add_cos_sq t]
private theorem point_inner (a c t : ℝ) :
    ⟪point c 0, point a t⟫ = cos a * cos c + sin a * sin c * cos t := by
  simp [point, PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, mul_assoc]
private theorem triangle_exists {a b c : ℝ}
    (hb : b ∈ Icc 0 π)
    (hab : |a - c| ≤ b) (hadd : b ≤ a + c) (hper : a + b + c ≤ 2 * π) :
    ∃ x y z : EuclideanSpace ℝ (Fin 3),
      ⟪x, x⟫ = 1 ∧ ⟪y, y⟫ = 1 ∧ ⟪z, z⟫ = 1 ∧
      ⟪x, y⟫ = cos c ∧ ⟪x, z⟫ = cos a ∧ ⟪y, z⟫ = cos b := by
  obtain ⟨t, ht⟩ := exists_triangle_parameter hb hab hadd hper
  refine ⟨point 0 0, point c 0, point a t, point_inner_self _ _,
    point_inner_self _ _, point_inner_self _ _, ?_, ?_, ?_⟩
  · simp [point_inner]
  · simp [point_inner]
  · rw [point_inner, ht]
private theorem insert_triangle {a b c : ℝ}
    (hb : b ∈ Icc 0 π)
    (hab : |a - c| ≤ b) (hadd : b ≤ a + c) (hper : a + b + c ≤ 2 * π)
    (x y : EuclideanSpace ℝ (Fin 3))
    (hx : ⟪x, x⟫ = 1) (hy : ⟪y, y⟫ = 1) (hxy : ⟪x, y⟫ = cos c) :
    ∃ z : EuclideanSpace ℝ (Fin 3),
      ⟪z, z⟫ = 1 ∧ ⟪x, z⟫ = cos a ∧ ⟪z, y⟫ = cos b := by
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := triangle_exists hb hab hadd hper
  have hg : ∀ i j : Fin 2, ⟪(![u,v] i), (![u,v] j)⟫ = ⟪(![x,y] i), (![x,y] j)⟫ := by
    intro i j
    fin_cases i <;> fin_cases j
    · change ⟪u,u⟫ = ⟪x, x⟫
      rw [hu, hx]
    · change ⟪u,v⟫ = ⟪x, y⟫
      rw [huv, hxy]
    · change ⟪v,u⟫ = ⟪y, x⟫
      rw [real_inner_comm u v, real_inner_comm x y, huv, hxy]
    · change ⟪v,v⟫ = ⟪y, y⟫
      rw [hv, hy]
  obtain ⟨e,he⟩ :=
    D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion.exists_linearIsometryEquiv_of_inner_eq hg
  have he0 : e u = x := he 0
  have he1 : e v = y := he 1
  refine ⟨e w, ?_, ?_, ?_⟩
  · rw [e.inner_map_map, hw]
  · rw [← he0, e.inner_map_map, huw]
  · rw [← he1, e.inner_map_map, real_inner_comm, hvw]

private theorem constraints_equiv {J : Type*} [Fintype J] [DecidableEq J]
    (e : I ≃ J) (θ : J → ℝ) : AngleConstraints (θ ∘ e) ↔ AngleConstraints θ := by
  have cost_map (f : I → ℝ) (F : Finset J) :
      cost (f ∘ e.symm) F = cost f (F.map e.symm.toEmbedding) := by
    unfold cost
    apply Fintype.sum_equiv e.symm
    intro i
    simp
  rw [constraints_iff, constraints_iff]
  constructor
  · intro h F hF
    have hh := h (F.map e.symm.toEmbedding) (by simpa using hF)
    have hm := cost_map (θ ∘ e) F
    rw [← hm] at hh
    simpa [Function.comp_def] using hh
  · intro h F hF
    have hh := h (F.map e.toEmbedding) (by simpa using hF)
    have hm : cost θ (F.map e.toEmbedding) = cost (θ ∘ e) F := by
      unfold cost
      symm
      apply Fintype.sum_equiv e
      intro i
      simp
    rwa [hm] at hh

private theorem constraints_cons {n : ℕ} (a : ℝ) (θ : Fin n → ℝ) :
    AngleConstraints (Fin.cons a θ) ↔
      AngleConstraints (fun o : Option (Fin n) => o.elim a θ) := by
  have he : (fun o : Option (Fin n) => o.elim a θ) ∘ finSuccEquiv n = Fin.cons a θ := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← he]
  exact constraints_equiv (finSuccEquiv n) _

private theorem elimination_fin {n : ℕ} (θ : Fin (n + 2) → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ π) (hC : AngleConstraints θ) :
    ∃ γ : ℝ, (0 ≤ γ ∧ γ ≤ π) ∧ |θ 0 - θ 1| ≤ γ ∧
      γ ≤ min (θ 0 + θ 1) (2 * π - θ 0 - θ 1) ∧
      AngleConstraints (Fin.cons γ (fun i : Fin n => θ i.succ.succ)) := by
  have he : θ = Fin.cons (θ 0) (Fin.cons (θ 1) (fun i : Fin n => θ i.succ.succ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  rw [he, constraints_cons] at hC
  have hC' : AngleConstraints (fun o : Option (Option (Fin n)) =>
      o.elim (θ 0) (fun p => p.elim (θ 1) (fun i => θ i.succ.succ))) := by
    apply (constraints_equiv ((finSuccEquiv n).optionCongr) _).mp
    convert hC using 1
    funext o
    cases o with
    | none => rfl
    | some i =>
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  obtain ⟨γ,hγ,hab,hs,hred⟩ := simultaneous_elimination
    (fun i : Fin n => θ i.succ.succ) (θ 0) (θ 1)
    (fun i => hθ _) (hθ 0) (hθ 1) hC'
  exact ⟨γ,hγ,hab,hs,(constraints_cons _ _).mpr hred⟩

/-- A closed chain with one vector more than edges, keeping the ambient space fixed. -/
private def ClosedChain {n : ℕ} (θ : Fin n → ℝ) : Prop :=
  ∃ p : Fin (n + 1) → EuclideanSpace ℝ (Fin 3),
    (∀ i, ⟪p i, p i⟫ = 1) ∧ p 0 = p (Fin.last n) ∧
    ∀ i : Fin n, ⟪p i.castSucc, p i.succ⟫ = cos (θ i)

private theorem closed_chain_base_zero (θ : Fin 0 → ℝ) : ClosedChain θ := by
  refine ⟨fun _ => point 0 0, fun _ => point_inner_self _ _, rfl, ?_⟩
  exact fun i => Fin.elim0 i

private theorem closed_chain_base_one (θ : Fin 1 → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ π) (hC : AngleConstraints θ) : ClosedChain θ := by
  have hh := hC {0} (by simp)
  have hz : θ 0 = 0 := by
    simp at hh
    linarith [(hθ 0).1]
  refine ⟨fun _ => point 0 0, fun _ => point_inner_self _ _, rfl, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [hz, cos_zero, point_inner_self]

private theorem closed_chain_insert {n : ℕ} (θ : Fin (n + 2) → ℝ)
    (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ π) (γ : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ π)
    (hab : |θ 0 - θ 1| ≤ γ)
    (hs : γ ≤ min (θ 0 + θ 1) (2 * π - θ 0 - θ 1))
    (hred : ClosedChain (Fin.cons γ (fun i : Fin n => θ i.succ.succ))) :
    ClosedChain θ := by
  obtain ⟨p,hp,hclose,hedge⟩ := hred
  have hdiag : ⟪p 0, p 1⟫ = cos γ := hedge 0
  obtain ⟨z,hz,hxz,hzy⟩ := insert_triangle (a := θ 0) (c := γ) (hθ 1)
    (by rw [abs_le] at hab ⊢; constructor <;> linarith [hab.1,hab.2, (le_min_iff.mp hs).1])
    (by have := (le_min_iff.mp hs).1; rw [abs_le] at hab; linarith [hab.1])
    (by have := (le_min_iff.mp hs).2; linarith)
    (p 0) (p 1) (hp _) (hp _) hdiag
  let q : Fin (n + 3) → EuclideanSpace ℝ (Fin 3) :=
    Fin.cons (p 0) (Fin.cons z (fun i : Fin (n + 1) => p i.succ))
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp _
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact hz
      · exact hp _
  · simpa [q] using hclose
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hxz
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact hzy
      · simpa [q] using hedge k.succ

/-- Construct a unit polygon in one real three-dimensional space. -/
private theorem closed_chain_of_constraints : ∀ n : ℕ, ∀ θ : Fin n → ℝ,
    (∀ i, 0 ≤ θ i ∧ θ i ≤ π) → AngleConstraints θ → ClosedChain θ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro θ hθ hC
    rcases n with _ | n
    · exact closed_chain_base_zero θ
    rcases n with _ | n
    · exact closed_chain_base_one θ hθ hC
    obtain ⟨γ,hγ,hab,hs,hred⟩ := elimination_fin θ hθ hC
    apply closed_chain_insert θ hθ γ hγ hab hs
    apply ih (n + 1) (by omega) _ _ hred
    intro i
    refine Fin.cases hγ (fun j => hθ j.succ.succ) i

private theorem restore_option (θ : I → ℝ) (a b γ : ℝ)
    (hab : |a - b| ≤ γ) (hs : γ ≤ min (a + b) (2 * π - a - b))
    (hred : AngleConstraints (fun o : Option I => o.elim γ θ)) :
    AngleConstraints (fun o : Option (Option I) => o.elim a (fun p => p.elim b θ)) := by
  have hr := (constraints_iff _).mp hred
  have hl (S : Finset I) (hS : Odd S.card) : π ≤ γ + cost θ S := by
    have hh := hr (S.map Function.Embedding.some) (by simpa using hS)
    simpa [cost, Fintype.sum_option] using hh
  have hu (S : Finset I) (hS : ¬ Odd S.card) : γ ≤ cost θ S := by
    have hh := hr S.insertNone (by simpa [Nat.odd_add_one] using hS)
    have he := cost_option θ γ S true
    simp only [↓reduceIte] at he
    rw [he] at hh
    linarith
  apply (constraints_iff _).mpr
  intro F hF
  rw [cost_erase, cost_erase]
  have hc0 := Finset.card_eraseNone_of_mem (s := F)
  have hc0' := Finset.card_eraseNone_of_notMem (s := F)
  have hc1 := Finset.card_eraseNone_of_mem (s := F.eraseNone)
  have hc1' := Finset.card_eraseNone_of_notMem (s := F.eraseNone)
  have hab' := abs_le.mp hab
  have hs' := le_min_iff.mp hs
  by_cases h0 : none ∈ F <;> by_cases h1 : none ∈ F.eraseNone
  · rw [ite_eq_left h0, ite_eq_left h1]
    have hS : Odd F.eraseNone.eraseNone.card := by
      rw [Nat.odd_iff] at hF ⊢
      have hca := hc0 h0; have hcb := hc1 h1
      have hp := Finset.card_pos.mpr (show F.eraseNone.Nonempty from ⟨none,h1⟩)
      omega
    linarith [hl _ hS]
  · rw [ite_eq_left h0, ite_eq_right h1]
    have hS : ¬ Odd F.eraseNone.eraseNone.card := by
      rw [Nat.odd_iff] at hF ⊢
      have := hc0 h0; have := hc1' h1; omega
    linarith [hu _ hS]
  · rw [ite_eq_right h0, ite_eq_left h1]
    have hS : ¬ Odd F.eraseNone.eraseNone.card := by
      rw [Nat.odd_iff] at hF ⊢
      have := hc0' h0; have := hc1 h1; omega
    linarith [hu _ hS]
  · rw [ite_eq_right h0, ite_eq_right h1]
    have hS : Odd F.eraseNone.eraseNone.card := by
      rw [Nat.odd_iff] at hF ⊢
      have := hc0' h0; have := hc1' h1; omega
    linarith [hl _ hS]

private theorem restore_fin {n : ℕ} (θ : Fin (n + 2) → ℝ) (γ : ℝ)
    (hab : |θ 0 - θ 1| ≤ γ)
    (hs : γ ≤ min (θ 0 + θ 1) (2 * π - θ 0 - θ 1))
    (hred : AngleConstraints (Fin.cons γ (fun i : Fin n => θ i.succ.succ))) :
    AngleConstraints θ := by
  have hr := (constraints_cons _ _).mp hred
  have hfull := restore_option (fun i : Fin n => θ i.succ.succ) (θ 0) (θ 1) γ hab hs hr
  have hC : AngleConstraints (fun o : Option (Fin (n + 1)) =>
      o.elim (θ 0) (Fin.cons (θ 1) (fun i : Fin n => θ i.succ.succ))) := by
    have hh := (constraints_equiv ((finSuccEquiv n).optionCongr) _).mpr hfull
    convert hh using 1
    funext o
    cases o with
    | none => rfl
    | some i => refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hh := (constraints_cons _ _).mpr hC
  convert hh using 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j <;> rfl

open InnerProductGeometry
private theorem norm_one_of_self {x : EuclideanSpace ℝ (Fin 3)} (hx : ⟪x, x⟫ = 1) :
    ‖x‖ = 1 := by
  rw [real_inner_self_eq_norm_sq] at hx
  nlinarith [norm_nonneg x]
private theorem angle_of_cos {x y : EuclideanSpace ℝ (Fin 3)}
    (hx : ⟪x, x⟫ = 1) (hy : ⟪y, y⟫ = 1) {a : ℝ}
    (ha : 0 ≤ a ∧ a ≤ π) (hxy : ⟪x, y⟫ = cos a) : angle x y = a := by
  rw [angle, norm_one_of_self hx, norm_one_of_self hy, mul_one, div_one, hxy]
  exact arccos_cos ha.1 ha.2

private theorem constraints_of_closed_chain : ∀ n : ℕ, ∀ θ : Fin n → ℝ,
    (∀ i, 0 ≤ θ i ∧ θ i ≤ π) → ClosedChain θ → AngleConstraints θ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro θ hθ hp
    obtain ⟨p,hp,hclose,hedge⟩ := hp
    have he (i : Fin n) : angle (p i.castSucc) (p i.succ) = θ i :=
      angle_of_cos (hp _) (hp _) (hθ i) (hedge i)
    rcases n with _ | n
    · intro F hF
      have : F = ∅ := Subsingleton.elim _ _
      simp [this] at hF
    rcases n with _ | n
    · have hz : θ 0 = 0 := by
        have ha := he 0
        have hn : p (Fin.last 1) ≠ 0 := by
          intro hz
          have hh := hp (Fin.last 1)
          rw [hz] at hh
          norm_num at hh
        change angle (p 0) (p (Fin.last 1)) = θ 0 at ha
        rw [hclose, angle_self hn] at ha
        exact ha.symm
      intro F hF
      have hF' : F = {0} := by
        have hne : F.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero (by intro hh; simp [hh] at hF))
        obtain ⟨i,hi⟩ := hne
        have hi0 : i = 0 := Fin.ext (by omega)
        have hzero : 0 ∈ F := hi0 ▸ hi
        ext j
        have hj : j = 0 := Fin.ext (by omega)
        subst j
        simp [hzero]
      simp [hF', hz]
    let γ := angle (p 0) (p 2)
    have hγ : 0 ≤ γ ∧ γ ≤ π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
    have ha : angle (p 0) (p 1) = θ 0 := he 0
    have hb : angle (p 1) (p 2) = θ 1 := he 1
    have ht0 := angle_le_angle_add_angle (p 0) (p 1) (p 2)
    have ht1 := angle_le_angle_add_angle (p 0) (p 2) (p 1)
    have ht2 := angle_le_angle_add_angle (p 1) (p 0) (p 2)
    have ht3 := angle_le_angle_add_angle (p 0) (-(p 1)) (p 2)
    rw [angle_neg_right, angle_neg_left] at ht3
    rw [angle_comm (p 2) (p 1)] at ht1
    rw [angle_comm (p 1) (p 0)] at ht2
    rw [ha,hb] at ht0 ht1 ht2 ht3
    have hab : |θ 0 - θ 1| ≤ γ := abs_le.mpr ⟨by linarith, by linarith⟩
    have hs : γ ≤ min (θ 0 + θ 1) (2 * π - θ 0 - θ 1) :=
      le_min (by exact ht0) (by linarith)
    apply restore_fin θ γ hab hs
    apply ih (n + 1) (by omega) _
      (fun i => Fin.cases hγ (fun j => hθ j.succ.succ) i)
    let q : Fin (n + 2) → EuclideanSpace ℝ (Fin 3) :=
      Fin.cons (p 0) (fun i : Fin (n + 1) => p i.succ.succ)
    refine ⟨q, ?_, ?_, ?_⟩
    · intro i
      exact Fin.cases (hp 0) (fun j => hp j.succ.succ) i
    · simpa [q] using hclose
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change ⟪p 0, p 2⟫ = cos γ
        exact inner_eq_cos_angle_of_norm_eq_one (norm_one_of_self (hp _))
          (norm_one_of_self (hp _))
      · simpa [q] using hedge j.succ.succ

private theorem cycle_of_closed_chain {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (h : ClosedChain θ) :
    ∃ p : Fin (n + 1) → EuclideanSpace ℝ (Fin 3),
      (∀ i, ⟪p i, p i⟫ = 1) ∧ ∀ i, ⟪p i, p (finRotate (n + 1) i)⟫ = cos (θ i) := by
  obtain ⟨p,hp,hclose,hedge⟩ := h
  let q : Fin (n + 1) → EuclideanSpace ℝ (Fin 3) := fun i => p i.castSucc
  have hn (i : Fin (n + 1)) : q (finRotate (n + 1) i) = p i.succ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [q] using hclose
    · have hr : finRotate (n + 1) j.castSucc = j.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last j)]
        rfl
      simp only [q, hr, Fin.succ_castSucc]
  exact ⟨q, fun i => hp _, fun i => by rw [hn]; exact hedge i⟩

private theorem closed_chain_of_cycle {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (p : Fin (n + 1) → EuclideanSpace ℝ (Fin 3))
    (hp : ∀ i, ⟪p i, p i⟫ = 1)
    (he : ∀ i, ⟪p i, p (finRotate (n + 1) i)⟫ = cos (θ i)) : ClosedChain θ := by
  let q : Fin (n + 2) → EuclideanSpace ℝ (Fin 3) := Fin.snoc p (p 0)
  have hn (i : Fin (n + 1)) : q i.succ = p (finRotate (n + 1) i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [q]
    · have hr : finRotate (n + 1) j.castSucc = j.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last j)]
        rfl
      simp only [hr, Fin.succ_castSucc, q, Fin.snoc_castSucc]
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i
    exact Fin.lastCases (by simpa [q] using hp 0) (fun j => by simpa [q] using hp j) i
  · simp [q]
  · intro i
    rw [hn]
    simpa [q] using he i

/-- The exact closed - interval cycle completion criterion, with a uniform rank - three bound. -/
theorem cycle_rank_three_iff {n : ℕ} (hn : 3 ≤ n) (a : Fin n → ℝ)
    (ha : ∀ i, -1 ≤ a i ∧ a i ≤ 1) :
    (∃ B : Matrix (Fin n) (Fin n) ℝ,
      B.PosSemidef ∧ B.rank ≤ 3 ∧ (∀ i, B i i = 1) ∧
        ∀ i, B i (finRotate n i) = a i) ↔
    ∀ F : Finset (Fin n), Odd F.card →
      (∑ i ∈ F, arccos (a i)) - (∑ i ∈ Finset.univ \ F, arccos (a i)) ≤
        ((F.card : ℝ) - 1) * π := by
  have hθ (i : Fin n) : 0 ≤ arccos (a i) ∧ arccos (a i) ≤ π :=
    ⟨arccos_nonneg _, arccos_le_pi _⟩
  cases n with
  | zero => omega
  | succ n =>
    constructor
    · rintro ⟨B,hB,hr,hd,he⟩
      obtain ⟨p,hp⟩ :=
        D5.S3.QuadraticForms.RankBoundedChordalPsdCompletion.gram_factor_rank (V := Fin (n + 1)) 3 B hB
          (by simpa only [Matrix.rank_eq_finrank_span_cols] using hr)
      have hc : ClosedChain (fun i => arccos (a i)) :=
        closed_chain_of_cycle _ p (fun i => (hp i i).trans (hd i))
          (fun i => by rw [hp,he,cos_arccos (ha i).1 (ha i).2])
      exact constraints_of_closed_chain _ _ hθ hc
    · intro hC
      obtain ⟨p,hp,he⟩ := cycle_of_closed_chain _ (closed_chain_of_constraints _ _ hθ hC)
      let X : Matrix (Fin 3) (Fin (n + 1)) ℝ := fun k i => p i k
      have hg : Matrix.gram ℝ p = X.conjTranspose * X := by
        ext i j
        change ⟪p i, p j⟫ = ∑ k, star (X k i) * X k j
        simp [PiLp.inner_apply, X, mul_comm]
      refine ⟨Matrix.gram ℝ p, Matrix.posSemidef_gram ℝ p, ?_, hp, ?_⟩
      · rw [hg, Matrix.rank_conjTranspose_mul_self]
        simpa using X.rank_le_card_height
      · intro i
        exact (he i).trans (cos_arccos (ha i).1 (ha i).2)

end
end D5.S3.QuadraticForms.CycleRankThreePsdCompletion
