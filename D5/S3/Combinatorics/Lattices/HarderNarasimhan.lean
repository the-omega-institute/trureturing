/- GID: D5/S3/Combinatorics/Lattices/HarderNarasimhan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/HarderNarasimhan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite rank yields canonical HN filtrations and attained extreme slopes. -/

import Mathlib.Basic.Real.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic

/-! Finite-length slope theory on intervals of a ranked lattice.
The extremum construction uses rank induction, without finiteness of the set of elements.
The mathematical context is the classical Harder--Narasimhan theory of lattices.
Structural witness: `supermodular_max` constructs a global optimizer by two nested
rank inductions; `slope_max` then constructs slope attainment on a proper interval.
Neither existence statement is an assumption or an instance of an upstream optimizer.
Further witnesses: `first_destabilizer` recovers global containment from local
semistability and strict descent; `last_bounds` uncrosses a quotient along the chain.
They are used in uniqueness and the extreme-slope characterizations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Lattices.HarderNarasimhan

universe u

/-- A strictly ranked lattice with a modular rank and a supermodular real degree. -/
structure SlopeData (Λ : Type u) [Lattice Λ] where
  rank : Λ → ℤ
  rank_strictMono : StrictMono rank
  rank_modular : ∀ x y, rank (x ⊔ y) + rank (x ⊓ y) = rank x + rank y
  degree : Λ → ℝ
  degree_supermodular : ∀ x y, degree x + degree y ≤ degree (x ⊔ y) + degree (x ⊓ y)

variable {Λ : Type u} [Lattice Λ]

/-- The slope of the quotient interval, with Lean's zero-denominator convention. -/
def SlopeData.slope (D : SlopeData Λ) (a b : Λ) : ℝ :=
  (D.degree b - D.degree a) / ((D.rank b : ℝ) - D.rank a)

/-- A maximal-slope element containing every other maximal-slope element. -/
def SlopeData.Destabilizer (D : SlopeData Λ) (a b e : Λ) : Prop :=
  a < e ∧ e ≤ b ∧
  (∀ x, a < x → x ≤ b → D.slope a x ≤ D.slope a e) ∧
  (∀ x, a < x → x ≤ b → D.slope a x = D.slope a e → x ≤ e)

private theorem real_rank_modular (D : SlopeData Λ) (x y : Λ) :
    (D.rank (x ⊔ y) : ℝ) + D.rank (x ⊓ y) = D.rank x + D.rank y := by
  exact_mod_cast D.rank_modular x y

private theorem rank_pos (D : SlopeData Λ) {a b : Λ} (h : a < b) :
    0 < (D.rank b : ℝ) - D.rank a := by
  have := D.rank_strictMono h
  exact sub_pos.mpr (by exact_mod_cast this)

/-- Supermodular optimization requires finite height, not a finite underlying lattice. -/
private theorem supermodular_max (r : Λ → ℤ) (hr : StrictMono r) (f : Λ → ℝ)
    (hf : ∀ x y, f x + f y ≤ f (x ⊔ y) + f (x ⊓ y))
    (a b : Λ) (hab : a ≤ b) :
    ∃ e, a ≤ e ∧ e ≤ b ∧ ∀ x, a ≤ x → x ≤ b → f x ≤ f e := by
  classical
  generalize hn : (r b - r a).toNat = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hc : ∃ c, a ≤ c ∧ c ≤ b ∧ f a < f c ∧ f b < f c
    · obtain ⟨c, hac, hcb, hfc, hbc⟩ := hc
      have hcb' : c < b := lt_of_le_of_ne hcb (by rintro rfl; exact hbc.false)
      have hrc := hr hcb'
      have hra := hr.monotone hac
      obtain ⟨d, had, hdc, hd⟩ := ih ((r c - r a).toNat) (by omega) a c hac rfl
      have hfd : f a < f d := hfc.trans_le (hd c hac le_rfl)
      have had' : a < d := lt_of_le_of_ne had (by rintro rfl; exact hfd.false)
      have hrd := hr had'
      have hdb : d ≤ b := hdc.trans hcb
      have hrdb := hr.monotone hdb
      obtain ⟨e, hde, heb, he⟩ := ih ((r b - r d).toNat) (by omega) d b hdb rfl
      refine ⟨e, had.trans hde, heb, ?_⟩
      intro x hax hxb
      have hmeet := hd (x ⊓ d) (le_inf hax had) (inf_le_right.trans hdc)
      have hjoin := he (x ⊔ d) le_sup_right (sup_le hxb hdb)
      linarith [hf x d]
    · by_cases hfba : f b ≤ f a
      · refine ⟨a, le_rfl, hab, ?_⟩
        intro x hax hxb
        by_contra hx
        exact hc ⟨x, hax, hxb, lt_of_not_ge hx, hfba.trans_lt (lt_of_not_ge hx)⟩
      · refine ⟨b, hab, le_rfl, ?_⟩
        intro x hax hxb
        by_contra hx
        exact hc ⟨x, hax, hxb,
          (le_of_not_ge hfba).trans_lt (lt_of_not_ge hx), lt_of_not_ge hx⟩

private theorem slope_max (D : SlopeData Λ) (a b : Λ) (hab : a < b) :
    ∃ e, a < e ∧ e ≤ b ∧
      ∀ x, a ≤ x → x ≤ b →
        D.degree x - D.degree a ≤ D.slope a e * ((D.rank x : ℝ) - D.rank a) := by
  classical
  generalize hn : (D.rank b - D.rank a).toNat = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    let t := D.slope a b
    let f := fun x => D.degree x - D.degree a - t * ((D.rank x : ℝ) - D.rank a)
    have hf : ∀ x y, f x + f y ≤ f (x ⊔ y) + f (x ⊓ y) := by
      intro x y
      dsimp [f]
      have := D.degree_supermodular x y
      have hr := congrArg (fun z : ℝ => t * z) (real_rank_modular D x y)
      simp only [mul_add] at hr
      nlinarith
    have hfa : f a = 0 := by simp [f]
    have hfb : f b = 0 := by
      dsimp [f, t, SlopeData.slope]
      rw [div_mul_cancel₀ _ (ne_of_gt (rank_pos D hab))]
      ring
    by_cases h : ∀ x, a ≤ x → x ≤ b → f x ≤ 0
    · refine ⟨b, hab, le_rfl, ?_⟩
      intro x hax hxb
      have := h x hax hxb
      dsimp [f, t] at this
      linarith
    · push Not at h
      obtain ⟨c, hac, hcb, hc⟩ := h
      obtain ⟨d, had, hdb, hd⟩ :=
        supermodular_max D.rank D.rank_strictMono f hf a b hab.le
      have hfd : 0 < f d := hc.trans_le (hd c hac hcb)
      have had' : a < d := lt_of_le_of_ne had (by rintro rfl; simpa [hfa] using hfd)
      have hdb' : d < b := lt_of_le_of_ne hdb (by rintro rfl; simpa [hfb] using hfd)
      have hrd := D.rank_strictMono hdb'
      have hra := D.rank_strictMono.monotone had
      obtain ⟨e, hae, hed, he⟩ := ih ((D.rank d - D.rank a).toNat) (by omega) a d had' rfl
      have hre := rank_pos D hae
      have hrd' := rank_pos D had'
      have hse : t < D.slope a e := by
        have h := he d had le_rfl
        dsimp [f] at hfd
        nlinarith
      refine ⟨e, hae, hed.trans hdb, ?_⟩
      intro x hax hxb
      have hm := he (x ⊓ d) (le_inf hax had) inf_le_right
      have hrm : (D.rank (x ⊓ d) : ℝ) ≤ D.rank x := by
        exact_mod_cast D.rank_strictMono.monotone (inf_le_left : x ⊓ d ≤ x)
      have hfx : f x - f (x ⊓ d) ≤ 0 := by
        have hj := hd (x ⊔ d) (hax.trans le_sup_left) (sup_le hxb hdb)
        linarith [hf x d]
      dsimp [f] at hfx
      have hprod := mul_nonneg (sub_nonneg.mpr hse.le)
        (sub_nonneg.mpr hrm)
      nlinarith

private theorem slope_bound (D : SlopeData Λ) {a b : Λ} (hab : a < b) (t : ℝ) :
    D.slope a b ≤ t ↔ D.degree b - D.degree a ≤ t * ((D.rank b : ℝ) - D.rank a) := by
  exact div_le_iff₀ (rank_pos D hab)

private theorem maximal_rank (D : SlopeData Λ) (a b : Λ) (P : Λ → Prop)
    (hP : ∃ x, a ≤ x ∧ x ≤ b ∧ P x) :
    ∃ e, a ≤ e ∧ e ≤ b ∧ P e ∧
      ∀ x, a ≤ x → x ≤ b → P x → D.rank x ≤ D.rank e := by
  classical
  let S := (Finset.Icc (D.rank a) (D.rank b)).filter
    (fun n => ∃ x, a ≤ x ∧ x ≤ b ∧ P x ∧ D.rank x = n)
  have hS : S.Nonempty := by
    obtain ⟨x, hax, hxb, hx⟩ := hP
    refine ⟨D.rank x, Finset.mem_filter.mpr ⟨?_, x, hax, hxb, hx, rfl⟩⟩
    exact Finset.mem_Icc.mpr
      ⟨D.rank_strictMono.monotone hax, D.rank_strictMono.monotone hxb⟩
  obtain ⟨e, hae, heb, he, her⟩ := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  refine ⟨e, hae, heb, he, ?_⟩
  intro x hax hxb hx
  rw [her]
  apply Finset.le_max'
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨D.rank_strictMono.monotone hax, D.rank_strictMono.monotone hxb⟩,
    x, hax, hxb, hx, rfl⟩

/-- Every nontrivial interval has a unique largest maximal-slope element.
No degree boundedness, discreteness, finiteness of the lattice, or bottom normalization is
assumed. Rank induction supplies attainment; supermodularity supplies containment.
-/
theorem exists_unique_destabilizer (D : SlopeData Λ) (a b : Λ) :
    (∃! e, D.Destabilizer a b e) ↔ a < b := by
  constructor
  · rintro ⟨e, he, _⟩
    exact he.1.trans_le he.2.1
  · intro hab
    obtain ⟨c, hac, hcb, hc⟩ := slope_max D a b hab
    let t := D.slope a c
    have ht : ∀ x, a ≤ x → x ≤ b →
        D.degree x - D.degree a ≤ t * ((D.rank x : ℝ) - D.rank a) := hc
    obtain ⟨e, hae, heb, ⟨hae', he⟩, hmax⟩ := maximal_rank D a b
      (fun x => a < x ∧ D.slope a x = t) ⟨c, hac.le, hcb, hac, rfl⟩
    have contain : ∀ x, a ≤ x → x ≤ b → D.slope a x = t → x ≤ e := by
      intro x hax hxb hx
      by_cases hxa : x = a
      · simpa [hxa] using hae
      have hax' : a < x := lt_of_le_of_ne hax (Ne.symm hxa)
      have hxdeg : D.degree x - D.degree a = t * ((D.rank x : ℝ) - D.rank a) := by
        exact (div_eq_iff (ne_of_gt (rank_pos D hax'))).mp hx
      have hedeg : D.degree e - D.degree a = t * ((D.rank e : ℝ) - D.rank a) := by
        exact (div_eq_iff (ne_of_gt (rank_pos D hae'))).mp he
      have hjb : x ⊔ e ≤ b := sup_le hxb heb
      have hja : a < x ⊔ e := hae'.trans_le le_sup_right
      have hm := ht (x ⊓ e) (le_inf hax hae) (inf_le_left.trans hxb)
      have hj := ht (x ⊔ e) hja.le hjb
      have hjeq : D.slope a (x ⊔ e) = t := by
        apply (div_eq_iff (ne_of_gt (rank_pos D hja))).mpr
        have hr := congrArg (fun z : ℝ => t * z) (real_rank_modular D x e)
        simp only [mul_add] at hr
        have := D.degree_supermodular x e
        nlinarith
      have hr := hmax (x ⊔ e) hja.le hjb ⟨hja, hjeq⟩
      by_contra hxe
      have hlt : e < x ⊔ e := lt_of_le_of_ne le_sup_right
        (by intro h; exact hxe (h ▸ le_sup_left))
      exact (not_lt_of_ge hr) (D.rank_strictMono hlt)
    have hemax : ∀ x, a < x → x ≤ b → D.slope a x ≤ D.slope a e := by
      intro x hax hxb
      rw [he]
      exact (slope_bound D hax t).mpr (ht x hax.le hxb)
    refine ⟨e, ⟨hae', heb, hemax, ?_⟩, ?_⟩
    · intro x hax hxb hx
      exact contain x hax.le hxb (hx.trans he)
    · intro y hy
      apply (le_antisymm ?_ ?_).symm
      · exact hy.2.2.2 e hae' heb (le_antisymm (hy.2.2.1 e hae' heb)
          (hemax y hy.1 hy.2.1))
      · exact contain y hy.1.le hy.2.1
          ((le_antisymm (hemax y hy.1 hy.2.1) (hy.2.2.1 e hae' heb)).trans he)

/-- Semistability of a nontrivial quotient interval. -/
def SlopeData.Semistable (D : SlopeData Λ) (a b : Λ) : Prop :=
  a < b ∧ ∀ x, a < x → x ≤ b → D.slope a x ≤ D.slope a b

/-- The first slope of a list lies strictly below a specified threshold. -/
def SlopeData.StartsBelow (D : SlopeData Λ) (a : Λ) (t : ℝ) : List Λ → Prop
  | [] => True
  | e :: _ => D.slope a e < t

/-- A genuine HN filtration: semistable factors and strictly decreasing slopes.
No maximality condition is built into this definition. -/
inductive SlopeData.Filtration (D : SlopeData Λ) : Λ → Λ → List Λ → Prop
  | nil (a : Λ) : D.Filtration a a []
  | cons {a e b : Λ} {l : List Λ} (hae : D.Semistable a e) (heb : e ≤ b)
      (tail : D.Filtration e b l) (drop : D.StartsBelow e (D.slope a e) l) :
      D.Filtration a b (e :: l)

private theorem slope_identity (D : SlopeData Λ) {a b : Λ} (h : a < b) :
    D.degree b - D.degree a = D.slope a b * ((D.rank b : ℝ) - D.rank a) := by
  exact (div_mul_cancel₀ _ (ne_of_gt (rank_pos D h))).symm

private theorem quotient_drop (D : SlopeData Λ) {a e b : Λ}
    (he : D.Destabilizer a b e) {x : Λ} (hex : e < x) (hxb : x ≤ b) :
    D.slope e x < D.slope a e := by
  have hax := he.1.trans hex
  have hx := (div_le_iff₀ (rank_pos D hax)).mp (he.2.2.1 x hax hxb)
  have hid := slope_identity D he.1
  by_contra h
  have hq := (le_div_iff₀ (rank_pos D hex)).mp (le_of_not_gt h)
  have heq : D.slope a x = D.slope a e := by
    apply (div_eq_iff (ne_of_gt (rank_pos D hax))).mpr
    nlinarith
  exact hex.not_ge (he.2.2.2 x hax hxb heq)

/-- Uncrossing shows that the first factor of any HN chain is maximal destabilizing. -/
private theorem first_destabilizer (D : SlopeData Λ) {a b e : Λ} {l : List Λ}
    (h : D.Filtration a b (e :: l)) : D.Destabilizer a b e := by
  induction l generalizing a e with
  | nil =>
    cases h with
    | cons hs heb tail hdrop =>
      cases tail
      exact ⟨hs.1, le_rfl, hs.2, fun x _ hx _ => hx⟩
  | cons c l ih =>
    cases h with
    | cons hs heb tail hdrop =>
      have hc := ih tail
      change D.slope e c < D.slope a e at hdrop
      let t := D.slope a e
      have hgap := rank_pos D hs.1
      have hedeg := slope_identity D hs.1
      have hmod (x : Λ) :
          t * ((D.rank (x ⊔ e) : ℝ) + D.rank (x ⊓ e)) =
            t * ((D.rank x : ℝ) + D.rank e) := by
        congr 1
        exact_mod_cast D.rank_modular x e
      have meet_bound (x : Λ) (hax : a ≤ x) :
          D.degree (x ⊓ e) - D.degree a ≤
            t * ((D.rank (x ⊓ e) : ℝ) - D.rank a) := by
        have ham : a ≤ x ⊓ e := le_inf hax hs.1.le
        rcases ham.eq_or_lt with hm | hm
        · rw [← hm]; simp
        · exact (div_le_iff₀ (rank_pos D hm)).mp (hs.2 _ hm inf_le_right)
      have join_bound (x : Λ) (hxb : x ≤ b) :
          D.degree (x ⊔ e) - D.degree e ≤
            t * ((D.rank (x ⊔ e) : ℝ) - D.rank e) := by
        rcases (le_sup_right : e ≤ x ⊔ e).eq_or_lt with hj | hj
        · rw [← hj]; simp
        · have hcj := hc.2.2.1 (x ⊔ e) hj (sup_le hxb heb)
          have hlt : D.slope e (x ⊔ e) < t := hcj.trans_lt hdrop
          exact ((div_lt_iff₀ (rank_pos D hj)).mp hlt).le
      have bound (x : Λ) (hax : a < x) (hxb : x ≤ b) : D.slope a x ≤ t := by
        apply (div_le_iff₀ (rank_pos D hax)).mpr
        have hm := meet_bound x hax.le
        have hj := join_bound x hxb
        have hr := hmod x
        have hd := D.degree_supermodular x e
        nlinarith
      refine ⟨hs.1, heb, bound, ?_⟩
      intro x hax hxb hx
      by_contra hxe
      have hj : e < x ⊔ e := lt_of_le_of_ne le_sup_right
        (by intro hj; exact hxe (hj ▸ le_sup_left))
      have hcj := hc.2.2.1 (x ⊔ e) hj (sup_le hxb heb)
      have hlt := (div_lt_iff₀ (rank_pos D hj)).mp (hcj.trans_lt hdrop)
      have hxdeg := (div_eq_iff (ne_of_gt (rank_pos D hax))).mp hx
      have hm := meet_bound x hax.le
      have hr := hmod x
      have hd := D.degree_supermodular x e
      nlinarith

private theorem filtration_exists (D : SlopeData Λ) (a b : Λ) (hab : a ≤ b) :
    ∃ l, D.Filtration a b l := by
  generalize hn : (D.rank b - D.rank a).toNat = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    rcases hab.eq_or_lt with rfl | hab
    · exact ⟨[], .nil a⟩
    · obtain ⟨e, he, _⟩ := (exists_unique_destabilizer D a b).mpr hab
      have hr := D.rank_strictMono he.1
      have hrb := D.rank_strictMono.monotone he.2.1
      obtain ⟨l, hl⟩ := ih ((D.rank b - D.rank e).toNat) (by omega) e b he.2.1 rfl
      refine ⟨e :: l, .cons ⟨he.1, fun x hx hxe =>
        he.2.2.1 x hx (hxe.trans he.2.1)⟩ he.2.1 hl ?_⟩
      cases l with
      | nil => trivial
      | cons c l =>
        have hc := first_destabilizer D hl
        exact quotient_drop D he hc.1 hc.2.1

private theorem filtration_unique (D : SlopeData Λ) {a b : Λ} {l m : List Λ}
    (hl : D.Filtration a b l) (hm : D.Filtration a b m) : l = m := by
  induction hl generalizing m with
  | nil a =>
    cases hm with
    | nil => rfl
    | cons hs heb _ _ => exact (hs.1.not_ge heb).elim
  | @cons a e b l hs heb tail drop ih =>
    cases m with
    | nil =>
      cases hm
      exact (hs.1.not_ge heb).elim
    | cons c m =>
      have he := first_destabilizer D (.cons hs heb tail drop)
      have hc := first_destabilizer D hm
      have hec : e = c :=
        ((exists_unique_destabilizer D a b).mpr (hs.1.trans_le heb)).unique he hc
      subst c
      cases hm with
      | cons _ _ htail _ => exact congrArg (List.cons e) (ih htail)

/-- Every interval has exactly one semistable filtration with strictly descending slopes.
The empty interval has the empty filtration. Uniqueness covers all filtrations satisfying
semistability and strict descent, not only those produced by the construction.
-/
theorem exists_unique_filtration (D : SlopeData Λ) (a b : Λ) :
    (∃! l, D.Filtration a b l) ↔ a ≤ b := by
  constructor
  · rintro ⟨l, hl, _⟩
    cases hl with
    | nil => exact le_rfl
    | cons hs heb _ _ => exact hs.1.le.trans heb
  · intro hab
    obtain ⟨l, hl⟩ := filtration_exists D a b hab
    exact ⟨l, hl, fun m hm => filtration_unique D hm hl⟩

/-- The lower endpoint of the last factor of a nonempty endpoint list. -/
def lastLower (a : Λ) : List Λ → Λ
  | [] => a
  | [_] => a
  | e :: c :: l => lastLower e (c :: l)

/-- The largest slope of nonzero subobjects in an interval. -/
def SlopeData.muMax (D : SlopeData Λ) (a b : Λ) : ℝ :=
  sSup {s | ∃ x, a < x ∧ x ≤ b ∧ D.slope a x = s}

/-- The smallest slope of nonzero quotient objects in an interval. -/
def SlopeData.muMin (D : SlopeData Λ) (a b : Λ) : ℝ :=
  sInf {s | ∃ x, a ≤ x ∧ x < b ∧ D.slope x b = s}

private theorem last_bounds (D : SlopeData Λ) {a b e : Λ} {l : List Λ}
    (h : D.Filtration a b (e :: l)) :
    let q := lastLower a (e :: l)
    a ≤ q ∧ q < b ∧ D.slope q b ≤ D.slope a e ∧
      ∀ x, a ≤ x → x < b → D.slope q b ≤ D.slope x b := by
  induction l generalizing a e with
  | nil =>
    cases h with
    | cons hs heb tail hdrop =>
      cases tail
      refine ⟨le_rfl, hs.1, le_rfl, ?_⟩
      intro x hax hxb
      change D.slope a b ≤ D.slope x b
      apply (le_div_iff₀ (rank_pos D hxb)).mpr
      have he := slope_identity D hs.1
      rcases hax.eq_or_lt with rfl | hax
      · exact he.ge
      · have hx := (div_le_iff₀ (rank_pos D hax)).mp (hs.2 x hax hxb.le)
        nlinarith
  | cons c l ih =>
    cases h with
    | cons hs heb tail hdrop =>
      obtain ⟨heq, hqb, hqc, hq⟩ := ih tail
      change D.slope e c < D.slope a e at hdrop
      let q := lastLower e (c :: l)
      change e ≤ q at heq
      change q < b at hqb
      change D.slope q b ≤ D.slope e c at hqc
      change ∀ x, e ≤ x → x < b → D.slope q b ≤ D.slope x b at hq
      change a ≤ q ∧ q < b ∧ D.slope q b ≤ D.slope a e ∧ _
      have hqt : D.slope q b ≤ D.slope a e := hqc.trans hdrop.le
      refine ⟨hs.1.le.trans heq, hqb, hqt, ?_⟩
      intro x hax hxb
      apply (le_div_iff₀ (rank_pos D hxb)).mpr
      let t := D.slope q b
      have he := slope_identity D hs.1
      have hm : t * ((D.rank e : ℝ) - D.rank (x ⊓ e)) ≤
          D.degree e - D.degree (x ⊓ e) := by
        have hma : a ≤ x ⊓ e := le_inf hax hs.1.le
        have hrm : (D.rank (x ⊓ e) : ℝ) ≤ D.rank e := by
          exact_mod_cast D.rank_strictMono.monotone (inf_le_right : x ⊓ e ≤ e)
        have hprod := mul_nonneg (sub_nonneg.mpr hqt) (sub_nonneg.mpr hrm)
        rcases hma.eq_or_lt with hm | hm
        · rw [← hm]
          rw [← hm] at hprod
          dsimp [t]
          nlinarith
        · have hx := (div_le_iff₀ (rank_pos D hm)).mp (hs.2 _ hm inf_le_right)
          nlinarith
      have hj : t * ((D.rank b : ℝ) - D.rank (x ⊔ e)) ≤
          D.degree b - D.degree (x ⊔ e) := by
        have hjb : x ⊔ e ≤ b := sup_le hxb.le heb
        rcases hjb.eq_or_lt with hj | hj
        · rw [hj]; simp
        · exact (le_div_iff₀ (rank_pos D hj)).mp (hq _ le_sup_right hj)
      have hr := congrArg (fun z : ℝ => t * z)
        (show (D.rank (x ⊔ e) : ℝ) + D.rank (x ⊓ e) = D.rank x + D.rank e by
          exact_mod_cast D.rank_modular x e)
      have hd := D.degree_supermodular x e
      change t * ((D.rank b : ℝ) - D.rank x) ≤ D.degree b - D.degree x
      nlinarith

/-- The first and last HN slopes are attained extrema of all subobject and quotient
slopes, respectively. In particular, the suprema and infima in their definitions are
finite real extrema, with witnesses given by the filtration itself. The first endpoint
is the full destabilizer. Semistability is equivalent to a single factor and to equality
of the extreme slopes; otherwise the first slope is strictly larger than the last. -/
theorem filtration_extremes (D : SlopeData Λ) (a b e : Λ) (l : List Λ)
    (h : D.Filtration a b (e :: l)) :
    let q := lastLower a (e :: l)
    a ≤ q ∧ q < b ∧
      IsGreatest {s | ∃ x, a < x ∧ x ≤ b ∧ D.slope a x = s} (D.slope a e) ∧
      IsLeast {s | ∃ x, a ≤ x ∧ x < b ∧ D.slope x b = s} (D.slope q b) ∧
      D.muMax a b = D.slope a e ∧ D.muMin a b = D.slope q b ∧
      D.Destabilizer a b e ∧ D.slope q b ≤ D.slope a e ∧
      (D.Semistable a b ↔ l = []) ∧
      (D.muMin a b = D.muMax a b ↔ D.Semistable a b) ∧
      (l ≠ [] → D.slope q b < D.slope a e) := by
  have he := first_destabilizer D h
  obtain ⟨haq, hqb, hcompare, hq⟩ := last_bounds D h
  let q := lastLower a (e :: l)
  have hmax : IsGreatest {s | ∃ x, a < x ∧ x ≤ b ∧ D.slope a x = s}
      (D.slope a e) := by
    refine ⟨⟨e, he.1, he.2.1, rfl⟩, ?_⟩
    rintro s ⟨x, hax, hxb, rfl⟩
    exact he.2.2.1 x hax hxb
  have hmin : IsLeast {s | ∃ x, a ≤ x ∧ x < b ∧ D.slope x b = s}
      (D.slope q b) := by
    refine ⟨⟨q, haq, hqb, rfl⟩, ?_⟩
    rintro s ⟨x, hax, hxb, rfl⟩
    exact hq x hax hxb
  have hstrict : l ≠ [] → D.slope q b < D.slope a e := by
    intro hne
    cases l with
    | nil => exact (hne rfl).elim
    | cons c l =>
      cases h with
      | cons hs heb tail drop =>
        have hlast := (last_bounds D tail).2.2.1
        exact hlast.trans_lt drop
  have hsem : D.Semistable a b ↔ l = [] := by
    constructor
    · intro hs
      have single : D.Filtration a b [b] := .cons hs le_rfl (.nil b) trivial
      exact (List.cons.inj (filtration_unique D h single)).2
    · rintro rfl
      cases h with
      | cons hs heb tail drop =>
        cases tail
        exact hs
  have hequal : D.muMin a b = D.muMax a b ↔ D.Semistable a b := by
    constructor
    · intro heq
      apply hsem.mpr
      by_contra hne
      rw [SlopeData.muMin, SlopeData.muMax, hmin.csInf_eq, hmax.csSup_eq] at heq
      exact (ne_of_lt (hstrict hne)) heq
    · intro hs
      have hl := hsem.mp hs
      subst l
      cases h with
      | cons hs heb tail drop =>
        cases tail
        exact hmin.csInf_eq.trans hmax.csSup_eq.symm
  exact ⟨haq, hqb, hmax, hmin, hmax.csSup_eq, hmin.csInf_eq,
    he, hcompare, hsem, hequal, hstrict⟩

end D5.S3.Combinatorics.Lattices.HarderNarasimhan
