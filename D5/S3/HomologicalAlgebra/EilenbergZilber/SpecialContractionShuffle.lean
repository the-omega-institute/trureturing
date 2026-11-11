/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContractionShuffle
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/SpecialContractionShuffle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paired simplex map cancellation for the Eilenberg–Mac Lane recursion. -/

import D5.S3.HomologicalAlgebra.EilenbergZilber.NormalizedOperators

/-! # Special contractions of the bisimplicial Eilenberg–Zilber homotopy -/

noncomputable section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber
namespace BisimplicialObject

/-- An adjacent pair identified by a simplex map. -/
def Repeats {n : ℕ} {a : SimplexCategory} (f : (⦋n⦌ : SimplexCategory) ⟶ a)
    (i : Fin n) : Prop :=
  f.toOrderHom i.castSucc = f.toOrderHom i.succ

lemma Repeats.comp {n : ℕ} {a b : SimplexCategory}
    {f : (⦋n⦌ : SimplexCategory) ⟶ a} {i : Fin n} (h : Repeats f i) (g : a ⟶ b) :
    Repeats (f ≫ g) i := by
  exact congrArg g.toOrderHom h

private lemma hLetter_fst_val (n : ℕ) (r : Fin (n + 1)) (ν : Shuffle r.val (n - r.val))
    (i : Fin (n + 1)) :
    ((hLetter n r ν).fst.toOrderHom i : ℕ) =
      (ν.1 (i.cast (by have := r.isLt; omega))).1.val := by
  simp only [hLetter, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, val_eqToHom_apply]
  change (ν.1 _).1.val = (ν.1 _).1.val
  congr 2
  apply congrArg (fun j => ν.1 j)
  exact Fin.ext (val_eqToHom_apply _ _)

private lemma hLetter_snd_val (n : ℕ) (r : Fin (n + 1)) (ν : Shuffle r.val (n - r.val))
    (i : Fin (n + 1)) :
    ((hLetter n r ν).snd.toOrderHom i : ℕ) =
      r.val + (ν.1 (i.cast (by have := r.isLt; omega))).2.val := by
  simp only [hLetter, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, val_eqToHom_apply]
  change r.val + (ν.1 _).2.val = r.val + (ν.1 _).2.val
  congr 3
  apply congrArg (fun j => ν.1 j)
  exact Fin.ext (val_eqToHom_apply _ _)

/-- A repeat before the split in the first input coordinate, or at or after the
split in the second, forces a common repeat in this shuffle summand. -/
private lemma hLetter_common_repeat {n : ℕ} {a b : SimplexCategory}
    (f : (⦋n⦌ : SimplexCategory) ⟶ a) (g : (⦋n⦌ : SimplexCategory) ⟶ b)
    (r : Fin (n + 1)) (ν : Shuffle r.val (n - r.val))
    (h : (∃ j : Fin n, j.val < r.val ∧ Repeats f j) ∨
         (∃ k : Fin n, r.val ≤ k.val ∧ Repeats g k)) :
    ∃ i : Fin n, Repeats ((hLetter n r ν).fst ≫ f) i ∧
      Repeats ((hLetter n r ν).snd ≫ g) i := by
  have hr := r.isLt
  rcases h with ⟨j, hj, hfj⟩ | ⟨k, hk, hgk⟩
  · obtain ⟨i, hi₀, hi₁, hi₂⟩ := Shuffle.exists_fst_step ν j.val (by omega)
    let t : Fin n := i.cast (by omega)
    have hc : t.castSucc.cast (by omega) = i.castSucc := Fin.ext rfl
    have hs : t.succ.cast (by omega) = i.succ := Fin.ext rfl
    have e₀ : (hLetter n r ν).fst.toOrderHom t.castSucc = j.castSucc := by
      apply Fin.ext
      rw [hLetter_fst_val, hc]
      exact hi₀
    have e₁ : (hLetter n r ν).fst.toOrderHom t.succ = j.succ := by
      apply Fin.ext
      rw [hLetter_fst_val, hs]
      exact hi₁
    have e₂ : Repeats (hLetter n r ν).snd t := by
      apply Fin.ext
      rw [hLetter_snd_val, hLetter_snd_val, hc, hs, hi₂]
    refine ⟨t, ?_, e₂.comp g⟩
    change f.toOrderHom ((hLetter n r ν).fst.toOrderHom t.castSucc) =
      f.toOrderHom ((hLetter n r ν).fst.toOrderHom t.succ)
    rw [e₀, e₁]
    exact hfj
  · have hk' := k.isLt
    obtain ⟨i, hi₀, hi₁, hi₂⟩ := Shuffle.exists_snd_step ν (k.val - r.val) (by omega)
    let t : Fin n := i.cast (by omega)
    have hc : t.castSucc.cast (by omega) = i.castSucc := Fin.ext rfl
    have hs : t.succ.cast (by omega) = i.succ := Fin.ext rfl
    have e₀ : (hLetter n r ν).snd.toOrderHom t.castSucc = k.castSucc := by
      apply Fin.ext
      rw [hLetter_snd_val, hc, hi₀]
      change r.val + (k.val - r.val) = k.val
      omega
    have e₁ : (hLetter n r ν).snd.toOrderHom t.succ = k.succ := by
      apply Fin.ext
      rw [hLetter_snd_val, hs, hi₁]
      change r.val + (k.val - r.val + 1) = k.val + 1
      omega
    have e₂ : Repeats (hLetter n r ν).fst t := by
      apply Fin.ext
      rw [hLetter_fst_val, hLetter_fst_val, hc, hs, hi₂]
    refine ⟨t, e₂.comp f, ?_⟩
    change g.toOrderHom ((hLetter n r ν).snd.toOrderHom t.castSucc) =
      g.toOrderHom ((hLetter n r ν).snd.toOrderHom t.succ)
    rw [e₀, e₁]
    exact hgk

private lemma isNorm_single_of_repeat {s n : ℕ} (l : OpLetter s n) (c : ℤ)
    (i : Fin n) (hf : Repeats l.fst i) (hg : Repeats l.snd i) :
    IsNorm (Finsupp.single l c) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    let k : OpLetter s n :=
      ⟨SimplexCategory.δ i.castSucc ≫ l.fst, SimplexCategory.δ i.castSucc ≫ l.snd⟩
    have e :
        (⟨SimplexCategory.σ i, SimplexCategory.σ i⟩ : OpLetter n (n + 1)).compLetter k = l := by
      cases l
      simp only [OpLetter.compLetter, k, OpLetter.mk.injEq]
      exact ⟨(factor_through_σ i _ hf).symm, (factor_through_σ i _ hg).symm⟩
    have hn := IsNorm.diagDegen (SimplexCategory.σ i) (sigma_not_mono i) (Finsupp.single k c)
    rwa [DerivedOp.single_comp_single, e, mul_one] at hn

private lemma isNorm_sum {s n : ℕ} {ι : Type*} (t : Finset ι) (f : ι → DerivedOp s n)
    (h : ∀ i ∈ t, IsNorm (f i)) : IsNorm (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using IsNorm.zero
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- For an ordered pair of separate repeats, every split meets at least one
repeat, hence every term of the composite has a diagonal degeneracy. -/
lemma hOp_comp_ordered_repeat {s n : ℕ} (l : OpLetter s n) (c : ℤ)
    (j k : Fin n) (hjk : j ≤ k) (hf : Repeats l.fst j) (hg : Repeats l.snd k) :
    IsNorm ((hOp n).comp (Finsupp.single l c)) := by
  let comp : DerivedOp n n →+ DerivedOp s n :=
    { toFun M := M.comp (Finsupp.single l c)
      map_zero' := DerivedOp.zero_comp _
      map_add' M N := DerivedOp.add_comp M N _ }
  change IsNorm (comp (hOp n))
  rw [hOp, map_sum]
  refine isNorm_sum _ _ fun r _ => ?_
  rw [map_sum]
  refine isNorm_sum _ _ fun ν _ => ?_
  change IsNorm (DerivedOp.comp (Finsupp.single (hLetter n r ν) ν.sign) (Finsupp.single l c))
  rw [DerivedOp.single_comp_single]
  have H := hLetter_common_repeat l.fst l.snd r ν
  have h : (∃ i : Fin n, i.val < r.val ∧ Repeats l.fst i) ∨
      (∃ i : Fin n, r.val ≤ i.val ∧ Repeats l.snd i) := by
    by_cases hj : j.val < r.val
    · exact Or.inl ⟨j, hj, hf⟩
    · exact Or.inr ⟨k, by have : j.val ≤ k.val := hjk; omega, hg⟩
  obtain ⟨i, hi, hi'⟩ := H h
  exact isNorm_single_of_repeat _ _ i hi hi'


/-- A shuffle with no offending step at the split must pass through the
horizontal-then-vertical corner, and that corner determines the entire path. -/
private lemma shuffle_split_repeat_or_corner {p q : ℕ} (μ : Shuffle p q)
    (r : Fin (p + q + 1)) :
    (∃ j : Fin (p + q), j.val < r.val ∧ Repeats (shuffleFstHom μ) j) ∨
    (∃ k : Fin (p + q), r.val ≤ k.val ∧ Repeats (shuffleSndHom μ) k) ∨
    (r.val = p ∧ μ = Shuffle.trivialShuffle p q) := by
  by_cases hy : (μ.1 r).2.val = 0
  · by_cases hx : (μ.1 r).1.val = p
    · right
      right
      have hr : r.val = p := by have := μ.coordSum_eq r; omega
      refine ⟨hr, ?_⟩
      apply Subtype.ext
      apply OrderHom.ext
      funext i
      have hs := μ.coordSum_eq i
      rw [Shuffle.trivialShuffle_apply]
      apply Prod.ext <;> apply Fin.ext
      · change (μ.1 i).1.val = min i.val p
        rcases le_total i r with hir | hri
        · have h := (μ.1.monotone hir).2
          change (μ.1 i).2.val ≤ (μ.1 r).2.val at h
          change i.val ≤ r.val at hir
          omega
        · have h := (μ.1.monotone hri).1
          change (μ.1 r).1.val ≤ (μ.1 i).1.val at h
          change r.val ≤ i.val at hri
          have := (μ.1 i).1.isLt
          omega
      · change (μ.1 i).2.val = i.val - p
        rcases le_total i r with hir | hri
        · have h := (μ.1.monotone hir).2
          change (μ.1 i).2.val ≤ (μ.1 r).2.val at h
          change i.val ≤ r.val at hir
          omega
        · have h := (μ.1.monotone hri).1
          change (μ.1 r).1.val ≤ (μ.1 i).1.val at h
          change r.val ≤ i.val at hri
          have := (μ.1 i).1.isLt
          omega
    · right
      left
      obtain ⟨k, hk, hk', hs⟩ := μ.exists_fst_step (μ.1 r).1.val
        (by have := (μ.1 r).1.isLt; omega)
      refine ⟨k, ?_, hs⟩
      by_contra! h
      have hm := (μ.1.monotone (show k.succ ≤ r by
        change k.val + 1 ≤ r.val; omega)).1
      change (μ.1 k.succ).1.val ≤ (μ.1 r).1.val at hm
      omega
  · left
    obtain ⟨j, hj, hj', hs⟩ := μ.exists_snd_step ((μ.1 r).2.val - 1)
      (by have := (μ.1 r).2.isLt; omega)
    refine ⟨j, ?_, hs⟩
    by_contra! h
    have hm := (μ.1.monotone (show r ≤ j.castSucc by
      change r.val ≤ j.val; exact h)).2
    change (μ.1 r).2.val ≤ (μ.1 j.castSucc).2.val at hm
    omega

/-- The letter of a shuffle has possibly unequal input degrees. -/
private abbrev RectLetter (p q n : ℕ) :=
  ((⦋n⦌ : SimplexCategory) ⟶ ⦋p⦌) × ((⦋n⦌ : SimplexCategory) ⟶ ⦋q⦌)

private def rectShuffleLetter {p q : ℕ} (μ : Shuffle p q) : RectLetter p q (p + q) :=
  ⟨shuffleFstHom μ, shuffleSndHom μ⟩

private abbrev RectOp (p q n : ℕ) := RectLetter p q n →₀ ℤ

private def rectCompLetter {p q n m : ℕ} (l : OpLetter n m) (a : RectLetter p q n) :
    RectLetter p q m :=
  ⟨l.fst ≫ a.1, l.snd ≫ a.2⟩

private def RectNorm {p q n : ℕ} (N : RectOp p q n) : Prop :=
  ∀ a ∈ N.support, ∃ i : Fin n, Repeats a.1 i ∧ Repeats a.2 i

private lemma RectNorm.single {p q n : ℕ} (a : RectLetter p q n) (c : ℤ)
    (h : ∃ i : Fin n, Repeats a.1 i ∧ Repeats a.2 i) :
    RectNorm (Finsupp.single a c) := by
  intro b hb
  rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset hb)]

private lemma RectNorm.sum {ι : Type*} {p q n : ℕ} (t : Finset ι) (f : ι → RectOp p q n)
    (h : ∀ i ∈ t, RectNorm (f i)) : RectNorm (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [RectNorm]
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    intro b hb
    rcases Finset.mem_union.mp (Finsupp.support_add hb) with hb' | hb'
    · exact h a (Finset.mem_insert_self a t) b hb'
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) b hb'

private noncomputable def rectComp {p q n m : ℕ} (M : DerivedOp n m) (N : RectOp p q n) :
    RectOp p q m :=
  N.sum fun a c => M.sum fun l d => Finsupp.single (rectCompLetter l a) (c * d)

private noncomputable def rectCompRight {p q n m : ℕ} (M : DerivedOp n m) :
    RectOp p q n →+ RectOp p q m where
  toFun := rectComp M
  map_zero' := by simp [rectComp]
  map_add' A B := by
    simp only [rectComp]
    apply Finsupp.sum_add_index'
    · intro a; simp
    · intro a c d; simp only [add_mul, Finsupp.single_add]; rw [Finsupp.sum_add]

private noncomputable def rectCompLeft {p q n m : ℕ} (N : RectOp p q n) :
    DerivedOp n m →+ RectOp p q m where
  toFun M := rectComp M N
  map_zero' := by simp [rectComp]
  map_add' A B := by
    simp only [rectComp]
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro a _
    apply Finsupp.sum_add_index'
    · intro l; simp
    · intro l c d; simp only [mul_add, Finsupp.single_add]

private lemma rectComp_single {p q n m : ℕ} (a : RectLetter p q n) (l : OpLetter n m)
    (c d : ℤ) :
    rectComp (Finsupp.single l d) (Finsupp.single a c) =
      Finsupp.single (rectCompLetter l a) (c * d) := by
  simp [rectComp, Finsupp.sum_single_index]

private noncomputable def rectShuffle (p q : ℕ) : RectOp p q (p + q) :=
  ∑ μ : Shuffle p q, Finsupp.single (rectShuffleLetter μ) μ.sign


private lemma shuffle_cast_snd {p q q' : ℕ} (e : q = q') (ν : Shuffle p q)
    (i : Fin (p + q + 1)) :
    let ν' := cast (congrArg (Shuffle p) e) ν
    let i' := i.cast (by rw [e])
    (ν'.1 i').1.val = (ν.1 i).1.val ∧ (ν'.1 i').2.val = (ν.1 i).2.val ∧
      ν'.sign = ν.sign := by
  subst q'
  exact ⟨rfl, rfl, rfl⟩

private lemma rectCompLetter_corner {p q : ℕ} (ν : Shuffle p q) :
    rectCompLetter (hLetter (p + q) ⟨p, by omega⟩
        (cast (congrArg (Shuffle p) (show q = p + q - p by omega)) ν))
        (rectShuffleLetter (Shuffle.trivialShuffle p q)) = rectShuffleLetter ν := by
  apply Prod.ext <;> apply SimplexCategory.Hom.ext <;> apply OrderHom.ext <;> funext i <;>
    apply Fin.ext
  · simp only [rectCompLetter, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    change min ((hLetter _ _ _).fst.toOrderHom i : ℕ) p = (ν.1 i).1.val
    rw [hLetter_fst_val, (shuffle_cast_snd (show q = p + q - p by omega) ν i).1]
    exact min_eq_left (Nat.le_of_lt_succ (ν.1 i).1.isLt)
  · simp only [rectCompLetter, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    change ((hLetter _ _ _).snd.toOrderHom i : ℕ) - p = (ν.1 i).2.val
    rw [hLetter_snd_val, (shuffle_cast_snd (show q = p + q - p by omega) ν i).2.1]
    exact Nat.add_sub_cancel_left p (ν.1 i).2.val

/-- In the signed shuffle sum, only the staircase at the matching split can
contribute a letter without a common plateau. Its contribution is the original
signed shuffle sum, with coefficient one from the staircase. -/
private lemma rectComp_hOp_shuffle_sub (p q : ℕ) :
    RectNorm (rectComp (hOp (p + q)) (rectShuffle p q) - rectShuffle p q) := by
  classical
  let t := Shuffle.trivialShuffle p q
  let r₀ : Fin (p + q + 1) := ⟨p, by omega⟩
  let f := fun (μ : Shuffle p q) (r : Fin (p + q + 1)) (ν : Shuffle r.val (p + q - r.val)) =>
    Finsupp.single (rectCompLetter (hLetter (p + q) r ν) (rectShuffleLetter μ))
      (μ.sign * ν.sign)
  let g := fun (μ : Shuffle p q) (r : Fin (p + q + 1)) => ∑ ν, f μ r ν
  have expand : rectComp (hOp (p + q)) (rectShuffle p q) = ∑ μ, ∑ r, g μ r := by
    change rectCompRight (hOp (p + q)) (∑ μ, Finsupp.single (rectShuffleLetter μ) μ.sign) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro μ _
    change rectCompLeft (Finsupp.single (rectShuffleLetter μ) μ.sign) (hOp (p + q)) = _
    rw [hOp, map_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [map_sum]
    exact Finset.sum_congr rfl fun ν _ => rectComp_single _ _ _ _
  have residue (μ : Shuffle p q) (r : Fin (p + q + 1)) (hne : μ ≠ t ∨ r ≠ r₀) :
      RectNorm (g μ r) := by
    refine RectNorm.sum _ _ fun ν _ => RectNorm.single _ _ ?_
    rcases shuffle_split_repeat_or_corner μ r with h | h | ⟨hr, hm⟩
    · exact hLetter_common_repeat _ _ r ν (Or.inl h)
    · exact hLetter_common_repeat _ _ r ν (Or.inr h)
    · exact False.elim (hne.elim (fun h => h hm) (fun h => h (Fin.ext hr)))
  have good : g t r₀ = rectShuffle p q := by
    let e : Shuffle p q ≃ Shuffle p (p + q - p) :=
      Equiv.cast (congrArg (Shuffle p) (by omega))
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro ν
    have hsign := (shuffle_cast_snd (show q = p + q - p by omega) ν 0).2.2
    change Finsupp.single (rectShuffleLetter ν) ν.sign = f t r₀ (e ν)
    unfold f
    change _ = Finsupp.single
      (rectCompLetter (hLetter (p + q) ⟨p, by omega⟩
        (cast (congrArg (Shuffle p) (by omega : q = p + q - p)) ν)) (rectShuffleLetter t))
      (t.sign * (cast (congrArg (Shuffle p) (by omega : q = p + q - p)) ν).sign)
    rw [rectCompLetter_corner, hsign, Shuffle.sign_trivialShuffle, one_mul]
  rw [expand, ← Finset.sum_erase_add _ _ (Finset.mem_univ t),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ r₀), good, ← add_assoc, add_sub_cancel_right]
  intro a ha
  rcases Finset.mem_union.mp (Finsupp.support_add ha) with ha' | ha'
  · exact RectNorm.sum _ _ (fun μ hμ => RectNorm.sum _ _
      fun r _ => residue μ r (Or.inl (Finset.ne_of_mem_erase hμ))) a ha'
  · exact RectNorm.sum _ _ (fun r hr => residue t r (Or.inr (Finset.ne_of_mem_erase hr))) a ha'


private lemma primeHom_succ {s n : ℕ} (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋s⦌)
    (i : Fin (n + 1)) : (primeHom f).toOrderHom i.succ = (f.toOrderHom i).succ := by
  apply Fin.ext
  have h : (f.toOrderHom i).val + 1 ≤ s + 1 := Fin.isLt _
  simp [primeHom, Nat.min_eq_left h]

private def rectShuffleLetterAt {p q n : ℕ} (e : n = p + q) (μ : Shuffle p q) :
    RectLetter p q n :=
  ⟨eqToHom (congrArg SimplexCategory.mk e) ≫ shuffleFstHom μ,
    eqToHom (congrArg SimplexCategory.mk e) ≫ shuffleSndHom μ⟩

private lemma rectShuffleLetterAt_self {p q : ℕ} (μ : Shuffle p q) :
    rectShuffleLetterAt rfl μ = rectShuffleLetter μ := by
  simp [rectShuffleLetterAt, rectShuffleLetter]

private noncomputable def rectShuffleAt {p q n : ℕ} (e : n = p + q) : RectOp p q n :=
  ∑ μ : Shuffle p q, Finsupp.single (rectShuffleLetterAt e μ) μ.sign

private def leftPrefix {p q n : ℕ} (a : RectLetter p q n) : RectLetter (p + 1) q (n + 1) :=
  ⟨primeHom a.1, primeHom a.2 ≫ SimplexCategory.σ 0⟩

private def rightPrefix {p q n : ℕ} (a : RectLetter p q n) : RectLetter p (q + 1) (n + 1) :=
  ⟨primeHom a.1 ≫ SimplexCategory.σ 0, primeHom a.2⟩

private lemma insertLeftIndex_zero {p q : ℕ} (ν : Shuffle p q) :
    ν.insertLeftIndex 0 = 0 := by
  apply Fin.ext
  simp [Shuffle.insertLeftIndex]

private lemma insertRightIndex_zero {p q : ℕ} (ν : Shuffle p q) :
    ν.insertRightIndex 0 = 0 := by
  apply Fin.ext
  simp [Shuffle.insertRightIndex]

private lemma first_left_sign {p q : ℕ} (ν : Shuffle p q) :
    (ν.insertLeftStep 0).sign = ν.sign := by
  simpa [insertLeftIndex_zero] using Shuffle.sign_insertLeftStep ν 0

private lemma first_right_sign {p q : ℕ} (ν : Shuffle p q) :
    (ν.insertRightStep 0).sign = (-1 : ℤ)^p * ν.sign := by
  simpa [insertRightIndex_zero] using Shuffle.sign_insertRightStep ν 0

private lemma first_left_letter {p q n : ℕ} (e : n = p + q)
    (E : n + 1 = (p + 1) + q) (ν : Shuffle p q) :
    rectShuffleLetterAt E (ν.insertLeftStep 0) = leftPrefix (rectShuffleLetterAt e ν) := by
  apply Prod.ext <;> apply SimplexCategory.Hom.ext <;> apply OrderHom.ext <;> funext i <;>
    refine Fin.cases ?_ (fun j => ?_) i
  · apply Fin.ext
    simp [rectShuffleLetterAt, leftPrefix, primeHom, shuffleFstHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom, Shuffle.apply_zero]
  · apply Fin.ext
    simp only [rectShuffleLetterAt, leftPrefix, primeHom_succ, SimplexCategory.comp_toOrderHom,
      OrderHom.comp_coe, Function.comp_apply, shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.fst_coe, SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso_apply,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.val_succ]
    change (Shuffle.insertLeftStepFun ν 0 _).1.val = _
    simp [Shuffle.insertLeftStepFun, insertLeftIndex_zero]
    rfl
  · apply Fin.ext
    simp [rectShuffleLetterAt, leftPrefix, primeHom, shuffleSndHom, SimplexCategory.σ,
      SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom, Shuffle.apply_zero]
  · simp only [rectShuffleLetterAt, leftPrefix, primeHom_succ, SimplexCategory.comp_toOrderHom,
      OrderHom.comp_coe, Function.comp_apply, shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.snd_coe, SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso_apply,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding]
    change (Shuffle.insertLeftStepFun ν 0 _).2 = (0 : Fin (q + 1)).predAbove (Fin.succ _)
    rw [Fin.predAbove_zero_succ]
    simp [Shuffle.insertLeftStepFun, insertLeftIndex_zero]
    rfl

private lemma first_right_letter {p q n : ℕ} (e : n = p + q)
    (E : n + 1 = p + (q + 1)) (ν : Shuffle p q) :
    rectShuffleLetterAt E (ν.insertRightStep 0) = rightPrefix (rectShuffleLetterAt e ν) := by
  apply Prod.ext <;> apply SimplexCategory.Hom.ext <;> apply OrderHom.ext <;> funext i <;>
    refine Fin.cases ?_ (fun j => ?_) i
  · apply Fin.ext
    simp [rectShuffleLetterAt, rightPrefix, primeHom, shuffleFstHom, SimplexCategory.σ,
      SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom, Shuffle.apply_zero]
  · simp only [rectShuffleLetterAt, rightPrefix, primeHom_succ, SimplexCategory.comp_toOrderHom,
      OrderHom.comp_coe, Function.comp_apply, shuffleFstHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.fst_coe, SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso_apply,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding]
    change (Shuffle.insertRightStepFun ν 0 _).1 = (0 : Fin (p + 1)).predAbove (Fin.succ _)
    rw [Fin.predAbove_zero_succ]
    simp [Shuffle.insertRightStepFun, insertRightIndex_zero]
    rfl
  · apply Fin.ext
    simp [rectShuffleLetterAt, rightPrefix, primeHom, shuffleSndHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom, Shuffle.apply_zero]
  · apply Fin.ext
    simp only [rectShuffleLetterAt, rightPrefix, primeHom_succ, SimplexCategory.comp_toOrderHom,
      OrderHom.comp_coe, Function.comp_apply, shuffleSndHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.snd_coe, SimplexCategory.eqToHom_toOrderHom, Fin.castOrderIso_apply,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.val_succ]
    change (Shuffle.insertRightStepFun ν 0 _).2.val = _
    simp [Shuffle.insertRightStepFun, insertRightIndex_zero]
    rfl

private lemma firstLeft_nonDiag {p q : ℕ} (μ : Shuffle (p + 1) q)
    (h : μ.isLeftStep 0) : ∃ ν : Shuffle p q, ν.insertLeftStep 0 = μ := by
  let r : Fin (p + q + 2) := 0
  have hV : μ.isLeftVertex (r.cast (by omega)) := by
    constructor
    · intro k hk
      have he := congrArg Fin.val hk
      change k.val + 1 = 0 at he
      omega
    · intro k hk
      have e : k = 0 := Fin.ext (congrArg (fun x => x.val) hk)
      simpa only [e] using h
  refine ⟨μ.removeLeft r hV, ?_⟩
  have H := Shuffle.insertLeft_removeLeft hV
  simpa [r, Shuffle.apply_zero] using H

private lemma firstRight_nonDiag {p q : ℕ} (μ : Shuffle p (q + 1))
    (h : ¬ μ.isLeftStep 0) : ∃ ν : Shuffle p q, ν.insertRightStep 0 = μ := by
  have h' : μ.swap.isLeftStep 0 := by
    rw [Shuffle.isLeftStep, Shuffle.swap_apply_fst, Shuffle.swap_apply_fst]
    have hiff := μ.shuffle_fst_lt_iff_not_snd_lt 0
    simp only [Shuffle.isLeftStep] at h
    have e₀ : (Fin.cast (by omega) ((0 : Fin (q + 1 + p)).castSucc) : Fin (p + (q + 1) + 1)) =
        (0 : Fin (p + (q + 1))).castSucc := Fin.ext rfl
    have e₁ : (Fin.cast (by omega) ((0 : Fin (q + 1 + p)).succ) : Fin (p + (q + 1) + 1)) =
        (0 : Fin (p + (q + 1))).succ := Fin.ext rfl
    rw [e₀, e₁]
    by_contra hn
    exact h (hiff.mpr hn)
  obtain ⟨ν, hν⟩ := firstLeft_nonDiag μ.swap h'
  refine ⟨ν.swap, (Shuffle.swapEquiv _ _).injective ?_⟩
  change (ν.swap.insertRightStep 0).swap = μ.swap
  rwa [Shuffle.insertRightStep_eq_swap, Shuffle.swap_swap]

private lemma firstLeft_isLeft {p q : ℕ} (ν : Shuffle p q) :
    (ν.insertLeftStep 0).isLeftStep 0 := by
  simpa [insertLeftIndex_zero] using
    Shuffle.insertLeftStep_isLeftStep_at ν 0 (by rw [insertLeftIndex_zero]; simp)

private lemma firstRight_isRight {p q : ℕ} (ν : Shuffle p q) :
    ¬ (ν.insertRightStep 0).isLeftStep 0 := by
  simpa [insertRightIndex_zero] using Shuffle.insertRightStep_not_isLeftType ν 0

private noncomputable def shuffleFirstEquiv (p q : ℕ) :
    Sum (Shuffle p (q + 1)) (Shuffle (p + 1) q) ≃ Shuffle (p + 1) (q + 1) :=
  Equiv.ofBijective (Sum.elim (fun ν => ν.insertLeftStep 0) (fun ν => ν.insertRightStep 0)) (by
    constructor
    · intro a b h
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          exact congrArg Sum.inl (Shuffle.insertLeftStep_injective 0 0 a b h
            (by simp [insertLeftIndex_zero])).2
        | inr b =>
          change a.insertLeftStep 0 = b.insertRightStep 0 at h
          exact False.elim (firstRight_isRight b (h ▸ firstLeft_isLeft a))
      | inr a =>
        cases b with
        | inl b =>
          change a.insertRightStep 0 = b.insertLeftStep 0 at h
          exact False.elim (firstRight_isRight a (h.symm ▸ firstLeft_isLeft b))
        | inr b =>
          exact congrArg Sum.inr (Shuffle.insertRightStep_injective 0 0 a b h
            (by simp [insertRightIndex_zero])).2
    · intro μ
      by_cases h : μ.isLeftStep 0
      · obtain ⟨ν, hν⟩ := firstLeft_nonDiag μ h
        exact ⟨Sum.inl ν, hν⟩
      · obtain ⟨ν, hν⟩ := firstRight_nonDiag μ h
        exact ⟨Sum.inr ν, hν⟩)

/-- The signed first-step split, with signs inherited from the actual insertion
identities. The two axes have just their one available first step. -/
private lemma rectShuffleAt_first {p q n : ℕ} (e : n + 1 = (p + 1) + (q + 1)) :
    rectShuffleAt e =
      Finsupp.mapDomain leftPrefix (rectShuffleAt (show n = p + (q + 1) by omega)) +
        ((-1 : ℤ) ^ (p + 1)) •
          Finsupp.mapDomain rightPrefix (rectShuffleAt (show n = (p + 1) + q by omega)) := by
  classical
  rw [rectShuffleAt, ← (shuffleFirstEquiv p q).sum_comp, Fintype.sum_sum_type]
  simp only [rectShuffleAt, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single,
    Finset.smul_sum, Finsupp.smul_single']
  congr 1
  · apply Finset.sum_congr rfl
    intro ν _
    change Finsupp.single (rectShuffleLetterAt e (ν.insertLeftStep 0))
      (ν.insertLeftStep 0).sign = _
    rw [first_left_letter, first_left_sign]
  · apply Finset.sum_congr rfl
    intro ν _
    change Finsupp.single (rectShuffleLetterAt e (ν.insertRightStep 0))
      (ν.insertRightStep 0).sign = _
    rw [first_right_letter, first_right_sign]

private lemma rectShuffleAt_first_left_axis {p n : ℕ} (e : n + 1 = (p + 1) + 0) :
    rectShuffleAt e =
      Finsupp.mapDomain leftPrefix (rectShuffleAt (show n = p + 0 by omega)) := by
  classical
  let e₀ : Shuffle p 0 ≃ Shuffle (p + 1) 0 :=
    Equiv.ofBijective (fun ν => ν.insertLeftStep 0) (by
      constructor
      · intro a b _; exact Subsingleton.elim a b
      · intro a; exact ⟨default, Subsingleton.elim _ a⟩)
  rw [rectShuffleAt, ← e₀.sum_comp]
  simp only [rectShuffleAt, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  apply Finset.sum_congr rfl
  intro ν _
  change Finsupp.single (rectShuffleLetterAt e (ν.insertLeftStep 0))
    (ν.insertLeftStep 0).sign = _
  rw [first_left_letter, first_left_sign]

private lemma rectShuffleAt_first_right_axis {q n : ℕ} (e : n + 1 = 0 + (q + 1)) :
    rectShuffleAt e =
      Finsupp.mapDomain rightPrefix (rectShuffleAt (show n = 0 + q by omega)) := by
  classical
  let e₀ : Shuffle 0 q ≃ Shuffle 0 (q + 1) :=
    Equiv.ofBijective (fun ν => ν.insertRightStep 0) (by
      constructor
      · intro a b _; exact Subsingleton.elim a b
      · intro a; exact ⟨default, Subsingleton.elim _ a⟩)
  rw [rectShuffleAt, ← e₀.sum_comp]
  simp only [rectShuffleAt, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  apply Finset.sum_congr rfl
  intro ν _
  change Finsupp.single (rectShuffleLetterAt e (ν.insertRightStep 0))
    (ν.insertRightStep 0).sign = _
  rw [first_right_letter, first_right_sign, pow_zero, one_mul]

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

The declarations IsFrontalHom, primeHom_frontal and primeHom_comp_degenZero are from
LeanPool/EilenbergZilber/BisimplicialDerivedOp.lean, author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: hOp_horizontal_frontal is a local calculation for the horizontal
coordinate of the shuffle summands.
The legal chain is recorded in Library/HomologicalAlgebra/li2026bisimplicialeilenbergzilber.md.
Use these declarations with the received phiOp definition. Retire the transplanted
closure when the pinned upstream library supplies equivalent declarations.
-/

/-- A `SimplexCategory` map is **frontal** if it fixes the bottom vertex `0` (equivalently its
operator word avoids the 0-th face `F₀`). -/
def IsFrontalHom {a b : ℕ} (f : (⦋a⦌ : SimplexCategory) ⟶ ⦋b⦌) : Prop :=
  SimplexCategory.Hom.toOrderHom f 0 = 0

/-- The horizontal coordinate of each supported `hOp` letter fixes zero. -/
lemma hOp_horizontal_frontal (n : ℕ) (l : OpLetter n n) (hl : l ∈ (hOp n).support) :
    IsFrontalHom l.fst := by
  have H {ι : Type} (t : Finset ι) (f : ι → DerivedOp n n)
      (hf : ∀ i ∈ t, ∀ k ∈ (f i).support, IsFrontalHom k.fst) :
      ∀ k ∈ (∑ i ∈ t, f i).support, IsFrontalHom k.fst := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      rw [Finset.sum_insert hi]
      intro k hk
      rcases Finset.mem_union.mp (Finsupp.support_add hk) with hk | hk
      · exact hf i (Finset.mem_insert_self _ _) k hk
      · exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) k hk
  rw [hOp] at hl
  refine H Finset.univ _ (fun r _ => H Finset.univ _ (fun ν _ k hk => ?_)) l hl
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hk)]
  apply Fin.ext
  change ((hLetter n r ν).fst.toOrderHom 0 : ℕ) = 0
  rw [hLetter_fst_val]
  simp [Shuffle.apply_zero]

/-- `primeHom θ` is frontal: it fixes the bottom vertex `0` (`primeHom` sends `0 ↦ 0`). -/
lemma primeHom_frontal {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    IsFrontalHom (primeHom θ) := by
  simp [IsFrontalHom, primeHom]

/-- For a **frontal** map (`θ 0 = 0`), the prepended vertex collapses against `σ 0`:
`primeHom θ ≫ σ 0 = σ 0 ≫ θ`. The combinatorial core of `prime_comp_D0_of_frontal`; frontality
is exactly what makes the two sides agree at the bottom vertex. -/
lemma primeHom_comp_degenZero {s q : ℕ} (θ : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌)
    (hθ : IsFrontalHom θ) :
    primeHom θ ≫ SimplexCategory.σ (0 : Fin (s + 1))
      = SimplexCategory.σ (0 : Fin (q + 1)) ≫ θ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · -- `j = 0`: both sides land on the bottom vertex; `σ 0` and `primeHom` send `0 ↦ 0`, and
    -- `θ 0 = 0` (frontality) closes `0 = ↑(θ 0)`.
    apply Fin.ext
    simp only [IsFrontalHom] at hθ
    simp only [SimplexCategory.len_mk, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
      Function.comp_apply]
    exact (congrArg Fin.val hθ).symm
  · -- `j = k.succ`: `primeHom θ` gives `θ(k) + 1`, then `σ 0` (always `0 < θ(k)+1`) drops back to
    -- `θ(k) = min (θ k) s`, matching `θ (σ 0 (k.succ)) = θ k`.
    apply Fin.ext
    simp [primeHom, SimplexCategory.σ, Fin.predAbove]
    have hk := (SimplexCategory.Hom.toOrderHom θ k).isLt
    simp only [SimplexCategory.len_mk] at hk
    split_ifs <;> simp_all [Fin.lt_def]

private lemma RectNorm.add {p q n : ℕ} {N K : RectOp p q n}
    (hN : RectNorm N) (hK : RectNorm K) : RectNorm (N + K) := by
  intro a ha
  exact (Finset.mem_union.mp (Finsupp.support_add ha)).elim (hN a) (hK a)

private lemma RectNorm.zsmul {p q n : ℕ} {N : RectOp p q n} (hN : RectNorm N) (c : ℤ) :
    RectNorm (c • N) := fun a ha => hN a (Finsupp.support_smul ha)

private lemma RectNorm.mapDomain {p q n p' q' n' : ℕ} {N : RectOp p q n}
    (hN : RectNorm N) (f : RectLetter p q n → RectLetter p' q' n')
    (hf : ∀ a, (∃ i : Fin n, Repeats a.1 i ∧ Repeats a.2 i) →
      ∃ i : Fin n', Repeats (f a).1 i ∧ Repeats (f a).2 i) :
    RectNorm (Finsupp.mapDomain f N) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  exact hf b (hN b hb)

lemma Repeats.prime {s n : ℕ} {f : (⦋n⦌ : SimplexCategory) ⟶ ⦋s⦌}
    {i : Fin n} (h : Repeats f i) : Repeats (primeHom f) i.succ := by
  have he : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
  unfold Repeats at *
  rw [he, primeHom_succ, primeHom_succ, h]

private def rectLift {p q n p' q' : ℕ} (f : (⦋p + 1⦌ : SimplexCategory) ⟶ ⦋p'⦌)
    (g : (⦋q + 1⦌ : SimplexCategory) ⟶ ⦋q'⦌) (a : RectLetter p q n) :
    RectLetter p' q' (n + 1) :=
  ⟨primeHom a.1 ≫ f, primeHom a.2 ≫ g⟩

private lemma RectNorm.lift {p q n p' q' : ℕ} {N : RectOp p q n} (hN : RectNorm N)
    (f : (⦋p + 1⦌ : SimplexCategory) ⟶ ⦋p'⦌)
    (g : (⦋q + 1⦌ : SimplexCategory) ⟶ ⦋q'⦌) :
    RectNorm (Finsupp.mapDomain (rectLift f g) N) :=
  hN.mapDomain _ fun _ ⟨i, h, k⟩ => ⟨i.succ, h.prime.comp f, k.prime.comp g⟩

/-- Extend a commuting identity on pairs to their finite integer sums. -/
private lemma rectComp_map {p q n m p' q' n' m' : ℕ}
    (M : DerivedOp n m) (N : RectOp p q n)
    (u : OpLetter n m → OpLetter n' m')
    (f : RectLetter p q n → RectLetter p' q' n')
    (g : RectLetter p q m → RectLetter p' q' m')
    (h : ∀ l a, rectCompLetter (u l) (f a) = g (rectCompLetter l a)) :
    rectComp (Finsupp.mapDomain u M) (Finsupp.mapDomain f N) =
      Finsupp.mapDomain g (rectComp M N) := by
  let U : DerivedOp n m →+ DerivedOp n' m' := Finsupp.mapDomain.addMonoidHom u
  let F : RectOp p q n →+ RectOp p' q' n' := Finsupp.mapDomain.addMonoidHom f
  let G : RectOp p q m →+ RectOp p' q' m' := Finsupp.mapDomain.addMonoidHom g
  change (((rectCompRight (U M)).comp F) N) = ((G.comp (rectCompRight M)) N)
  apply DFunLike.congr_fun
  apply Finsupp.addHom_ext
  intro a c
  simp only [AddMonoidHom.comp_apply]
  change rectCompLeft (F (Finsupp.single a c)) (U M) =
    G (rectCompLeft (Finsupp.single a c) M)
  change (((rectCompLeft (F (Finsupp.single a c))).comp U) M) =
    ((G.comp (rectCompLeft (Finsupp.single a c))) M)
  apply DFunLike.congr_fun
  apply Finsupp.addHom_ext
  intro l d
  simp only [AddMonoidHom.comp_apply]
  change rectComp (Finsupp.mapDomain u (Finsupp.single l d))
      (Finsupp.mapDomain f (Finsupp.single a c)) =
    Finsupp.mapDomain g (rectComp (Finsupp.single l d) (Finsupp.single a c))
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, rectComp_single,
    rectComp_single, Finsupp.mapDomain_single, h]

private lemma rectComp_prime_lift {p q n m p' q' : ℕ} (M : DerivedOp n m) (N : RectOp p q n)
    (f : (⦋p + 1⦌ : SimplexCategory) ⟶ ⦋p'⦌)
    (g : (⦋q + 1⦌ : SimplexCategory) ⟶ ⦋q'⦌) :
    rectComp M.prime (Finsupp.mapDomain (rectLift f g) N) =
      Finsupp.mapDomain (rectLift f g) (rectComp M N) :=
  rectComp_map M N _ _ _ (by
    intro l a
    simp only [rectCompLetter, OpLetter.primeLetter, rectLift, primeHom_comp, Category.assoc])

def diagLetter {n : ℕ} (i : Fin (n + 1)) : OpLetter n (n + 1) :=
  ⟨SimplexCategory.σ i, SimplexCategory.σ i⟩

private lemma rectComp_comp_D0 {p q n m : ℕ} (M : DerivedOp (n + 1) m) (N : RectOp p q n) :
    rectComp (M.comp (D0op n)) N =
      rectComp M (Finsupp.mapDomain (rectCompLetter (diagLetter 0)) N) := by
  let F : DerivedOp (n + 1) m →+ DerivedOp n m :=
    { toFun A := A.comp (D0op n)
      map_zero' := DerivedOp.zero_comp _
      map_add' A B := DerivedOp.add_comp A B _ }
  let G : RectOp p q n →+ RectOp p q (n + 1) :=
    Finsupp.mapDomain.addMonoidHom (rectCompLetter (diagLetter 0))
  change ((rectCompRight (F M)) N) = (((rectCompRight M).comp G) N)
  apply DFunLike.congr_fun
  apply Finsupp.addHom_ext
  intro a c
  change ((rectCompLeft (Finsupp.single a c)).comp F) M =
    rectCompLeft (G (Finsupp.single a c)) M
  apply DFunLike.congr_fun
  apply Finsupp.addHom_ext
  intro l d
  change rectComp (DerivedOp.comp (Finsupp.single l d) (D0op n)) (Finsupp.single a c) =
    rectComp (Finsupp.single l d)
      (Finsupp.mapDomain (rectCompLetter (diagLetter 0)) (Finsupp.single a c))
  rw [D0op, DerivedOp.single_comp_single, one_mul, Finsupp.mapDomain_single,
    rectComp_single, rectComp_single]
  congr 1

private lemma rectShuffleAt_self (p q : ℕ) :
    rectShuffleAt (rfl : p + q = p + q) = rectShuffle p q := by
  simp only [rectShuffleAt, rectShuffle, rectShuffleLetterAt_self]

private lemma rectShuffleAt_front {p q n : ℕ} (e : n = p + q) (μ : Shuffle p q) :
    IsFrontalHom (rectShuffleLetterAt e μ).1 ∧ IsFrontalHom (rectShuffleLetterAt e μ).2 := by
  subst n
  rw [rectShuffleLetterAt_self]
  constructor <;>
    simp [IsFrontalHom, rectShuffleLetter, shuffleFstHom, shuffleSndHom, Shuffle.apply_zero]

private lemma rectShuffleAt_D0 {p q n : ℕ} (e : n = p + q) :
    Finsupp.mapDomain (rectCompLetter (diagLetter 0)) (rectShuffleAt e) =
      Finsupp.mapDomain (rectLift (SimplexCategory.σ 0) (SimplexCategory.σ 0))
        (rectShuffleAt e) := by
  simp only [rectShuffleAt, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
  apply Finset.sum_congr rfl
  intro μ _
  congr 1
  obtain ⟨h, k⟩ := rectShuffleAt_front e μ
  simp only [rectCompLetter, diagLetter, rectLift, primeHom_comp_degenZero _ h,
    primeHom_comp_degenZero _ k]

lemma repeats_sigma (n : ℕ) (i : Fin (n + 1)) : Repeats (SimplexCategory.σ i) i := by
  change i.predAbove i.castSucc = i.predAbove i.succ
  rw [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]

private lemma rectComp_hPrime_D0_shuffleAt {p q n : ℕ} (e : n = p + q) :
    RectNorm (rectComp ((hOp n).prime.comp (D0op n)) (rectShuffleAt e)) := by
  rw [rectComp_comp_D0, rectShuffleAt_D0, rectComp_prime_lift]
  let L : RectOp p q n →+ RectOp p q (n + 1) := Finsupp.mapDomain.addMonoidHom
    (rectLift (SimplexCategory.σ (0 : Fin (p + 1))) (SimplexCategory.σ (0 : Fin (q + 1))))
  change RectNorm (L (rectComp (hOp n) (rectShuffleAt e)))
  rw [← sub_add_cancel (rectComp (hOp n) (rectShuffleAt e)) (rectShuffleAt e), map_add]
  apply RectNorm.add
  · have h : RectNorm (rectComp (hOp n) (rectShuffleAt e) - rectShuffleAt e) := by
      subst n
      rw [rectShuffleAt_self]
      exact rectComp_hOp_shuffle_sub p q
    exact h.lift _ _
  · change RectNorm (Finsupp.mapDomain _ (rectShuffleAt e))
    rw [← rectShuffleAt_D0]
    intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
    exact ⟨0, (repeats_sigma n 0).comp b.1, (repeats_sigma n 0).comp b.2⟩

/-- The actual recursive homotopy takes the signed shuffle into diagonal
degeneracies, before any realization. -/
private lemma rectComp_phi_shuffleAt (n : ℕ) :
    ∀ {p q : ℕ} (e : n = p + q), RectNorm (rectComp (phiOp n) (rectShuffleAt e)) := by
  induction n with
  | zero =>
    intro p q e
    simp [phiOp, rectComp, RectNorm]
  | succ n ih =>
    intro p q e
    rw [phiOp]
    change RectNorm (rectCompLeft (rectShuffleAt e)
      (-(phiOp n).prime + (hOp (n + 1)).prime.comp (D0op (n + 1))))
    rw [map_add, map_neg]
    apply RectNorm.add
    · change RectNorm (-rectComp (phiOp n).prime (rectShuffleAt e))
      rw [show -rectComp (phiOp n).prime (rectShuffleAt e) =
          (-1 : ℤ) • rectComp (phiOp n).prime (rectShuffleAt e) from (neg_one_zsmul _).symm]
      apply RectNorm.zsmul
      cases p <;> cases q
      · omega
      · rw [rectShuffleAt_first_right_axis]
        change RectNorm (rectComp (phiOp n).prime
          (Finsupp.mapDomain (rectLift (SimplexCategory.σ 0) (𝟙 _)) _))
        rw [rectComp_prime_lift]
        exact (ih _).lift _ _
      · rw [rectShuffleAt_first_left_axis]
        change RectNorm (rectComp (phiOp n).prime
          (Finsupp.mapDomain (rectLift (𝟙 _) (SimplexCategory.σ 0)) _))
        rw [rectComp_prime_lift]
        exact (ih _).lift _ _
      · rw [rectShuffleAt_first]
        change RectNorm (rectCompRight (phiOp n).prime (_ + _ • _))
        rw [map_add, map_zsmul]
        apply RectNorm.add
        · change RectNorm (rectComp (phiOp n).prime
            (Finsupp.mapDomain (rectLift (𝟙 _) (SimplexCategory.σ 0)) _))
          rw [rectComp_prime_lift]
          exact (ih _).lift _ _
        · apply RectNorm.zsmul
          change RectNorm (rectComp (phiOp n).prime
            (Finsupp.mapDomain (rectLift (SimplexCategory.σ 0) (𝟙 _)) _))
          rw [rectComp_prime_lift]
          exact (ih _).lift _ _
    · exact rectComp_hPrime_D0_shuffleAt e

private def rectEmbed {p q s n : ℕ} (f : (⦋p⦌ : SimplexCategory) ⟶ ⦋s⦌)
    (g : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (a : RectLetter p q n) : OpLetter s n :=
  ⟨a.1 ≫ f, a.2 ≫ g⟩

private lemma rectEmbed_comp {p q s n m : ℕ} (f : (⦋p⦌ : SimplexCategory) ⟶ ⦋s⦌)
    (g : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) (M : DerivedOp n m) (N : RectOp p q n) :
    Finsupp.mapDomain (rectEmbed f g) (rectComp M N) =
      M.comp (Finsupp.mapDomain (rectEmbed f g) N) := by
  let F : RectOp p q n →+ DerivedOp s n := Finsupp.mapDomain.addMonoidHom (rectEmbed f g)
  let G : RectOp p q m →+ DerivedOp s m := Finsupp.mapDomain.addMonoidHom (rectEmbed f g)
  let D (A : DerivedOp n m) : DerivedOp s n →+ DerivedOp s m :=
    { toFun B := A.comp B
      map_zero' := by simp [DerivedOp.comp]
      map_add' := DerivedOp.comp_add_right A }
  let E (B : DerivedOp s n) : DerivedOp n m →+ DerivedOp s m :=
    { toFun A := A.comp B
      map_zero' := DerivedOp.zero_comp _
      map_add' A A' := DerivedOp.add_comp A A' _ }
  change (G.comp (rectCompRight M)) N = ((D M).comp F) N
  apply DFunLike.congr_fun
  apply Finsupp.addHom_ext
  intro a c
  change (G.comp (rectCompLeft (Finsupp.single a c))) M = E (F (Finsupp.single a c)) M
  apply DFunLike.congr_fun
  apply Finsupp.addHom_ext
  intro l d
  change Finsupp.mapDomain (rectEmbed f g)
      (rectComp (Finsupp.single l d) (Finsupp.single a c)) =
    DerivedOp.comp (Finsupp.single l d)
      (Finsupp.mapDomain (rectEmbed f g) (Finsupp.single a c))
  rw [rectComp_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    DerivedOp.single_comp_single]
  congr 1

private lemma RectNorm.embed {p q s n : ℕ} {N : RectOp p q n} (hN : RectNorm N)
    (f : (⦋p⦌ : SimplexCategory) ⟶ ⦋s⦌) (g : (⦋q⦌ : SimplexCategory) ⟶ ⦋s⦌) :
    IsNorm (Finsupp.mapDomain (rectEmbed f g) N) := by
  classical
  rw [← N.sum_single, Finsupp.mapDomain_sum]
  change IsNorm (∑ a ∈ N.support, Finsupp.mapDomain (rectEmbed f g) (Finsupp.single a (N a)))
  refine isNorm_sum _ _ fun a ha => ?_
  rw [Finsupp.mapDomain_single]
  obtain ⟨i, hf, hg⟩ := hN a ha
  exact isNorm_single_of_repeat _ _ i (hf.comp f) (hg.comp g)

lemma phiOp_comp_hOp_isNorm (n : ℕ) : IsNorm ((phiOp n).comp (hOp n)) := by
  let L : DerivedOp n n →+ DerivedOp n (n + 1) :=
    { toFun M := (phiOp n).comp M
      map_zero' := by simp [DerivedOp.comp]
      map_add' := DerivedOp.comp_add_right _ }
  change IsNorm (L (hOp n))
  rw [hOp, map_sum]
  refine isNorm_sum _ _ fun r _ => ?_
  let p := r.val
  let q := n - r.val
  have e : n = p + q := by have := r.isLt; dsimp [p, q]; omega
  let f := ιFront p q ≫ eqToHom (congrArg SimplexCategory.mk e.symm)
  let g := ιBack p q ≫ eqToHom (congrArg SimplexCategory.mk e.symm)
  have H := (rectComp_phi_shuffleAt n e).embed f g
  rw [rectEmbed_comp] at H
  change IsNorm (L (Finsupp.mapDomain (rectEmbed f g) (rectShuffleAt e))) at H
  have E : Finsupp.mapDomain (rectEmbed f g) (rectShuffleAt e) =
      ∑ μ : Shuffle p q, Finsupp.single (hLetter n r μ) μ.sign := by
    simp only [rectShuffleAt, Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_single]
    apply Finset.sum_congr rfl
    intro μ _
    congr 1
  rwa [E] at H

end BisimplicialObject
end D5.S3.HomologicalAlgebra.EilenbergZilber
