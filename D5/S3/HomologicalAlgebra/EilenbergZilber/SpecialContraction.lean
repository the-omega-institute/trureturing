/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/SpecialContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structural cancellation for the recursive normalized Eilenberg–Mac Lane homotopy. -/

import D5.S3.HomologicalAlgebra.EilenbergZilber.BisimplicialNormalized

/-! # Special contractions of the bisimplicial Eilenberg–Zilber homotopy -/

noncomputable section

open CategoryTheory
open AlgebraicTopology AlgebraicTopology.DoldKan CategoryTheory.Limits
open scoped Simplicial

namespace D5.S3.HomologicalAlgebra.EilenbergZilber
namespace BisimplicialObject

/-- An adjacent pair identified by a simplex map. -/
private def Repeats {n : ℕ} {a : SimplexCategory} (f : (⦋n⦌ : SimplexCategory) ⟶ a)
    (i : Fin n) : Prop :=
  f.toOrderHom i.castSucc = f.toOrderHom i.succ

private lemma Repeats.comp {n : ℕ} {a b : SimplexCategory}
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
private lemma hOp_comp_ordered_repeat {s n : ℕ} (l : OpLetter s n) (c : ℤ)
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

end BisimplicialObject
end D5.S3.HomologicalAlgebra.EilenbergZilber
