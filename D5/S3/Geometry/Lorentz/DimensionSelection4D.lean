/- GID: D5/S3/Geometry/Lorentz/DimensionSelection4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/DimensionSelection4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Algebraic curvature, Ricci and null-screen dimensions with the angular summability and chirality selection of dimension four. -/

import D5.S3.Geometry.Lorentz.WeylNullScreen
import Mathlib.Analysis.PSeries
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Sym.Card
import Mathlib.Order.Hom.PowersetCard

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.DimensionSelection4D

open scoped BigOperators
open Function Module

/-- Increasing coordinate tuples enumerate exterior basis elements. -/
abbrev Increasing (k D : ℕ) := Fin k ↪o Fin D

private instance (k D : ℕ) : Fintype (Increasing k D) :=
  Fintype.ofEquiv _ Set.powersetCard.ofFinEmbEquiv.symm
private theorem card_increasing (k D : ℕ) : Fintype.card (Increasing k D) = D.choose k := by
  rw [Fintype.card_congr Set.powersetCard.ofFinEmbEquiv, ← Nat.card_eq_fintype_card,
    Set.powersetCard.card, Nat.card_fin]

/-- A symmetric array stores one scalar for each unordered pair, including the diagonal. -/
abbrev SymForm (ι : Type*) := Sym2 ι → ℝ

def entry {ι : Type*} (A : SymForm ι) (i j : ι) : ℝ := A (Sym2.mk i j)
private theorem entry_comm {ι : Type*} (A : SymForm ι) (i j : ι) :
    entry A i j = entry A j i :=
  congrArg A (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))

private def pair {D : ℕ} (a b : Fin D) (h : a < b) : Increasing 2 D :=
  OrderEmbedding.ofStrictMono ![a, b] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact h | contradiction)

private def quad {D : ℕ} (a b c d : Fin D) (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) :
    Increasing 4 D :=
  OrderEmbedding.ofStrictMono ![a, b, c, d] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega)
private def pairOf {D : ℕ} (q : Increasing 4 D) (i j : Fin 4) (h : i < j) :
    Increasing 2 D := pair (q i) (q j) (q.strictMono h)

/-- The three pairings in the first Bianchi identity on an increasing quadruple. -/
private def pivot {D : ℕ} (q : Increasing 4 D) : Sym2 (Increasing 2 D) :=
  Sym2.mk (pairOf q 0 1 (by decide)) (pairOf q 2 3 (by decide))
private def cross {D : ℕ} (q : Increasing 4 D) : Sym2 (Increasing 2 D) :=
  Sym2.mk (pairOf q 0 2 (by decide)) (pairOf q 1 3 (by decide))
private def outer {D : ℕ} (q : Increasing 4 D) : Sym2 (Increasing 2 D) :=
  Sym2.mk (pairOf q 0 3 (by decide)) (pairOf q 1 2 (by decide))

/-- First Bianchi map on the symmetric form on exterior pairs. -/
def bianchiMap (D : ℕ) : SymForm (Increasing 2 D) →ₗ[ℝ] (Increasing 4 D → ℝ) where
  toFun R q := R (pivot q) - R (cross q) + R (outer q)
  map_add' R S := by funext q; simp only [Pi.add_apply]; ring
  map_smul' a R := by funext q; simp [mul_sub, mul_add]
private theorem pairOf_equal {D : ℕ} {q t : Increasing 4 D} {i j k l : Fin 4}
    {h : i < j} {h' : k < l} (e : pairOf q i j h = pairOf t k l h') :
    q i = t k ∧ q j = t l :=
  ⟨congrArg (fun p : Increasing 2 D => p 0) e,
    congrArg (fun p : Increasing 2 D => p 1) e⟩
private theorem pivot_injective (D : ℕ) : Injective (pivot (D := D)) := by
  intro q t h
  rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨h₀, h₁⟩ := pairOf_equal h₁
    obtain ⟨h₂, h₃⟩ := pairOf_equal h₂
    apply RelEmbedding.ext
    intro i
    fin_cases i <;> assumption
  · obtain ⟨_, h₁⟩ := pairOf_equal h₁
    obtain ⟨h₂, _⟩ := pairOf_equal h₂
    have hq := q.strictMono (show (1 : Fin 4) < 2 by decide)
    have ht := t.strictMono (show (0 : Fin 4) < 3 by decide)
    rw [h₁, h₂] at hq
    exact (lt_asymm ht hq).elim
private theorem pivot_separated {D : ℕ} (t : Increasing 4 D) {p q : Increasing 2 D}
    (h : Sym2.mk p q = pivot t) : p 1 < q 0 ∨ q 1 < p 0 := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (t.strictMono (show (1 : Fin 4) < 2 by decide))
  · exact Or.inr (t.strictMono (show (1 : Fin 4) < 2 by decide))
private theorem cross_ne_pivot {D : ℕ} (q t : Increasing 4 D) : cross q ≠ pivot t := by
  intro h
  exact (pivot_separated t h).elim
    (lt_asymm (q.strictMono (show (1 : Fin 4) < 2 by decide)))
    (lt_asymm (q.strictMono (show (0 : Fin 4) < 3 by decide)))
private theorem outer_ne_pivot {D : ℕ} (q t : Increasing 4 D) : outer q ≠ pivot t := by
  intro h
  exact (pivot_separated t h).elim
    (lt_asymm (q.strictMono (show (1 : Fin 4) < 3 by decide)))
    (lt_asymm (q.strictMono (show (0 : Fin 4) < 2 by decide)))

/-- Insert each coordinate at its unique consecutive pairing. -/
def bianchiSection (D : ℕ) : (Increasing 4 D → ℝ) →ₗ[ℝ] SymForm (Increasing 2 D) := by
  classical
  exact ∑ q, (LinearMap.proj q).smulRight (Pi.single (pivot q) (1 : ℝ))

theorem bianchi_right_inverse (D : ℕ) : RightInverse (bianchiSection D) (bianchiMap D) := by
  classical
  intro u
  funext q
  change bianchiSection D u (pivot q) - bianchiSection D u (cross q) +
    bianchiSection D u (outer q) = u q
  simp [bianchiSection, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, mul_ite,
    (pivot_injective D).eq_iff, cross_ne_pivot, outer_ne_pivot, eq_comm (a := q)]

/-- Symmetric pair arrays in the Bianchi kernel. -/
abbrev AlgebraicCurvature (D : ℕ) := LinearMap.ker (bianchiMap D)

private def orientLeft {D : ℕ} (a b : Fin D) : Option (Increasing 2 D × ℝ) :=
  if h : a < b then some (pair a b h, 1)
  else if h' : b < a then some (pair b a h', -1) else none

/-- The components of a symmetric pair array, extended with the two skew pair signs. -/
def component {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) : ℝ :=
  match orientLeft a b, orientLeft c d with
  | some (p, s), some (q, t) => s * t * entry R p q
  | _, _ => 0
private theorem component_ordered {D : ℕ} (R : SymForm (Increasing 2 D))
    {a b c d : Fin D} (h₁ : a < b) (h₂ : c < d) :
    component R a b c d = entry R (pair a b h₁) (pair c d h₂) := by
  simp [component, orientLeft, h₁, h₂]
private theorem component_swap₁ {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    component R b a c d = -component R a b c d := by
  rcases lt_trichotomy a b with h | rfl | h
  · have ha : orientLeft a b = some (pair a b h, 1) := by simp [orientLeft, h]
    have hb : orientLeft b a = some (pair a b h, -1) := by simp [orientLeft, h, h.asymm]
    cases hd : orientLeft c d with
    | none => simp [component, ha, hb, hd]
    | some q => rcases q with ⟨q, t⟩; simp [component, ha, hb, hd]
  · simp [component, orientLeft]
  · have ha : orientLeft b a = some (pair b a h, 1) := by simp [orientLeft, h]
    have hb : orientLeft a b = some (pair b a h, -1) := by simp [orientLeft, h, h.asymm]
    cases hd : orientLeft c d with
    | none => simp [component, ha, hb, hd]
    | some q => rcases q with ⟨q, t⟩; simp [component, ha, hb, hd]
private theorem component_exchange {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    component R a b c d = component R c d a b := by
  cases ha : orientLeft a b with
  | none => cases orientLeft c d <;> simp [component, ha]
  | some p =>
    rcases p with ⟨p, s⟩
    cases hb : orientLeft c d with
    | none => simp [component, ha, hb]
    | some q => rcases q with ⟨q, t⟩; simp [component, ha, hb, entry_comm R p q, mul_comm s t]
private theorem component_swap₂ {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    component R a b d c = -component R a b c d := by
  rw [component_exchange R a b d c, component_swap₁, component_exchange R a b c d]
private theorem component_repeated {D : ℕ} (R : SymForm (Increasing 2 D)) (a c d : Fin D) :
    component R a a c d = 0 := by
  simp [component, orientLeft]
private theorem component_add {D : ℕ} (R S : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    component (R + S) a b c d = component R a b c d + component S a b c d := by
  cases ha : orientLeft a b <;> cases hb : orientLeft c d <;>
    simp [component, ha, hb, entry, mul_add]
private theorem component_smul {D : ℕ} (r : ℝ) (R : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    component (r • R) a b c d = r * component R a b c d := by
  cases ha : orientLeft a b <;> cases hb : orientLeft c d <;>
    simp [component, ha, hb, entry, mul_left_comm]

private def bianchiValue {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) : ℝ :=
  component R a b c d - component R a c b d + component R a d b c
private theorem bianchi_swap₀₁ {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    bianchiValue R b a c d = -bianchiValue R a b c d := by
  unfold bianchiValue
  rw [component_swap₁ R a b c d, component_exchange R b c a d,
    component_exchange R b d a c]
  ring
private theorem bianchi_swap₁₂ {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    bianchiValue R a c b d = -bianchiValue R a b c d := by
  unfold bianchiValue
  rw [component_swap₂ R a d b c]
  ring
private theorem bianchi_swap₂₃ {D : ℕ} (R : SymForm (Increasing 2 D)) (a b c d : Fin D) :
    bianchiValue R a b d c = -bianchiValue R a b c d := by
  unfold bianchiValue
  rw [component_swap₂ R a b c d]
  ring

private theorem bianchi_swap_iff {D : ℕ} (R : SymForm (Increasing 2 D)) (f : Fin 4 → Fin D)
    (i j : Fin 4) :
    bianchiValue R (f (Equiv.swap i j 0)) (f (Equiv.swap i j 1))
      (f (Equiv.swap i j 2)) (f (Equiv.swap i j 3)) = 0
      ↔ bianchiValue R (f 0) (f 1) (f 2) (f 3) = 0 := by
  fin_cases i <;> fin_cases j <;> simp only [Equiv.swap_apply_def] <;> norm_num <;>
    first
    | rw [bianchi_swap₀₁ R (f 0) (f 1) (f 2) (f 3), neg_eq_zero]
    | rw [bianchi_swap₁₂ R (f 0) (f 1) (f 2) (f 3), neg_eq_zero]
    | rw [bianchi_swap₂₃ R (f 0) (f 1) (f 2) (f 3), neg_eq_zero]
    | rw [bianchi_swap₀₁ R (f 1) (f 2) (f 0) (f 3), neg_eq_zero,
        bianchi_swap₁₂ R (f 1) (f 0) (f 2) (f 3), neg_eq_zero,
        bianchi_swap₀₁ R (f 0) (f 1) (f 2) (f 3), neg_eq_zero]
    | rw [bianchi_swap₁₂ R (f 0) (f 2) (f 3) (f 1), neg_eq_zero,
        bianchi_swap₂₃ R (f 0) (f 2) (f 1) (f 3), neg_eq_zero,
        bianchi_swap₁₂ R (f 0) (f 1) (f 2) (f 3), neg_eq_zero]
    | rw [bianchi_swap₀₁ R (f 1) (f 3) (f 2) (f 0), neg_eq_zero,
        bianchi_swap₁₂ R (f 1) (f 2) (f 3) (f 0), neg_eq_zero,
        bianchi_swap₂₃ R (f 1) (f 2) (f 0) (f 3), neg_eq_zero,
        bianchi_swap₁₂ R (f 1) (f 0) (f 2) (f 3), neg_eq_zero,
        bianchi_swap₀₁ R (f 0) (f 1) (f 2) (f 3), neg_eq_zero]

/-- Checking the increasing quadruples imposes the full first Bianchi identity. -/
theorem bianchi_identity {D : ℕ} (R : AlgebraicCurvature D) (a b c d : Fin D) :
    component R.val a b c d - component R.val a c b d + component R.val a d b c = 0 := by
  let f : Fin 4 → Fin D := ![a, b, c, d]
  change bianchiValue R.val (f 0) (f 1) (f 2) (f 3) = 0
  have hp (σ : Equiv.Perm (Fin 4)) :
      bianchiValue R.val (f (σ 0)) (f (σ 1)) (f (σ 2)) (f (σ 3)) = 0 ↔
        bianchiValue R.val (f 0) (f 1) (f 2) (f 3) = 0 := by
    induction σ using Equiv.Perm.swap_induction_on' with
    | one => simp
    | mul_swap σ i j hne ih =>
      exact (bianchi_swap_iff R.val (f ∘ σ) i j).trans ih
  apply (hp (Tuple.sort f)).mp
  let g := f ∘ Tuple.sort f
  change bianchiValue R.val (g 0) (g 1) (g 2) (g 3) = 0
  have hm : Monotone g := Tuple.monotone_sort f
  obtain h₁ | h₁ := (hm (show (0 : Fin 4) ≤ 1 by decide)).eq_or_lt
  · have h := bianchi_swap₀₁ R.val (g 0) (g 1) (g 2) (g 3)
    rw [h₁] at h ⊢
    linarith
  obtain h₂ | h₂ := (hm (show (1 : Fin 4) ≤ 2 by decide)).eq_or_lt
  · have h := bianchi_swap₁₂ R.val (g 0) (g 1) (g 2) (g 3)
    rw [h₂] at h ⊢
    linarith
  obtain h₃ | h₃ := (hm (show (2 : Fin 4) ≤ 3 by decide)).eq_or_lt
  · have h := bianchi_swap₂₃ R.val (g 0) (g 1) (g 2) (g 3)
    rw [h₃] at h ⊢
    linarith
  let q := quad (g 0) (g 1) (g 2) (g 3) h₁ h₂ h₃
  have hz := congrFun (LinearMap.mem_ker.mp R.property) q
  unfold bianchiValue
  rw [component_ordered _ h₁ h₃, component_ordered _ (h₁.trans h₂) (h₂.trans h₃),
    component_ordered _ (h₁.trans (h₂.trans h₃)) h₂]
  exact hz
private theorem rank_split {U V : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ U] (f : U →ₗ[ℝ] V)
    (hf : Surjective f) : finrank ℝ f.ker + finrank ℝ V = finrank ℝ U := by
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, add_comm] at h
  exact h
private theorem two_choose (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  simpa [Nat.descFactorial_succ, Nat.mul_comm] using
    (Nat.descFactorial_eq_factorial_mul_choose n 2).symm
private theorem four_choose (n : ℕ) : 24 * n.choose 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  have h : Nat.factorial 4 = 24 := by decide
  simpa [h, Nat.descFactorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.descFactorial_eq_factorial_mul_choose n 4).symm
private theorem symForm_rank {ι : Type*} [Fintype ι] :
    finrank ℝ (SymForm ι) = (Fintype.card ι + 1).choose 2 := by
  classical
  rw [Module.finrank_fintype_fun_eq_card, Sym2.card]
private theorem curvature_rank_count (D : ℕ) :
    finrank ℝ (AlgebraicCurvature D) + D.choose 4 = (D.choose 2 + 1).choose 2 := by
  classical
  have h := rank_split (bianchiMap D) (bianchi_right_inverse D).surjective
  rw [Module.finrank_fintype_fun_eq_card, card_increasing, symForm_rank, card_increasing] at h
  exact h
private theorem curvature_rank_mul (D : ℕ) (hD : 3 ≤ D) :
    12 * finrank ℝ (AlgebraicCurvature D) = D ^ 2 * (D ^ 2 - 1) := by
  have h₁ := curvature_rank_count D
  have h₂ := two_choose D
  have h₃ := two_choose (D.choose 2 + 1)
  simp only [Nat.add_sub_cancel] at h₃
  have h₄ := four_choose D
  have hsq : 1 ≤ D ^ 2 := by nlinarith
  zify [show 1 ≤ D by omega, show 2 ≤ D by omega, hD, hsq] at h₁ h₂ h₃ h₄ ⊢
  apply (mul_right_inj' (show (2 : ℤ) ≠ 0 by decide)).mp
  linear_combination 24 * h₁ + 12 * h₃ - h₄ +
    3 * (2 * (D.choose 2 : ℤ) + (D : ℤ) * ((D : ℤ) - 1) + 2) * h₂

/-- The arbitrary-dimensional algebraic curvature dimension. -/
theorem finrank_algebraicCurvature (D : ℕ) (hD : 3 ≤ D) :
    finrank ℝ (AlgebraicCurvature D) = D ^ 2 * (D ^ 2 - 1) / 12 := by
  have h := curvature_rank_mul D hD
  omega

/-- Diagonal entries of the Lorentzian metric and its inverse. -/
def lorentzSign {D : ℕ} (i : Fin D) : ℝ := if i.val = 0 then -1 else 1
private theorem lorentzSign_mul {D : ℕ} (i : Fin D) : lorentzSign i * lorentzSign i = 1 := by
  unfold lorentzSign
  split <;> norm_num

/-- Lorentz metric in the standard coordinate frame. -/
def metric (D : ℕ) : SymForm (Fin D) :=
  Sym2.lift ⟨fun a b => if a = b then lorentzSign a else 0, by
    intro a b
    by_cases h : a = b <;> simp [h, eq_comm]⟩
private theorem metric_entry {D : ℕ} (a b : Fin D) :
    entry (metric D) a b = if a = b then lorentzSign a else 0 := rfl
private def metricTrace (D : ℕ) : SymForm (Fin D) →ₗ[ℝ] ℝ where
  toFun T := ∑ a, lorentzSign a * entry T a a
  map_add' T U := by simp [entry, mul_add, Finset.sum_add_distrib]
  map_smul' r T := by simp [entry, Finset.mul_sum, mul_left_comm]
private theorem metricTrace_metric (D : ℕ) : metricTrace D (metric D) = D := by
  change ∑ a : Fin D, lorentzSign a * entry (metric D) a a = _
  simp [metric_entry, lorentzSign_mul]

/-- Contraction of the first and third curvature arguments against the inverse metric. -/
def ricciMap (D : ℕ) : AlgebraicCurvature D →ₗ[ℝ] SymForm (Fin D) where
  toFun R := Sym2.lift ⟨fun b d => ∑ a, lorentzSign a * component R.val a b a d, by
    intro b d
    apply Finset.sum_congr rfl
    intro a _
    rw [component_exchange R.val a b a d]⟩
  map_add' R S := by
    ext z
    induction z using Sym2.ind with
    | _ b d =>
      change ∑ a, lorentzSign a * component (R.val + S.val) a b a d = _
      simp [component_add, mul_add, Finset.sum_add_distrib, Sym2.lift_mk]
  map_smul' r R := by
    ext z
    induction z using Sym2.ind with
    | _ b d =>
      change ∑ a, lorentzSign a * component (r • R.val) a b a d = _
      simp [component_smul, Finset.mul_sum, Sym2.lift_mk, mul_left_comm]
private theorem ricci_entry {D : ℕ} (R : AlgebraicCurvature D) (b d : Fin D) :
    entry (ricciMap D R) b d = ∑ a, lorentzSign a * component R.val a b a d := rfl

private def knValue {ι : Type*} (G T : SymForm ι) (a b c d : ι) : ℝ :=
  entry G a c * entry T b d - entry G a d * entry T b c -
    entry G b c * entry T a d + entry G b d * entry T a c
private theorem kn_swap₁ {ι : Type*} (G T : SymForm ι) (a b c d : ι) :
    knValue G T b a c d = -knValue G T a b c d := by unfold knValue; ring
private theorem kn_swap₂ {ι : Type*} (G T : SymForm ι) (a b c d : ι) :
    knValue G T a b d c = -knValue G T a b c d := by unfold knValue; ring
private theorem kn_exchange {ι : Type*} (G T : SymForm ι) (a b c d : ι) :
    knValue G T a b c d = knValue G T c d a b := by
  unfold knValue
  rw [entry_comm G c a, entry_comm G c b, entry_comm G d a, entry_comm G d b,
    entry_comm T d b, entry_comm T d a, entry_comm T c b, entry_comm T c a]
  ring

private def knArray {D : ℕ} (G T : SymForm (Fin D)) : SymForm (Increasing 2 D) :=
  Sym2.lift ⟨fun p q => knValue G T (p 0) (p 1) (q 0) (q 1),
    fun p q => kn_exchange G T (p 0) (p 1) (q 0) (q 1)⟩

private theorem component_knArray {D : ℕ} (G T : SymForm (Fin D)) (a b c d : Fin D) :
    component (knArray G T) a b c d = knValue G T a b c d := by
  wlog ha : a ≤ b generalizing a b
  · rw [← neg_neg (component _ a b c d), ← component_swap₁, kn_swap₁ G T b a c d]
    rw [this b a (le_of_not_ge ha)]
  wlog hc : c ≤ d generalizing c d
  · rw [← neg_neg (component _ a b c d), ← component_swap₂, kn_swap₂ G T a b d c]
    rw [this d c (le_of_not_ge hc)]
  obtain rfl | hab := ha.eq_or_lt
  · rw [component_repeated]
    unfold knValue
    ring
  obtain rfl | hcd := hc.eq_or_lt
  · rw [component_exchange, component_repeated]
    unfold knValue
    ring
  exact component_ordered _ hab hcd

/-- Kulkarni–Nomizu multiplication by a symmetric form in exterior-pair coordinates. -/
def kulkarniNomizu {D : ℕ} (G : SymForm (Fin D)) :
    SymForm (Fin D) →ₗ[ℝ] AlgebraicCurvature D where
  toFun T := ⟨knArray G T, by
    apply LinearMap.mem_ker.mpr
    funext q
    change knValue G T (q 0) (q 1) (q 2) (q 3) -
      knValue G T (q 0) (q 2) (q 1) (q 3) +
      knValue G T (q 0) (q 3) (q 1) (q 2) = 0
    unfold knValue
    rw [entry_comm T (q 2) (q 1), entry_comm T (q 3) (q 2),
      entry_comm T (q 3) (q 1), entry_comm G (q 2) (q 1),
      entry_comm G (q 3) (q 2), entry_comm G (q 3) (q 1)]
    ring⟩
  map_add' T U := by
    apply Subtype.ext
    funext z
    induction z using Sym2.ind with
    | _ p q => simp [knArray, knValue, entry, mul_add, Sym2.lift_mk]; ring
  map_smul' r T := by
    apply Subtype.ext
    funext z
    induction z using Sym2.ind with
    | _ p q => simp [knArray, knValue, entry, Sym2.lift_mk]; ring

private theorem ricci_kn {D : ℕ} (T : SymForm (Fin D)) :
    ricciMap D (kulkarniNomizu (metric D) T) =
      ((D : ℝ) - 2) • T + metricTrace D T • metric D := by
  classical
  funext z
  induction z using Sym2.ind with
  | _ b d =>
    change entry (ricciMap D (kulkarniNomizu (metric D) T)) b d = _
    rw [ricci_entry]
    change (∑ a, lorentzSign a * component (knArray (metric D) T) a b a d) = _
    simp only [component_knArray, knValue, metric_entry, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hd : (∑ a, lorentzSign a * ((if a = d then lorentzSign a else 0) * entry T b a)) =
        entry T b d := by
      simp [mul_ite, ite_mul, lorentzSign_mul, ← mul_assoc]
    have hb : (∑ a, lorentzSign a * ((if b = a then lorentzSign b else 0) * entry T a d)) =
        entry T b d := by
      simp [mul_ite, ite_mul, lorentzSign_mul, ← mul_assoc]
    rw [hd, hb]
    simp only [ite_true, ← mul_assoc, lorentzSign_mul, one_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change _ + _ = ((D : ℝ) - 2) * entry T b d +
      (∑ a, lorentzSign a * entry T a a) * entry (metric D) b d
    rw [metric_entry, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro a _
      ring
private def schouten (D : ℕ) : SymForm (Fin D) →ₗ[ℝ] SymForm (Fin D) :=
  ((D : ℝ) - 2)⁻¹ • (LinearMap.id -
    (2 * ((D : ℝ) - 1))⁻¹ • (metricTrace D).smulRight (metric D))

/-- The Kulkarni–Nomizu lift of the Schouten correction. -/
def ricciSection (D : ℕ) : SymForm (Fin D) →ₗ[ℝ] AlgebraicCurvature D :=
  (kulkarniNomizu (metric D)).comp (schouten D)
private theorem schouten_apply (D : ℕ) (T : SymForm (Fin D)) :
    schouten D T = ((D : ℝ) - 2)⁻¹ •
      (T - ((2 * ((D : ℝ) - 1))⁻¹ * metricTrace D T) • metric D) := by
  simp [schouten, smul_smul]
private theorem schouten_trace (D : ℕ) (hD : 3 ≤ D) (T : SymForm (Fin D)) :
    metricTrace D (schouten D T) = (2 * ((D : ℝ) - 1))⁻¹ * metricTrace D T := by
  have h₁ : (D : ℝ) - 1 ≠ 0 := by exact_mod_cast (show (D : ℤ) - 1 ≠ 0 by omega)
  have h₂ : (D : ℝ) - 2 ≠ 0 := by exact_mod_cast (show (D : ℤ) - 2 ≠ 0 by omega)
  rw [schouten_apply, map_smul, map_sub, map_smul, metricTrace_metric]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem ricci_right_inverse (D : ℕ) (hD : 3 ≤ D) :
    RightInverse (ricciSection D) (ricciMap D) := by
  intro T
  change ricciMap D (kulkarniNomizu (metric D) (schouten D T)) = T
  rw [ricci_kn, schouten_trace D hD, schouten_apply, smul_smul]
  have h₂ : (D : ℝ) - 2 ≠ 0 := by exact_mod_cast (show (D : ℤ) - 2 ≠ 0 by omega)
  rw [mul_inv_cancel₀ h₂, one_smul, sub_add_cancel]

/-- Algebraic Weyl curvature is the Ricci kernel. -/
abbrev Weyl (D : ℕ) := LinearMap.ker (ricciMap D)
theorem finrank_symmetricRicci (D : ℕ) :
    finrank ℝ (SymForm (Fin D)) = D * (D + 1) / 2 := by
  rw [symForm_rank, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]
private theorem weyl_rank_mul (D : ℕ) (hD : 3 ≤ D) :
    12 * finrank ℝ (Weyl D) = D * (D + 1) * (D + 2) * (D - 3) := by
  classical
  have hr := rank_split (ricciMap D) (ricci_right_inverse D hD).surjective
  have hc := curvature_rank_mul D hD
  have hs := two_choose (D + 1)
  rw [← Fintype.card_fin D, ← symForm_rank] at hs
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at hs
  have hsq : 1 ≤ D ^ 2 := by nlinarith
  zify [hD, hsq] at hr hc hs ⊢
  linear_combination hc + 12 * hr - 6 * hs

/-- The dimension of the Weyl curvature space, including the zero-dimensional boundary. -/
theorem finrank_weyl (D : ℕ) (hD : 3 ≤ D) :
    finrank ℝ (Weyl D) = D * (D + 1) * (D + 2) * (D - 3) / 12 := by
  have h := weyl_rank_mul D hD
  omega
theorem weylDim_pos_iff (D : ℕ) (hD : 3 ≤ D) :
    0 < finrank ℝ (Weyl D) ↔ 4 ≤ D := by
  have h := weyl_rank_mul D hD
  rw [← Nat.mul_pos_iff_of_pos_left (show 0 < 12 by decide), h]
  simp only [Nat.pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]
  omega

private def screenTrace (n : ℕ) : SymForm (Fin n) →ₗ[ℝ] ℝ where
  toFun A := ∑ i, entry A i i
  map_add' _ _ := by simp [entry, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [entry, Finset.mul_sum]
private def screenMetric (n : ℕ) : SymForm (Fin n) :=
  Sym2.lift ⟨fun i j => if i = j then 1 else 0, fun i j => by simp [eq_comm]⟩

/-- Symmetric trace-free tensors on the transverse Euclidean screen. -/
abbrev ScreenSTF (D : ℕ) := LinearMap.ker (screenTrace (D - 2))

/-- The number of independent transverse trace-free components. -/
def screenDim (D : ℕ) : ℕ := D * (D - 3) / 2
theorem finrank_screenSTF (D : ℕ) (hD : 3 ≤ D) :
    finrank ℝ (ScreenSTF D) = screenDim D := by
  let n := D - 2
  have hn : 0 < n := by dsimp [n]; omega
  have htrace : screenTrace n (screenMetric n) = n := by
    change (∑ i : Fin n, if i = i then (1 : ℝ) else 0) = n
    simp
  have hs : Surjective (screenTrace n) := by
    intro x
    refine ⟨(x / (n : ℝ)) • screenMetric n, ?_⟩
    rw [map_smul, htrace, smul_eq_mul, div_mul_cancel₀]
    exact_mod_cast hn.ne'
  have h := rank_split (screenTrace n) hs
  rw [Module.finrank_self] at h
  have hm := two_choose (n + 1)
  rw [← Fintype.card_fin n, ← symForm_rank] at hm
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at hm
  have hmul : 2 * finrank ℝ (ScreenSTF D) = D * (D - 3) := by
    change 2 * finrank ℝ (screenTrace n).ker = _
    dsimp [n] at h hm ⊢
    zify [hD, show 2 ≤ D by omega] at h hm ⊢
    linear_combination hm + 2 * h
  unfold screenDim
  omega
theorem screenDim_pos_iff (D : ℕ) : 0 < screenDim D ↔ 4 ≤ D := by
  unfold screenDim
  constructor
  · intro h
    by_contra! hD
    have : D - 3 = 0 := by omega
    simp [this] at h
  · intro hD
    have h₁ : 1 ≤ D - 3 := by omega
    have h₂ : 4 * 1 ≤ D * (D - 3) := Nat.mul_le_mul hD h₁
    omega

/-- The Hodge complement of degree two has degree two exactly in dimension four. -/
theorem hodge_two_form_degree_iff (D : ℕ) : D - 2 = 2 ↔ D = 4 := by omega
def angularMode (D ℓ : ℕ) : ℝ := ((ℓ : ℝ) + 1) ^ ((D : ℤ) - 7)
theorem summable_angularMode_iff (D : ℕ) :
    Summable (fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ ((D : ℤ) - 7)) ↔ D ≤ 5 := by
  let p : ℝ := ((D : ℤ) - 7 : ℤ)
  have hs := summable_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) ^ p)
  rw [Real.summable_nat_rpow] at hs
  simp only [p, Nat.cast_add, Nat.cast_one, Real.rpow_intCast] at hs
  rw [hs]
  exact_mod_cast (show (D : ℤ) - 7 < -1 ↔ D ≤ 5 by omega)

theorem angular_trace_summable_iff_of_eventually_comparable (D : ℕ) (t : ℕ → ℝ)
    (ht : ∀ ℓ, 0 ≤ t ℓ) {a b : ℝ} (ha : 0 < a)
    (h : ∀ᶠ ℓ in Filter.atTop, a * angularMode D ℓ ≤ t ℓ ∧ t ℓ ≤ b * angularMode D ℓ) :
    Summable t ↔ D ≤ 5 := by
  rw [← summable_angularMode_iff]
  change Summable t ↔ Summable (angularMode D)
  constructor
  · intro hs
    apply (hs.mul_left a⁻¹).of_norm_bounded_eventually_nat
    filter_upwards [h] with ℓ hℓ
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold angularMode; positivity)]
    exact (le_inv_mul_iff₀ ha).2 hℓ.1
  · intro hs
    apply (hs.mul_left b).of_norm_bounded_eventually_nat
    filter_upwards [h] with ℓ hℓ
    rw [Real.norm_eq_abs, abs_of_nonneg (ht ℓ)]
    exact hℓ.2

theorem unique_dimension_four_of_weyl_modular_chiral (D : ℕ) :
    (0 < screenDim D ∧
      Summable (fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ ((D : ℤ) - 7)) ∧ Even D) ↔ D = 4 := by
  rw [screenDim_pos_iff, summable_angularMode_iff]
  constructor
  · rintro ⟨hl, hu, m, hm⟩
    omega
  · rintro rfl
    exact ⟨le_rfl, by decide, ⟨2, rfl⟩⟩
theorem unique_dimension_four_of_weyl_modular_hodge (D : ℕ) :
    (0 < screenDim D ∧
      Summable (fun ℓ : ℕ => ((ℓ : ℝ) + 1) ^ ((D : ℤ) - 7)) ∧ D - 2 = 2) ↔ D = 4 := by
  rw [screenDim_pos_iff, summable_angularMode_iff, hodge_two_form_degree_iff]
  omega

private def screenIndex {n : ℕ} (i : Fin n) : Fin (n + 2) := i.succ.succ

/-- In the standard Lorentz frame the generator is the sum of the first two basis vectors. -/
def screenTide {n : ℕ} (R : AlgebraicCurvature (n + 2)) (i j : Fin n) : ℝ :=
  let C := component R.val
  let a := screenIndex i
  let b := screenIndex j
  C 0 a 0 b + C 0 a 1 b + C 1 a 0 b + C 1 a 1 b
private theorem screenTide_trace {n : ℕ} (R : AlgebraicCurvature (n + 2)) :
    (∑ i, screenTide R i i) =
      entry (ricciMap _ R) 0 0 + entry (ricciMap _ R) 0 1 +
      entry (ricciMap _ R) 1 0 + entry (ricciMap _ R) 1 1 := by
  have hs : (0 : Fin (n + 1)).succ = 1 := Fin.succ_zero_eq_one'
  have hrev (i : Fin n) (a b : Fin (n + 2)) :
      component R.val i.succ.succ a i.succ.succ b =
        component R.val a i.succ.succ b i.succ.succ := by
    rw [component_swap₁, component_swap₂, neg_neg]
  have hcancel : component R.val 1 0 1 0 = component R.val 0 1 0 1 := by
    rw [component_swap₁, component_swap₂, neg_neg]
  have hzero (a b c : Fin (n + 2)) : component R.val a b c c = 0 := by
    rw [component_exchange, component_repeated]
  simp only [screenTide, screenIndex, Finset.sum_add_distrib, ricci_entry, Fin.sum_univ_succ,
    lorentzSign, Fin.val_zero, Fin.val_succ, Nat.succ_ne_zero, ite_true, ite_false,
    one_mul, neg_one_mul, hs, component_repeated, hzero, hrev, hcancel]
  ring
private theorem screenTide_lift {n : ℕ} (T : SymForm (Fin (n + 2))) (i j : Fin n) :
    screenTide (kulkarniNomizu (metric _) T) i j =
      (if i = j then 1 else 0) * (entry T 0 0 + entry T 0 1 + entry T 1 0 + entry T 1 1) := by
  have comp (a b c d : Fin (n + 2)) :
      component ((kulkarniNomizu (metric _) T).val) a b c d = knValue (metric _) T a b c d :=
    component_knArray _ _ _ _ _ _
  simp only [screenTide, comp, knValue, metric_entry, screenIndex]
  have h₀ (a : Fin n) : (0 : Fin (n + 2)) ≠ a.succ.succ := by simp [← Fin.val_ne_iff]
  have h₁ (a : Fin n) : (1 : Fin (n + 2)) ≠ a.succ.succ := by
    simp [← Fin.val_ne_iff]
  simp [h₀, h₁, Ne.symm (h₀ _), Ne.symm (h₁ _), lorentzSign]
  split <;> ring

/-- Subtracting the screen trace gives the Weyl tide in the standard null frame. -/
theorem screen_tide_weyl_invariance {n : ℕ} (hn : 0 < n)
    (R : AlgebraicCurvature (n + 2)) (i j : Fin n) :
    screenTide R i j - (if i = j then 1 else 0) * (∑ a, screenTide R a a) / n =
      screenTide (R - ricciSection _ (ricciMap _ R)) i j := by
  have h : 3 ≤ n + 2 := by omega
  let L := ricciSection _ (ricciMap _ R)
  have hw : ricciMap _ (R - L) = 0 := by
    rw [map_sub, ricci_right_inverse _ h (ricciMap _ R), sub_self]
  have ha (a b : Fin n) : screenTide R a b =
      screenTide (R - L) a b + screenTide L a b := by
    conv_lhs => rw [← sub_add_cancel R L]
    simp only [screenTide, AddMemClass.coe_add, component_add]
    ring
  have ht : (∑ a, screenTide (R - L) a a) = 0 := by simp [screenTide_trace, hw, entry]
  let T := schouten _ (ricciMap _ R)
  let t := entry T 0 0 + entry T 0 1 + entry T 1 0 + entry T 1 1
  have hl (a b : Fin n) : screenTide L a b = (if a = b then 1 else 0) * t :=
    screenTide_lift T a b
  have hr : (∑ a, screenTide R a a) = (n : ℝ) * t := by
    simp only [ha, Finset.sum_add_distrib, ht, zero_add, hl, ite_true, one_mul]
    simp [nsmul_eq_mul]
  rw [hr, ha i j, hl i j]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

/-- The dimensions agree with the oriented four-dimensional curvature and Weyl spaces. -/
theorem four_dimensional_compatibility :
    finrank ℝ (AlgebraicCurvature 4) = finrank ℝ WeylNullScreen.AlgebraicCurvature4 ∧
    finrank ℝ (Weyl 4) = finrank ℝ WeylNullScreen.Weyl4 ∧ finrank ℝ (ScreenSTF 4) = 2 := by
  rw [WeylNullScreen.finrank_algebraicCurvature4, WeylNullScreen.finrank_weyl4,
    finrank_algebraicCurvature 4 (by decide), finrank_weyl 4 (by decide),
    finrank_screenSTF 4 (by decide)]
  decide

private def oldPair (p : WeylNullScreen.PairIndex) : Fin 4 × Fin 4 :=
  match p with
  | .inl i => (0, i.succ)
  | .inr i => (![2, 3, 1] i, ![3, 1, 2] i)
private def oldMatrix (R : AlgebraicCurvature 4) :
    Matrix WeylNullScreen.PairIndex WeylNullScreen.PairIndex ℝ :=
  fun p q => component R.val (oldPair p).1 (oldPair p).2 (oldPair q).1 (oldPair q).2

/-- Read the four-dimensional array in the oriented pair basis of `WeylNullScreen`. -/
def curvature4 (R : AlgebraicCurvature 4) : WeylNullScreen.AlgebraicCurvature4 :=
  ⟨oldMatrix R, fun _ _ => component_exchange _ _ _ _ _, by
    change Matrix.trace (Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) ℝ) 1 1 0 *
      oldMatrix R) = 0
    have h := bianchi_identity R 0 1 2 3
    have h31 := (component_exchange R.val 3 1 0 2).trans (component_swap₂ R.val 0 2 1 3)
    simp [Matrix.trace, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
      Fin.sum_univ_succ, Matrix.one_apply, oldMatrix, oldPair, h31,
      component_exchange R.val 2 3 0 1, component_exchange R.val 1 2 0 3,
      component_swap₂ R.val 0 2 1 3]
    linarith⟩
theorem curvature4_ricci (R : AlgebraicCurvature 4) (i j : Fin 4) :
    WeylNullScreen.ricci (curvature4 R) i j = entry (ricciMap 4 R) i j := by
  let A := oldMatrix R
  let E (i j : Fin 3) := A (.inl i) (.inl j)
  let M (i j : Fin 3) := A (.inl i) (.inr j)
  let S (i j : Fin 3) := A (.inr i) (.inr j)
  let t := E 0 0 + E 1 1 + E 2 2
  let x := M 1 2 - M 2 1
  let y := M 2 0 - M 0 2
  let z := M 0 1 - M 1 0
  change (!![t, x, y, z;
      x, -E 0 0 + S 1 1 + S 2 2, -E 0 1 - S 0 1, -E 0 2 - S 0 2;
      y, -E 0 1 - S 0 1, -E 1 1 + S 0 0 + S 2 2, -E 1 2 - S 1 2;
      z, -E 0 2 - S 0 2, -E 1 2 - S 1 2, -E 2 2 + S 0 0 + S 1 1] : Matrix _ _ ℝ) i j = _
  have hn (a b c : Fin 4) : component R.val a b c c = 0 := by
    rw [component_exchange, component_repeated]
  fin_cases i <;> fin_cases j <;> rw [ricci_entry] <;>
    simp [A, E, M, S, t, x, y, z, oldMatrix, oldPair, lorentzSign, Fin.sum_univ_succ,
      component_repeated, hn] <;> norm_num [component, orientLeft] <;> grind only [entry_comm]

/-- The oriented curvature map restricts to the existing Weyl space. -/
def weyl4 (R : Weyl 4) : WeylNullScreen.Weyl4 :=
  ⟨curvature4 R.val, LinearMap.mem_ker.mpr (by
    ext i j
    rw [curvature4_ricci, LinearMap.mem_ker.mp R.property]
    rfl)⟩


end D5.S3.Geometry.Lorentz.DimensionSelection4D
