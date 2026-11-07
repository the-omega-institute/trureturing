/- GID: D5/S3/Geometry/CoefficientBodies/ConvexRankOneRulings
   generality: G
   mirror-B: D5/B/S3/Geometry/CoefficientBodies/ConvexRankOneRulings
   mirror-E: none(waiver:arbitrary-pointwise-coefficient-body)
   anchors: []
   utility: none
   digest: Whole convex families of deficient two-column coefficient matrices have one common factor. -/

import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic

/-!
Real coefficient bodies with literal pointwise inequalities. Labels are ordered
0, 1, 3, B; Fin 2 coordinates 0, 1 denote radical columns 1, 2. Matrix.rank is
the dimension of the range of mulVecLin, not a definition by vanishing minors.
The rank and dimension interfaces are reused from the pinned Mathlib source.
The common-factor argument applies to the entire family, including empty and
all-zero families, without a chosen ruling among its hypotheses.

The generality is algebraic, not a bounded enumeration, checker, numerical
reduction or certified finite instance. Determinant expansions, factor choices
and rank interfaces below are consumed proof organization, not content claims.
-/

noncomputable section
open Matrix Set
open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings

set_option backward.isDefEq.respectTransparency.types false in
inductive Label where
  | zero | one | three | B
  deriving DecidableEq, Fintype

abbrev Coeff (d : ℕ) := Matrix Label (Fin d) ℝ

def H : Set (Label → ℝ) := {c | ∑ y, c y = 0}

def ZeroSum {d : ℕ} (A : Coeff d) : Prop := ∀ j, ∑ y, A y j = 0

/-- Arbitrary point set; inequalities hold at each point, without an a.e. quotient. -/
def body {X : Type*} {d : ℕ} (b : Label → X → ℝ) (r : Fin d → X → ℝ) :
    Set (Coeff d) :=
  {A | ZeroSum A ∧ ∀ y x, 0 ≤ b y x + ∑ j, A y j * r j x}

def blend {d : ℕ} (θ : ℝ) (A B : Coeff d) : Coeff d := θ • A + (1 - θ) • B

def minor (A : Coeff 2) (i k : Label) (j l : Fin 2) : ℝ :=
  (A.submatrix ![i, k] ![j, l]).det

def wedge {I : Type*} (u s : I → ℝ) (i k : I) : ℝ := u i * s k - u k * s i

def Parallel {I : Type*} (u s : I → ℝ) : Prop := ∀ i k, wedge u s i k = 0

def Transverse (u s : Label → ℝ) (v t : Fin 2 → ℝ) : Prop :=
  ¬ Parallel u s ∧ ¬ Parallel v t

def Rulings (C : Set (Coeff 2)) : Prop :=
  (∃ c ∈ H, c ≠ 0 ∧ ∀ A ∈ C, ∃ z, A = vecMulVec c z) ∨
  (∃ w : Fin 2 → ℝ, w ≠ 0 ∧ ∀ A ∈ C, ∃ v ∈ H, A = vecMulVec v w)

/-- Intrinsic pair predicate; every factor is nonzero and both endpoints have actual rank one. -/
def TransversePair (A B : Coeff 2) : Prop :=
  A ≠ 0 ∧ B ≠ 0 ∧ A.rank = 1 ∧ B.rank = 1 ∧
  ∃ u ∈ H, ∃ s ∈ H, ∃ v t : Fin 2 → ℝ,
    u ≠ 0 ∧ s ≠ 0 ∧ v ≠ 0 ∧ t ≠ 0 ∧
    A = vecMulVec u v ∧ B = vecMulVec s t ∧ Transverse u s v t

private theorem nonzero_entry {I J : Type*} {A : Matrix I J ℝ} (h : A ≠ 0) :
    ∃ i j, A i j ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  ext i j
  exact hn i j

private theorem rank_pos {d : ℕ} {A : Coeff d} (h : A ≠ 0) : 0 < A.rank := by
  obtain ⟨i, j, hij⟩ := nonzero_entry h
  let M : Matrix (Fin 1) (Fin 1) ℝ := A.submatrix (fun _ => i) (fun _ => j)
  have hd : M.det ≠ 0 := by simpa [M, Matrix.det_fin_one] using hij
  have hr := Matrix.rank_of_det_ne_zero hd
  have hle := A.rank_submatrix_le (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
  have : M.rank = 1 := by simpa using hr
  change M.rank ≤ A.rank at hle
  omega

/-- The pinned one-dimensional range theorem supplies factors; no upstream transplant. -/
private theorem factors {d : ℕ} (A : Coeff d) (h : A.rank ≤ 1) :
    ∃ u : Label → ℝ, ∃ v : Fin d → ℝ, A = vecMulVec u v := by
  obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := ℝ)
    (V := LinearMap.range A.mulVecLin)).mp h
  have hcol (j : Fin d) : A.col j ∈ LinearMap.range A.mulVecLin :=
    ⟨Pi.single j 1, A.mulVec_single_one j⟩
  choose v hv using fun j => hu ⟨A.col j, hcol j⟩
  refine ⟨u.val, v, ?_⟩
  ext i j
  have he := congrArg (fun z : LinearMap.range A.mulVecLin => z.val i) (hv j)
  simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, col_apply,
    vecMulVec_apply, mul_comm] using he.symm

private theorem zero_sum_factors {d : ℕ} (A : Coeff d)
    (hA : A ≠ 0) (hz : ZeroSum A) (hr : A.rank ≤ 1) :
    ∃ u ∈ H, ∃ v : Fin d → ℝ, u ≠ 0 ∧ v ≠ 0 ∧ A = vecMulVec u v := by
  obtain ⟨u, v, huv⟩ := factors A hr
  have hu : u ≠ 0 := by
    intro h
    apply hA
    rw [huv, h]
    ext i j
    simp [vecMulVec_apply]
  have hv : v ≠ 0 := by
    intro h
    apply hA
    rw [huv, h]
    ext i j
    simp [vecMulVec_apply]
  have hv' : ∃ j, v j ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hv (funext hh)
  obtain ⟨j, hj⟩ := hv'
  have hs : (∑ y, u y) * v j = 0 := by
    simpa only [huv, vecMulVec_apply, ← Finset.sum_mul] using hz j
  exact ⟨u, (mul_eq_zero.mp hs).resolve_right hj, v, hu, hv, huv⟩

private theorem minor_eq (A : Coeff 2) (i k : Label) (j l : Fin 2) :
    minor A i k j l = A i j * A k l - A i l * A k j := by
  simp [minor, Matrix.det_fin_two]

/-- Exact actual-rank/minor interface for rectangular real two-column matrices. -/
private theorem rank_le_one_iff_minors (A : Coeff 2) :
    A.rank ≤ 1 ↔ ∀ i k j l, minor A i k j l = 0 := by
  constructor
  · intro h
    obtain ⟨u, v, rfl⟩ := factors A h
    intro i k j l
    simp only [minor_eq, vecMulVec_apply]
    ring
  · intro h
    by_cases hz : A = 0
    · simp [hz]
    obtain ⟨i, j, hij⟩ := nonzero_entry hz
    have he : A = vecMulVec (fun k => A k j) (fun l => A i l / A i j) := by
      ext k l
      have hh := h i k j l
      rw [minor_eq] at hh
      simp only [vecMulVec_apply]
      calc
        A k l = (A k j * A i l) / A i j :=
          (eq_div_iff hij).2 (by nlinarith only [hh])
        _ = A k j * (A i l / A i j) := by ring
    rw [he]
    exact Matrix.rank_vecMulVec_le _ _

private theorem rank_two_iff_minor (A : Coeff 2) :
    A.rank = 2 ↔ ∃ i k j l, minor A i k j l ≠ 0 := by
  have hb : A.rank ≤ 2 := by simpa using A.rank_le_card_width
  have he := rank_le_one_iff_minors A
  constructor
  · intro h
    by_contra hh
    push_neg at hh
    have := he.mpr hh
    omega
  · rintro ⟨i, k, j, l, h⟩
    have hn : ¬ A.rank ≤ 1 := fun hr => h (he.mp hr i k j l)
    omega

private theorem parallel_symm {I : Type*} {u s : I → ℝ} (h : Parallel u s) :
    Parallel s u := by
  intro i k
  have hh := h i k
  dsimp [wedge] at *
  nlinarith only [hh]

private theorem parallel_iff_scalar {I : Type*} (u s : I → ℝ) (hu : u ≠ 0) :
    Parallel u s ↔ ∃ a : ℝ, s = a • u := by
  constructor
  · intro h
    have hp : ∃ i, u i ≠ 0 := by
      by_contra hh
      push_neg at hh
      exact hu (funext hh)
    obtain ⟨i, hi⟩ := hp
    refine ⟨s i / u i, ?_⟩
    ext k
    have hh := h i k
    dsimp [wedge] at hh
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      s k = (s i * u k) / u i := (eq_div_iff hi).2 (by nlinarith only [hh])
      _ = (s i / u i) * u k := by ring
  · rintro ⟨a, rfl⟩ i k
    simp only [wedge, Pi.smul_apply, smul_eq_mul]
    ring

private theorem wedge_blend (θ : ℝ) (u s : Label → ℝ) (v t : Fin 2 → ℝ)
    (i k : Label) (j l : Fin 2) :
    minor (blend θ (vecMulVec u v) (vecMulVec s t)) i k j l =
      θ * (1 - θ) * wedge u s i k * wedge v t j l := by
  simp only [minor_eq, blend, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, vecMulVec_apply, wedge]
  ring

private theorem rank_blend_iff (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < 1)
    (u s : Label → ℝ) (v t : Fin 2 → ℝ) :
    (blend θ (vecMulVec u v) (vecMulVec s t)).rank = 2 ↔ Transverse u s v t := by
  rw [rank_two_iff_minor]
  have hc : θ * (1 - θ) ≠ 0 := ne_of_gt (mul_pos hθ (sub_pos.mpr hθ'))
  constructor
  · rintro ⟨i, k, j, l, h⟩
    rw [wedge_blend] at h
    exact ⟨fun hp => h (by rw [hp i k]; ring),
      fun hp => h (by rw [hp j l]; ring)⟩
  · rintro ⟨hu, hv⟩
    unfold Parallel at hu hv
    push_neg at hu hv
    obtain ⟨i, k, hi⟩ := hu
    obtain ⟨j, l, hj⟩ := hv
    exact ⟨i, k, j, l, by rw [wedge_blend]; exact mul_ne_zero (mul_ne_zero hc hi) hj⟩

private theorem body_convex {X : Type*} {d : ℕ}
    (b : Label → X → ℝ) (r : Fin d → X → ℝ) : Convex ℝ (body b r) := by
  intro A hA B hB a c ha hc hac
  constructor
  · intro j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hA.1 j, hB.1 j]
    ring
  · intro y x
    have he : b y x + ∑ j, (a • A + c • B) y j * r j x =
        a * (b y x + ∑ j, A y j * r j x) +
        c * (b y x + ∑ j, B y j * r j x) := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      linear_combination -(b y x) * hac
    rw [he]
    exact add_nonneg (mul_nonneg ha (hA.2 y x)) (mul_nonneg hc (hB.2 y x))

private theorem rulings_small (C : Set (Coeff 2)) (h : Rulings C) :
    ∀ A ∈ C, A.rank ≤ 1 := by
  rcases h with ⟨c, _, _, h⟩ | ⟨w, _, h⟩
  · intro A hA
    obtain ⟨z, rfl⟩ := h A hA
    exact Matrix.rank_vecMulVec_le _ _
  · intro A hA
    obtain ⟨v, _, rfl⟩ := h A hA
    exact Matrix.rank_vecMulVec_le _ _

/-- The substantive whole-family step: midpoint compatibility forces a global factor. -/
private theorem common_factor (C : Set (Coeff 2))
    (hz : ∀ A ∈ C, ZeroSum A) (hr : ∀ A ∈ C, A.rank ≤ 1)
    (hm : ∀ A ∈ C, ∀ B ∈ C, (blend (1 / 2) A B).rank ≤ 1) : Rulings C := by
  classical
  by_cases hall : ∀ A ∈ C, A = 0
  · left
    let c : Label → ℝ := fun y => match y with
      | .zero => 1 | .one => -1 | .three => 0 | .B => 0
    have hc : c ∈ H := by
      have he : (Finset.univ : Finset Label) = {.zero, .one, .three, .B} := by
        ext y
        cases y <;> simp
      change ∑ y, c y = 0
      rw [he]
      norm_num [c]
    have hc' : c ≠ 0 := by
      intro he
      have := congrFun he Label.zero
      norm_num [c] at this
    refine ⟨c, hc, hc', ?_⟩
    intro A hA
    refine ⟨0, ?_⟩
    rw [hall A hA]
    ext i j
    simp [vecMulVec_apply]
  push_neg at hall
  obtain ⟨A₀, hA₀, hA₀'⟩ := hall
  obtain ⟨u, huH, v, hu, hv, hA⟩ := zero_sum_factors A₀ hA₀' (hz A₀ hA₀) (hr A₀ hA₀)
  have compat (A B : Coeff 2) (hA : A ∈ C) (hB : B ∈ C)
      (a c : Label → ℝ) (b d : Fin 2 → ℝ)
      (ha : A = vecMulVec a b) (hb : B = vecMulVec c d) :
      Parallel a c ∨ Parallel b d := by
    by_contra h
    have ht : Transverse a c b d := ⟨fun hh => h (Or.inl hh), fun hh => h (Or.inr hh)⟩
    have he := (rank_blend_iff (1 / 2) (by norm_num) (by norm_num) a c b d).mpr ht
    have hl := hm A hA B hB
    rw [ha, hb] at hl
    omega
  by_cases hleft : ∀ B ∈ C, ∃ z, B = vecMulVec u z
  · exact Or.inl ⟨u, huH, hu, hleft⟩
  push_neg at hleft
  obtain ⟨B, hB, hBbad⟩ := hleft
  have hB' : B ≠ 0 := by
    intro he
    apply hBbad 0
    rw [he]
    ext i j
    simp [vecMulVec_apply]
  obtain ⟨s, hsH, t, hs, ht, hBs⟩ := zero_sum_factors B hB' (hz B hB) (hr B hB)
  have hus : ¬ Parallel u s := by
    intro hp
    obtain ⟨a, ha⟩ := (parallel_iff_scalar u s hu).mp hp
    apply hBbad (a • t)
    rw [hBs, ha]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hvt := (compat A₀ B hA₀ hB u s v t hA hBs).resolve_left hus
  obtain ⟨a, ha⟩ := (parallel_iff_scalar v t hv).mp hvt
  have ha' : a ≠ 0 := by intro he; apply ht; simp [ha, he]
  let s' : Label → ℝ := a • s
  have hBs' : B = vecMulVec s' v := by
    rw [hBs, ha]
    ext i j
    simp only [s', vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hus' : ¬ Parallel u s' := by
    intro hp
    apply hus
    intro i k
    have hh := hp i k
    have he : wedge u s' i k = a * wedge u s i k := by
      simp only [s', wedge, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he] at hh
    exact (mul_eq_zero.mp hh).resolve_left ha'
  right
  refine ⟨v, hv, ?_⟩
  intro D hD
  by_cases hD' : D = 0
  · refine ⟨0, by simp [H], ?_⟩
    rw [hD']
    ext i j
    simp [vecMulVec_apply]
  obtain ⟨p, hpH, q, hp, hq, hDp⟩ := zero_sum_factors D hD' (hz D hD) (hr D hD)
  have hvq : Parallel v q := by
    by_contra hbad
    have hup := (compat A₀ D hA₀ hD u p v q hA hDp).resolve_right hbad
    have hsp := (compat B D hB hD s' p v q hBs' hDp).resolve_right hbad
    obtain ⟨d, hd⟩ := (parallel_iff_scalar p u hp).mp (parallel_symm hup)
    obtain ⟨e, he⟩ := (parallel_iff_scalar p s' hp).mp (parallel_symm hsp)
    apply hus'
    intro i k
    simp only [hd, he, wedge, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨d, hd⟩ := (parallel_iff_scalar v q hv).mp hvq
  refine ⟨d • p, ?_, ?_⟩
  · change ∑ y, d * p y = 0
    rw [← Finset.mul_sum, hpH, mul_zero]
  · rw [hDp, hd]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring

private theorem convex_classification (C : Set (Coeff 2)) (hc : Convex ℝ C)
    (hz : ∀ A ∈ C, ZeroSum A) :
    (∀ A ∈ C, A.rank ≤ 1) ↔ Rulings C := by
  constructor
  · intro hr
    apply common_factor C hz hr
    intro A hA B hB
    exact hr _ (hc hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by norm_num))
  · exact rulings_small C

/-- All original clauses, with the whole convex family as the content-bearing conclusion.
No nonemptiness premise is needed: empty and all-zero bodies are included. -/
theorem result {X : Type*} (b : Label → X → ℝ)
    (r₁ : Fin 1 → X → ℝ) (r₂ : Fin 2 → X → ℝ) :
    Convex ℝ (body b r₁) ∧ Convex ℝ (body b r₂) ∧
    ((∃ A ∈ body b r₁, A.rank = 1) ↔ ¬ body b r₁ ⊆ {0}) ∧
    ((¬ ∃ A ∈ body b r₂, A.rank = 2) ↔ Rulings (body b r₂)) ∧
    ((∃ A ∈ body b r₂, A.rank = 2) ↔ ¬ Rulings (body b r₂)) ∧
    ((∃ A ∈ body b r₂, A.rank = 2) ↔
      ∃ A ∈ body b r₂, ∃ B ∈ body b r₂,
        ∃ i k j l, minor (blend (1 / 2) A B) i k j l ≠ 0) ∧
    ((∀ A ∈ body b r₂, ∀ B ∈ body b r₂, ∀ i k j l,
      minor (blend (1 / 2) A B) i k j l = 0) → Rulings (body b r₂)) ∧
    (∀ A : Coeff 2, ZeroSum A → A ≠ 0 → A.rank = 1 →
      ∃ u ∈ H, ∃ v : Fin 2 → ℝ, u ≠ 0 ∧ v ≠ 0 ∧ A = vecMulVec u v) ∧
    (∀ (u s : Label → ℝ) (v t : Fin 2 → ℝ) (θ : ℝ)
      (i k : Label) (j l : Fin 2),
      minor (blend θ (vecMulVec u v) (vecMulVec s t)) i k j l =
        θ * (1 - θ) * wedge u s i k * wedge v t j l) ∧
    (∀ (u s : Label → ℝ) (v t : Fin 2 → ℝ) (θ : ℝ), 0 < θ → θ < 1 →
      (blend θ (vecMulVec u v) (vecMulVec s t)).rank = 2 ↔ Transverse u s v t) ∧
    (∀ (u s u' s' : Label → ℝ) (v t v' t' : Fin 2 → ℝ),
      vecMulVec u v = vecMulVec u' v' → vecMulVec s t = vecMulVec s' t' →
      (Transverse u s v t ↔ Transverse u' s' v' t')) ∧
    (∀ A ∈ body b r₂, ∀ B ∈ body b r₂, ∀ θ : ℝ, 0 < θ → θ < 1 →
      blend θ A B ∈ body b r₂ ∧
      (A ≠ 0 → B ≠ 0 → A.rank = 1 → B.rank = 1 →
        ((blend θ A B).rank = 2 ↔ TransversePair A B))) ∧
    ((∀ A ∈ body b r₂, A.rank ≤ 1) →
      (¬ ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, ∃ θ : ℝ,
        0 < θ ∧ θ < 1 ∧ (blend θ A B).rank = 2) ∧
      (¬ ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, TransversePair A B) ∧
      ((∃ A ∈ body b r₂, ∃ B ∈ body b r₂, ∃ θ : ℝ,
        0 < θ ∧ θ < 1 ∧ (blend θ A B).rank = 2) ↔
        ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, TransversePair A B) ∧
      Rulings (body b r₂)) ∧
    (∀ C : Set (Coeff 2), Convex ℝ C → (∀ A ∈ C, ZeroSum A) →
      ((∀ A ∈ C, A.rank ≤ 1) ↔ Rulings C)) ∧
    (∀ A : Coeff 2, A.rank = 2 ↔ ∃ i k j l, minor A i k j l ≠ 0) := by
  classical
  have hc₁ := body_convex b r₁
  have hc₂ := body_convex b r₂
  have hdef : (¬ ∃ A ∈ body b r₂, A.rank = 2) ↔
      ∀ A ∈ body b r₂, A.rank ≤ 1 := by
    constructor
    · intro h A hA
      have hb : A.rank ≤ 2 := by simpa using A.rank_le_card_width
      have hn : A.rank ≠ 2 := fun he => h ⟨A, hA, he⟩
      omega
    · intro h ⟨A, hA, he⟩
      have := h A hA
      omega
  have hclass := convex_classification (body b r₂) hc₂ (fun A hA => hA.1)
  have hblend : ∀ A ∈ body b r₂, ∀ B ∈ body b r₂, ∀ θ : ℝ,
      0 < θ → θ < 1 → blend θ A B ∈ body b r₂ := by
    intro A hA B hB θ ht ht'
    exact hc₂ hA hB ht.le (sub_pos.mpr ht').le (by ring)
  have hpair : ∀ A ∈ body b r₂, ∀ B ∈ body b r₂, ∀ θ : ℝ,
      0 < θ → θ < 1 → A ≠ 0 → B ≠ 0 → A.rank = 1 → B.rank = 1 →
      ((blend θ A B).rank = 2 ↔ TransversePair A B) := by
    intro A hA B hB θ ht ht' hA' hB' hrA hrB
    constructor
    · intro hr
      obtain ⟨u, huH, v, hu, hv, hAu⟩ := zero_sum_factors A hA' hA.1 hrA.le
      obtain ⟨s, hsH, t, hs, htv, hBs⟩ := zero_sum_factors B hB' hB.1 hrB.le
      refine ⟨hA', hB', hrA, hrB, u, huH, s, hsH, v, t, hu, hs, hv, htv, hAu, hBs, ?_⟩
      apply (rank_blend_iff θ ht ht' u s v t).mp
      simpa only [← hAu, ← hBs] using hr
    · rintro ⟨_, _, _, _, u, _, s, _, v, t, _, _, _, _, hAu, hBs, htuv⟩
      rw [hAu, hBs]
      exact (rank_blend_iff θ ht ht' u s v t).mpr htuv
  refine ⟨hc₁, hc₂, ?_, hdef.trans hclass, ?_, ?_, ?_, ?_,
    (fun u s v t θ i k j l => wedge_blend θ u s v t i k j l),
    (fun u s v t θ ht ht' => rank_blend_iff θ ht ht' u s v t),
    ?_, ?_, ?_, convex_classification, rank_two_iff_minor⟩
  · constructor
    · rintro ⟨A, hA, hr⟩ hh
      have he : A = 0 := hh hA
      simp [he] at hr
    · intro hh
      have hh' : ∃ A ∈ body b r₁, A ≠ 0 := by simpa using hh
      obtain ⟨A, hA, hn⟩ := hh'
      have hp := rank_pos hn
      have hb : A.rank ≤ 1 := by simpa using A.rank_le_card_width
      exact ⟨A, hA, by omega⟩
  · simpa only [not_not] using not_congr (hdef.trans hclass)
  · constructor
    · rintro ⟨A, hA, hr⟩
      have he : blend (1 / 2) A A = A := by
        ext i j
        simp only [blend, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      obtain ⟨i, k, j, l, hm⟩ := (rank_two_iff_minor A).mp hr
      exact ⟨A, hA, A, hA, i, k, j, l, by simpa [he] using hm⟩
    · rintro ⟨A, hA, B, hB, i, k, j, l, hm⟩
      exact ⟨_, hblend A hA B hB (1 / 2) (by norm_num) (by norm_num),
        (rank_two_iff_minor _).mpr ⟨i, k, j, l, hm⟩⟩
  · intro hh
    apply hclass.mp
    intro A hA
    apply (rank_le_one_iff_minors A).mpr
    intro i k j l
    have he : blend (1 / 2) A A = A := by
      ext i j
      simp only [blend, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    simpa only [he] using hh A hA A hA i k j l
  · intro A hz hn hr
    exact zero_sum_factors A hn hz hr.le
  · intro u s u' s' v t v' t' hA hB
    rw [← rank_blend_iff (1 / 2) (by norm_num) (by norm_num) u s v t,
      ← rank_blend_iff (1 / 2) (by norm_num) (by norm_num) u' s' v' t', hA, hB]
  · intro A hA B hB θ ht ht'
    exact ⟨hblend A hA B hB θ ht ht', hpair A hA B hB θ ht ht'⟩
  · intro hr
    have hn : ¬ ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, ∃ θ : ℝ,
        0 < θ ∧ θ < 1 ∧ (blend θ A B).rank = 2 := by
      rintro ⟨A, hA, B, hB, θ, ht, ht', he⟩
      have := hr _ (hblend A hA B hB θ ht ht')
      omega
    have hp : ¬ ∃ A ∈ body b r₂, ∃ B ∈ body b r₂, TransversePair A B := by
      rintro ⟨A, hA, B, hB, hp⟩
      have he := (hpair A hA B hB (1 / 2) (by norm_num) (by norm_num)
        hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1).mpr hp
      exact hn ⟨A, hA, B, hB, 1 / 2, by norm_num, by norm_num, he⟩
    exact ⟨hn, hp, ⟨fun h => (hn h).elim, fun h => (hp h).elim⟩, hclass.mp hr⟩

end D5.S3.Geometry.CoefficientBodies.ConvexRankOneRulings
