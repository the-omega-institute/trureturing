/- GID: D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionJordanFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Jordan-block algebras are minimal perfect with exact evolution embedding dimension. -/

/-
The Jordan-block family and its explicit plus/minus embedding are due to
Wenlin Zhang and Haobo Ma in Structure tests for stable derived terms.
Jordan-block describes the nilpotent coordinate shift, not a Jordan algebra
identity. Minimality quantifies over every complex linear subspace. The
ambient algebra need not be perfect: its first and second product spans are
exactly the embedded range. The general idempotent theorem and the general
nilpotent/cyclic classification are not assumed here.
-/

import D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 2048

namespace D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily

open D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionLowerBound

def minimalPerfect {d : ℕ} (μ : Product d) : Prop :=
  perfect μ ∧ ∀ U : Submodule ℂ (Coord d),
    U ≠ ⊥ → square μ U = U → U = ⊤

def isEmbeddingDimension {d : ℕ} (μ : Product d) (n : ℕ) : Prop :=
  hasEvolutionEmbedding μ n ∧
    ∀ q : ℕ, hasEvolutionEmbedding μ q → n ≤ q

def hasStableSquareEmbedding {d : ℕ} (μ : Product d) (n : ℕ) : Prop :=
  ∃ ν : Product n, ∃ f : Coord d →ₗ[ℂ] Coord n,
    hasNaturalBasis ν ∧ Function.Injective f ∧
    (∀ x y, f (μ x y) = ν (f x) (f y)) ∧
    square ν ⊤ = f.range ∧ square ν f.range = f.range

/-- Coordinates are u,w_1,...,w_m; N w_i = w_(i-1). -/
def jordanProduct (m : ℕ) (x y : Coord (m + 1)) : Coord (m + 1) :=
  fun k =>
    if k.val = 0 then 4 * x 0 * y 0
    else
      2 * x 0 * y k + 2 * x k * y 0 +
      (if h : k.val + 1 < m + 1 then
        2 * x 0 * y ⟨k.val + 1, h⟩ +
          2 * x ⟨k.val + 1, h⟩ * y 0
       else 0) +
      (if k.val = m then 2 * x 0 * y 0 else 0)

def jordanLaw (m : ℕ) (μ : Product (m + 1)) : Prop :=
  ∀ x y, μ x y = jordanProduct m x y


/-- Bilinear implementation of the exact Jordan-block coordinate law. -/
noncomputable def jordan (m : ℕ) : Product (m + 1) where
  toFun x :=
    { toFun := jordanProduct m x
      map_add' := by
        intro y z; ext k
        simp only [jordanProduct, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := by
        intro a y; ext k
        simp only [jordanProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    ext k
    change jordanProduct m (x+y) z k = jordanProduct m x z k + jordanProduct m y z k
    simp only [jordanProduct, Pi.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    ext k
    change jordanProduct m (a • x) y k = a * jordanProduct m x y k
    simp only [jordanProduct, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring

private theorem jordan_commutative (m : ℕ) : commutative (jordan m) := by
  intro x y; ext k
  simp only [jordan, LinearMap.coe_mk, AddHom.coe_mk, jordanProduct]
  split_ifs <;> ring

/-- The coordinate hyperplane spanned by w₁,...,wₘ. -/
private def jordanW (m : ℕ) : Submodule ℂ (Coord (m + 1)) :=
  LinearMap.ker (LinearMap.proj (0 : Fin (m + 1)))

private theorem jordan_w_square_zero (m : ℕ) : square (jordan m) (jordanW m) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hx0 : x 0 = 0 := hx
  have hy0 : y 0 = 0 := hy
  change jordanProduct m x y = 0
  ext k
  simp only [jordanProduct, hx0, hy0, zero_mul, mul_zero, zero_add, add_zero,
    Pi.zero_apply]
  split_ifs <;> simp

/-- Left multiplication by u is injective; backwards substitution uses the
    diagonal entries 4,2,...,2 and the nilpotent shift. -/
private theorem jordan_left_u_injective (m : ℕ) :
    Function.Injective (jordan m (Pi.single 0 1)) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  have hmul : jordanProduct m (Pi.single 0 1) x = 0 := hx
  have hx0 : x 0 = 0 := by
    have h := congr_fun hmul 0
    simpa [jordanProduct] using h
  change x = 0
  ext k
  induction k using Fin.reverseInduction with
  | last =>
      by_cases hm : m = 0
      · subst m; simpa using hx0
      · have h := congr_fun hmul (Fin.last m)
        simp [jordanProduct, hm, hx0] at h
        exact h
  | @cast i ih =>
      by_cases hi : i.val = 0
      · have he : i.castSucc = 0 := Fin.ext hi
        simpa [he] using hx0
      · have h := congr_fun hmul i.castSucc
        have hnext : (⟨i.val + 1, by omega⟩ : Fin (m + 1)) = i.succ := rfl
        simp [jordanProduct, hi, hx0, hnext, ih, i.isLt] at h
        exact h

/-- Perfectness of the full Jordan-block family, for every m. -/
private theorem jordan_perfect (m : ℕ) : perfect (jordan m) := by
  apply le_antisymm le_top
  intro x hx
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective (jordan_left_u_injective m) x
  exact Submodule.subset_span ⟨Pi.single 0 1, Submodule.mem_top, y, Submodule.mem_top, hy⟩

private theorem jordan_w_finrank (m : ℕ) : Module.finrank ℂ (jordanW m) = m := by
  let L : Coord (m+1) →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hsurj : Function.Surjective L := by
    intro a
    refine ⟨Pi.single 0 a, ?_⟩
    simp [L]
  have hnull := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj] at hnull
  have hdim : Module.finrank ℂ (Coord (m+1)) = m+1 := by simp [Coord]
  have hrange : Module.finrank ℂ (⊤ : Submodule ℂ ℂ) = 1 := by simp
  rw [hdim, hrange] at hnull
  change Module.finrank ℂ (LinearMap.ker L) = m
  omega

private theorem jordan_embedding_lower_bound {m n : ℕ}
    (he : hasEvolutionEmbedding (jordan m) n) : 2*m+1 ≤ n := by
  have h := square_zero_embedding_lower_bound (jordan m) (jordan_commutative m)
    (jordan_perfect m) (jordanW m) (jordan_w_square_zero m) he
  rw [jordan_w_finrank] at h
  omega

private theorem jordan_not_has_natural_basis {m : ℕ} (hm : 1 ≤ m) :
    ¬ hasNaturalBasis (jordan m) := by
  intro hn
  have he : hasEvolutionEmbedding (jordan m) (m+1) :=
    ⟨jordan m, LinearMap.id, hn, Function.injective_id, fun x y => rfl⟩
  have h := jordan_embedding_lower_bound he
  omega


/-- Products commute with image under a multiplication-preserving linear map. -/
private theorem square_map {d n : ℕ} (μ : Product d) (ν : Product n)
    (f : Coord d →ₗ[ℂ] Coord n) (hf : ∀ x y, f (μ x y) = ν (f x) (f y))
    (U : Submodule ℂ (Coord d)) :
    (square μ U).map f = square ν (U.map f) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    change f (μ x y) ∈ square ν (U.map f)
    rw [hf]
    exact Submodule.subset_span ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨x, hx, y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨μ x y, Submodule.subset_span ⟨x, hx, y, hy, rfl⟩, hf x y⟩

/-- Quotient by the first square-zero direction w₁. -/
private def jordanDrop (m : ℕ) : Coord (m+2) →ₗ[ℂ] Coord (m+1) where
  toFun x := Fin.cases (x 0) (fun i => x i.succ.succ)
  map_add' := by intro x y; ext k; refine Fin.cases ?_ (fun i => ?_) k <;> rfl
  map_smul' := by intro a x; ext k; refine Fin.cases ?_ (fun i => ?_) k <;> rfl


private theorem jordan_drop_hom (m : ℕ) (x y : Coord (m+2)) :
    jordanDrop m (jordan (m+1) x y) = jordan m (jordanDrop m x) (jordanDrop m y) := by
  ext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [jordan, jordanProduct, jordanDrop]
  · change jordanProduct (m+1) x y i.succ.succ =
      jordanProduct m (jordanDrop m x) (jordanDrop m y) i.succ
    by_cases h : i.val + 1 < m
    · have ho : i.val + 2 + 1 < m+1+1 := by omega
      have hn : i.val + 1 + 1 < m+1 := by omega
      have ho0 : i.val+2 ≠ 0 := by omega
      have hn0 : i.val+1 ≠ 0 := by omega
      have he : (⟨i.val+1+1, hn⟩ : Fin (m+1)) = (⟨i.val+1, h⟩ : Fin m).succ := rfl
      simp [jordanProduct, ho, hn, ho0, hn0]
      rfl
    · have ho : ¬ i.val + 2 + 1 < m+1+1 := by omega
      have hn : ¬ i.val + 1 + 1 < m+1 := by omega
      have ho0 : i.val+2 ≠ 0 := by omega
      have hn0 : i.val+1 ≠ 0 := by omega
      simp [jordanProduct, ho, hn, ho0, hn0]
      rfl

/-- Insert a zero at the w₁ coordinate. -/
private def jordanLift (m : ℕ) (z : Coord (m+1)) : Coord (m+2) :=
  Fin.cases (z 0) (Fin.cases 0 (fun i => z i.succ))

private theorem jordan_drop_decompose (m : ℕ) (x : Coord (m+2)) :
    x = jordanLift m (jordanDrop m x) + x 1 • Pi.single 1 1 := by
  change x = jordanLift m (jordanDrop m x) +
    x (Fin.succ 0) • Pi.single (Fin.succ (0 : Fin (m+1))) 1
  ext k
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) k <;>
    simp only [jordanLift, jordanDrop, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.cases_zero, Fin.cases_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Fin.succ_inj, Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _), ite_true, ite_false, zero_add, add_zero, mul_one, mul_zero]

private theorem jordan_lift_zero (m : ℕ) : jordanLift m 0 = 0 := by
  ext k
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) k <;> rfl

private theorem jordan_lift_u (m : ℕ) : jordanLift m (Pi.single 0 1) = Pi.single 0 1 := by
  ext k
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) k <;>
    simp only [jordanLift, Fin.cases_zero, Fin.cases_succ, Pi.single_apply,
      Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _), ite_true, ite_false]

private theorem jordan_lift_w (m : ℕ) :
    jordanLift (m+1) (Pi.single 1 1) = Pi.single 2 1 := by
  change jordanLift (m+1) (Pi.single (Fin.succ (0 : Fin (m+1))) 1) =
    Pi.single (Fin.succ (Fin.succ (0 : Fin (m+1)))) 1
  ext k
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) k <;>
    simp only [jordanLift, Fin.cases_zero, Fin.cases_succ, Pi.single_apply,
      Fin.succ_ne_zero, Ne.symm (Fin.succ_ne_zero _), Fin.succ_inj, ite_true, ite_false]

private theorem jordan_u_square (m : ℕ) :
    jordan (m+1) (Pi.single 0 1) (Pi.single 0 1) =
      (4:ℂ) • Pi.single 0 1 + (2:ℂ) • Pi.single (Fin.last (m+1)) 1 := by
  ext k
  change jordanProduct (m+1) (Pi.single 0 1) (Pi.single 0 1) k = _
  unfold jordanProduct
  simp [Pi.single_apply, Fin.ext_iff, -Fin.val_eq_zero_iff]
  split_ifs <;> simp_all only [mul_one, mul_zero, zero_mul, add_zero, zero_add, zero_smul] <;> omega

private theorem jordan_u_w1 (m : ℕ) :
    jordan (m+1) (Pi.single 0 1) (Pi.single 1 1) = (2:ℂ) • Pi.single 1 1 := by
  ext k
  change jordanProduct (m+1) (Pi.single 0 1) (Pi.single 1 1) k = _
  unfold jordanProduct
  simp [Pi.single_apply, Fin.ext_iff, -Fin.val_eq_zero_iff]
  split_ifs <;> simp_all only [mul_one, mul_zero, zero_mul, add_zero, zero_add, zero_smul] <;> omega

private theorem jordan_u_w2 (m : ℕ) :
    jordan (m+2) (Pi.single 0 1) (Pi.single 2 1) =
      (2:ℂ) • Pi.single 2 1 + (2:ℂ) • Pi.single 1 1 := by
  have h2 : 2 < m+3 := by omega
  ext k
  refine Fin.cases ?_ (fun i => ?_) k
  · change jordanProduct (m+2) (Pi.single 0 1) (Pi.single 2 1) 0 = _
    unfold jordanProduct
    simp [Pi.single_apply, Fin.ext_iff, Nat.mod_eq_of_lt h2, -Fin.val_eq_zero_iff]
  · change jordanProduct (m+2) (Pi.single 0 1) (Pi.single 2 1) i.succ = _
    unfold jordanProduct
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      subst i
      simp [Pi.single_apply, Fin.ext_iff, Nat.mod_eq_of_lt h2, -Fin.val_eq_zero_iff]
    · have hn : i.val + 1 + 1 ≠ 2 := by omega
      have hn1 : i.val + 1 ≠ 1 := by omega
      simp [Pi.single_apply, Fin.ext_iff, Nat.mod_eq_of_lt h2, hn, hn1, hi, -Fin.val_eq_zero_iff]

private theorem jordan_w1_square (m : ℕ) :
    jordan (m+1) (Pi.single 1 1) (Pi.single 1 1) = 0 := by
  have h : (Pi.single (1:Fin (m+2)) (1:ℂ) : Coord (m+2)) ∈ jordanW (m+1) := by
    change ((Pi.single (1 : Fin (m+2)) (1:ℂ)) : Coord (m+2)) 0 = 0
    simp
  have hp : jordan (m+1) (Pi.single 1 1) (Pi.single 1 1) ∈
      square (jordan (m+1)) (jordanW (m+1)) :=
    Submodule.subset_span ⟨Pi.single 1 1, h, Pi.single 1 1, h, rfl⟩
  simpa only [jordan_w_square_zero, Submodule.mem_bot] using hp

private theorem square_mono {d : ℕ} (μ : Product d) {U V : Submodule ℂ (Coord d)}
    (h : U ≤ V) : square μ U ≤ square μ V := by
  apply Submodule.span_le.mpr
  rintro z ⟨x,hx,y,hy,rfl⟩
  exact Submodule.subset_span ⟨x,h hx,y,h hy,rfl⟩

private theorem jordan_w_product_zero {m : ℕ} {x y : Coord (m+1)}
    (hx : x ∈ jordanW m) (hy : y ∈ jordanW m) : jordan m x y = 0 := by
  have h : jordan m x y ∈ square (jordan m) (jordanW m) :=
    Submodule.subset_span ⟨x,hx,y,hy,rfl⟩
  simpa only [jordan_w_square_zero, Submodule.mem_bot] using h

/-- Minimality of every Jordan-block family member, including the dimension-one base. -/
private theorem jordan_minimal_perfect (m : ℕ) : minimalPerfect (jordan m) := by
  induction m with
  | zero =>
    refine ⟨jordan_perfect 0, ?_⟩
    intro U hne hU
    have hle : Module.finrank ℂ U ≤ 1 := by
      simpa [Coord] using Submodule.finrank_le U
    have hn : Module.finrank ℂ U ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
    apply Submodule.eq_top_of_finrank_eq
    have hdim : Module.finrank ℂ U = 1 := by omega
    simpa [Coord] using hdim
  | succ m ih =>
    refine ⟨jordan_perfect (m+1), ?_⟩
    intro U hne hU
    let q := jordanDrop m
    have hclosed : ∀ x ∈ U, ∀ y ∈ U, jordan (m+1) x y ∈ U := by
      intro x hx y hy
      rw [← hU]
      exact Submodule.subset_span ⟨x,hx,y,hy,rfl⟩
    have himage_ne : U.map q ≠ ⊥ := by
      intro hb
      have hle : U ≤ jordanW (m+1) := by
        intro x hx
        have hqx : q x ∈ U.map q := ⟨x,hx,rfl⟩
        rw [hb] at hqx
        have hz : q x = 0 := hqx
        have h0 := congr_fun hz 0
        exact h0
      have hs := square_mono (jordan (m+1)) hle
      rw [hU, jordan_w_square_zero] at hs
      exact hne (le_antisymm hs bot_le)
    have himage_perfect : square (jordan m) (U.map q) = U.map q := by
      rw [← square_map (jordan (m+1)) (jordan m) q (jordan_drop_hom m), hU]
    have himage : U.map q = ⊤ := ih.2 (U.map q) himage_ne himage_perfect
    obtain ⟨x,hxU,hqx⟩ : ∃ x ∈ U, q x = Pi.single 0 1 := by
      have h : Pi.single 0 (1:ℂ) ∈ U.map q := by rw [himage]; trivial
      exact h
    have hx : x = Pi.single 0 1 + x 1 • Pi.single 1 1 := by
      simpa only [q, hqx, jordan_lift_u] using jordan_drop_decompose m x
    have hw1 : Pi.single 1 (1:ℂ) ∈ U := by
      have hrelmem : (2:ℂ) • Pi.single 1 (1:ℂ) ∈ U := by
        cases m with
        | zero =>
          have hrel : jordan 1 x x - (4:ℂ) • x = (2:ℂ) • Pi.single 1 1 := by
            rw [hx]
            simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
              RingHom.id_apply, jordan_u_square, jordan_u_w1, jordan_w1_square]
            have hwu := jordan_commutative 1 (Pi.single 1 1) (Pi.single 0 1)
            rw [hwu, jordan_u_w1]
            ext k
            simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
              Pi.zero_apply, Fin.last, Fin.mk_one]
            ring_nf <;> rfl
          rw [← hrel]
          exact U.sub_mem (hclosed x hxU x hxU) (U.smul_mem 4 hxU)
        | succ r =>
          obtain ⟨y,hyU,hqy⟩ : ∃ y ∈ U, q y = Pi.single 1 1 := by
            have h : Pi.single 1 (1:ℂ) ∈ U.map q := by rw [himage]; trivial
            exact h
          have hy : y = Pi.single 2 1 + y 1 • Pi.single 1 1 := by
            simpa only [q, hqy, jordan_lift_w] using jordan_drop_decompose (r+1) y
          have h12 : jordan (r+2) (Pi.single 1 1) (Pi.single 2 1) = 0 := by
            apply jordan_w_product_zero
            · change ((Pi.single (1 : Fin (r+3)) (1:ℂ)) : Coord (r+3)) 0 = 0
              simp
            · change ((Pi.single (2 : Fin (r+3)) (1:ℂ)) : Coord (r+3)) 0 = 0
              simp [Pi.single_apply, Fin.ext_iff, -Fin.val_eq_zero_iff, Nat.mod_eq_of_lt (by omega : 2 < r+3)]
          have hrel : jordan (r+2) x y - (2:ℂ) • y = (2:ℂ) • Pi.single 1 1 := by
            rw [hx,hy]
            simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
              RingHom.id_apply, jordan_u_w2, jordan_u_w1, jordan_w1_square, h12]
            ext k
            simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
              Pi.zero_apply, smul_zero]
            ring
          rw [← hrel]
          exact U.sub_mem (hclosed x hxU y hyU) (U.smul_mem 2 hyU)
      have h := U.smul_mem (2:ℂ)⁻¹ hrelmem
      simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2:ℂ) ≠ 0), one_smul] using h
    apply le_antisymm le_top
    intro z hz
    obtain ⟨y,hy,hqy⟩ : ∃ y ∈ U, q y = q z := by
      have h : q z ∈ U.map q := by rw [himage]; trivial
      exact h
    have hqzero : q (z-y) = 0 := by rw [map_sub,hqy,sub_self]
    have hk : z-y ∈ U := by
      have hdec := jordan_drop_decompose m (z-y)
      rw [show jordanDrop m (z-y) = 0 from hqzero, jordan_lift_zero, zero_add] at hdec
      rw [hdec]
      exact U.smul_mem _ hw1
    have h := U.add_mem hk hy
    simpa only [sub_add_cancel] using h


private def plusIndex {m : ℕ} (i : Fin m) : Fin (2*m+1) := ⟨i.val+1, by omega⟩
private def minusIndex {m : ℕ} (i : Fin m) : Fin (2*m+1) := ⟨m+i.val+1, by omega⟩

private def jordanEmbeddingFun (m : ℕ) (x : Coord (m+1)) : Coord (2*m+1) :=
  Fin.cases (x 0) (fun k =>
    if h : k.val < m then x 0 + x ⟨k.val+1, by omega⟩
    else x 0 - x ⟨k.val-m+1, by omega⟩)

/-- Coordinates are f₀, all plus coordinates, then all minus coordinates. -/
private def jordanEmbedding (m : ℕ) : Coord (m+1) →ₗ[ℂ] Coord (2*m+1) where
  toFun := jordanEmbeddingFun m
  map_add' := by
    intro x y; ext k
    change jordanEmbeddingFun m (x+y) k = jordanEmbeddingFun m x k + jordanEmbeddingFun m y k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · simp only [jordanEmbeddingFun, Fin.cases_succ, Pi.add_apply]
      split_ifs <;> ring
  map_smul' := by
    intro a x; ext k
    change jordanEmbeddingFun m (a • x) k = a * jordanEmbeddingFun m x k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · simp only [jordanEmbeddingFun, Fin.cases_succ, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring

@[simp] private theorem jordan_embedding_zero (m : ℕ) (x : Coord (m+1)) :
    jordanEmbedding m x 0 = x 0 := rfl

private theorem jordan_embedding_plus {m : ℕ} (x : Coord (m+1)) (i : Fin m) :
    jordanEmbedding m x (plusIndex i) = x 0 + x i.succ := by
  change (if h : i.val < m then x 0 + x ⟨i.val+1, by omega⟩
    else x 0 - x ⟨i.val-m+1, by omega⟩) = _
  simp [i.isLt]
  rfl

private theorem jordan_embedding_minus {m : ℕ} (x : Coord (m+1)) (i : Fin m) :
    jordanEmbedding m x (minusIndex i) = x 0 - x i.succ := by
  change (if h : m+i.val < m then x 0 + x ⟨m+i.val+1, by omega⟩
    else x 0 - x ⟨m+i.val-m+1, by omega⟩) = _
  simp
  rfl

private theorem jordan_embedding_injective (m : ℕ) : Function.Injective (jordanEmbedding m) := by
  intro x y h
  have h0 : x 0 = y 0 := congr_fun h 0
  ext k
  refine Fin.cases h0 (fun i => ?_) k
  have hp := congr_fun h (plusIndex i)
  rw [jordan_embedding_plus, jordan_embedding_plus, h0] at hp
  exact add_left_cancel hp

/-- The intrinsic coefficient map whose columns prescribe the ambient squares. -/
private def jordanCoefficients (m : ℕ) : Coord (2*m+1) →ₗ[ℂ] Coord (m+1) where
  toFun z := Fin.cases (4*z 0) (fun i =>
    z (plusIndex i) - z (minusIndex i) +
    (if h : i.val+1 < m then
      z (plusIndex ⟨i.val+1,h⟩) - z (minusIndex ⟨i.val+1,h⟩) else 0) +
    (if i.val+1 = m then 2*z 0 else 0))
  map_add' := by
    intro x y; ext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp; ring
    · simp only [Fin.cases_succ, Pi.add_apply]
      split_ifs <;> ring
  map_smul' := by
    intro a x; ext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp; ring
    · simp only [Fin.cases_succ, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs <;> ring

/-- All embedding identities at once, with no finite-dimensional computation. -/
private theorem jordan_coefficients_product (m : ℕ) (x y : Coord (m+1)) :
    jordanCoefficients m (jordanEmbedding m x * jordanEmbedding m y) = jordan m x y := by
  ext k
  refine Fin.cases ?_ (fun i => ?_) k
  · change 4 * (jordanEmbedding m x 0 * jordanEmbedding m y 0) =
      jordanProduct m x y 0
    simp [jordanProduct]; ring
  · change _ = jordanProduct m x y i.succ
    unfold jordanProduct
    simp only [jordanCoefficients, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.cases_succ, Pi.mul_apply, Fin.val_succ, jordan_embedding_plus,
      jordan_embedding_minus, jordan_embedding_zero]
    have h0 : i.val+1 ≠ 0 := by omega
    simp only [h0, if_false]
    by_cases hn : i.val+1 < m
    · have hn2 : i.val+1+1 < m+1 := by omega
      simp only [hn, hn2, dite_true]
      have heq : (⟨i.val+1, hn⟩ : Fin m).succ = (⟨i.val+1+1, hn2⟩ : Fin (m+1)) := rfl
      rw [heq]
      split_ifs <;> ring
    · have hn2 : ¬ i.val+1+1 < m+1 := by omega
      simp only [hn, hn2, dite_false]
      split_ifs <;> ring

/-- Any linear structure map defines a bilinear evolution law in standard coordinates. -/
def coordinateProduct {n : ℕ} (M : Coord n →ₗ[ℂ] Coord n) : Product n where
  toFun x :=
    { toFun := fun y => M (x*y)
      map_add' := by intro y z; rw [mul_add, map_add]
      map_smul' := by intro a y; rw [mul_smul_comm, map_smul, RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change M ((x+y)*z) = M (x*z)+M (y*z)
    rw [add_mul,map_add]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    change M ((a • x)*y) = a • M (x*y)
    rw [smul_mul_assoc,map_smul]

theorem coordinate_product_natural {n : ℕ} (M : Coord n →ₗ[ℂ] Coord n) :
    hasNaturalBasis (coordinateProduct M) := by
  classical
  refine ⟨Pi.basisFun ℂ (Fin n), ?_⟩
  intro i j hij
  simp only [Pi.basisFun_apply]
  change M ((Pi.single i 1)*(Pi.single j 1)) = 0
  have hzero : ((Pi.single i (1:ℂ)) : Coord n)*(Pi.single j 1) = 0 := by
    ext k
    by_cases hi : k=i
    · subst k; simp [Pi.single_apply,hij]
    · simp [Pi.single_apply,hi]
  rw [hzero,map_zero]

theorem coordinate_product_square {n : ℕ} (M : Coord n →ₗ[ℂ] Coord n) :
    square (coordinateProduct M) ⊤ = LinearMap.range M := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    exact ⟨x*y,rfl⟩
  · let e := Pi.basisFun ℂ (Fin n)
    have hrange : LinearMap.range M = Submodule.span ℂ (Set.range (fun i => M (e i))) := by
      calc
        LinearMap.range M = LinearMap.range (e.constr ℂ (fun i => M (e i))) :=
          congr_arg LinearMap.range (e.constr_self ℂ M).symm
        _ = _ := e.constr_range ℂ
    rw [hrange]
    apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    have hi : (e i : Coord n)*(e i) = e i := by
      ext k; simp [e,Pi.basisFun_apply,Pi.single_apply]
    have hprod : coordinateProduct M (e i) (e i) = M (e i) := by
      change M ((e i)*(e i)) = M (e i)
      rw [hi]
    exact Submodule.subset_span ⟨e i, Submodule.mem_top, e i, Submodule.mem_top, hprod⟩

private theorem jordan_coefficients_range (m : ℕ) : LinearMap.range (jordanCoefficients m) = ⊤ := by
  apply le_antisymm le_top
  have hs : square (jordan m) ⊤ ≤ LinearMap.range (jordanCoefficients m) := by
    apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    exact ⟨jordanEmbedding m x * jordanEmbedding m y, jordan_coefficients_product m x y⟩
  have hp : square (jordan m) ⊤ = ⊤ := jordan_perfect m
  rwa [hp] at hs

private theorem jordan_stable_embedding (m : ℕ) :
    hasStableSquareEmbedding (jordan m) (2*m+1) := by
  let J := jordanEmbedding m
  let A := jordanCoefficients m
  let ν := coordinateProduct (J.comp A)
  have hmul : ∀ x y, J (jordan m x y) = ν (J x) (J y) := by
    intro x y
    change J (jordan m x y) = J (A (J x * J y))
    rw [jordan_coefficients_product]
  refine ⟨ν,J,coordinate_product_natural _,jordan_embedding_injective m,hmul,?_,?_⟩
  · change square (coordinateProduct (J.comp A)) ⊤ = LinearMap.range J
    rw [coordinate_product_square, LinearMap.range_comp, jordan_coefficients_range,
      Submodule.map_top]
  · have h := square_map (jordan m) ν J hmul ⊤
    have hp : square (jordan m) ⊤ = ⊤ := jordan_perfect m
    simpa only [hp, Submodule.map_top] using h.symm

/-- Every positive Jordan-block member attains its exact evolution embedding dimension. -/
theorem jordan_family (m : ℕ) (hm : 1 ≤ m) :
    ∃ μ : Product (m+1),
      jordanLaw m μ ∧ commutative μ ∧ minimalPerfect μ ∧
      ¬ hasNaturalBasis μ ∧
      hasStableSquareEmbedding μ (2*m+1) ∧
      isEmbeddingDimension μ (2*m+1) := by
  have hs := jordan_stable_embedding m
  have he : hasEvolutionEmbedding (jordan m) (2*m+1) := by
    obtain ⟨ν,f,hn,hf,hmul,h1,h2⟩ := hs
    exact ⟨ν,f,hn,hf,hmul⟩
  exact ⟨jordan m,(fun x y => rfl),jordan_commutative m,jordan_minimal_perfect m,
    jordan_not_has_natural_basis hm,hs,he,fun q hq => jordan_embedding_lower_bound hq⟩


#print axioms jordan_family
end D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionJordanFamily
