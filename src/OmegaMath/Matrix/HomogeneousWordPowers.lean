import OmegaBuild.Commands
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.NoncommRing

/-! Omega original.

Dimension growth for exact powers of subspaces of a finite-dimensional algebra and
the two-dimensional generator-space reduction for size-three matrix algebras.
In the setting of Shitov's Question 2, a proper seventh power in the
invertible-generator case forces a square-zero generator with zero first return
and nonzero second return. -/

compile_only_with_mathlib

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace OmegaMath.HomogeneousWordPowers

section Algebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- Fullness at a positive exact length persists at every larger length. -/
theorem pow_eq_top_of_le (L : Submodule K A) {m k : ℕ}
    (hm : 0 < m) (hfull : L ^ m = ⊤) (hk : m ≤ k) : L ^ k = ⊤ := by
  have htop : (⊤ : Submodule K A) * L = ⊤ := by
    apply top_unique
    calc
      ⊤ = L ^ (m - 1) * L := by rw [← pow_succ, Nat.sub_add_cancel hm, hfull]
      _ ≤ ⊤ * L := by gcongr; exact le_top
  induction k, hk using Nat.le_induction with
  | base => exact hfull
  | succ k hk ih => rw [pow_succ, ih, htop]

/-- A unit in degree `s` forces strict growth over `s` steps from every proper power
of an eventually full subspace. -/
theorem finrank_pow_lt_of_unit_mem [FiniteDimensional K A]
    (L : Submodule K A) (j s : ℕ) (u : Aˣ)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hs : 0 < s) (hu : (u : A) ∈ L ^ s) (hj : L ^ j ≠ ⊤) :
    Module.finrank K ↥(L ^ j) < Module.finrank K ↥(L ^ (j + s)) := by
  let U := Submodule.span K ({(u : A)} : Set A)
  let e := u.mulLeftLinearEquiv K A
  have hmap (V : Submodule K A) : U * V = V.map e.toLinearMap := by
    ext x
    rw [Submodule.mem_span_singleton_mul, Submodule.mem_map]
    rfl
  have hle : U * L ^ j ≤ L ^ (j + s) := by
    rw [Nat.add_comm j s, pow_add]
    gcongr
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hu
  by_contra! hrank
  have hstep : U * L ^ j = L ^ (j + s) :=
    Submodule.eq_of_le_of_finrank_le hle (by rwa [hmap, LinearEquiv.finrank_map_eq])
  have hproper (n : ℕ) : L ^ (j + n * s) ≠ ⊤ := by
    induction n with
    | zero => simpa using hj
    | succ n ih =>
      have hindex : j + (n + 1) * s = (j + s) + n * s := by
        rw [Nat.add_mul]
        simp only [one_mul]
        omega
      rw [hindex, pow_add, ← hstep, mul_assoc, ← pow_add, hmap]
      exact fun h => ih (Submodule.map_eq_top_iff.mp h)
  obtain ⟨m, hm, hfull⟩ := hfull
  have hle : m ≤ j + m * s :=
    (Nat.le_mul_of_pos_right m hs).trans (Nat.le_add_left _ _)
  exact hproper m (pow_eq_top_of_le L hm hfull hle)

/-- An invertible element in degree one bounds the remaining length by the dimension deficit. -/
theorem pow_eq_top_of_finrank_add_le [FiniteDimensional K A]
    (L : Submodule K A) (u : Aˣ) (hu : (u : A) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) {j t : ℕ} (hj : 0 < j)
    (hbound : Module.finrank K A ≤ Module.finrank K ↥(L ^ j) + t) :
    L ^ (j + t) = ⊤ := by
  by_contra hproper
  have hg (k : ℕ) (hk : k ≤ t) :
      Module.finrank K ↥(L ^ j) + k ≤ Module.finrank K ↥(L ^ (j + k)) := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hp : L ^ (j + k) ≠ ⊤ := by
          intro heq
          exact hproper (pow_eq_top_of_le L (by omega) heq (by omega))
        have hs := finrank_pow_lt_of_unit_mem L (j + k) 1 u hfull (by decide)
          (by simpa using hu) hp
        have hb := ih (by omega)
        rw [show j + (k + 1) = (j + k) + 1 by omega]
        omega
  exact hproper (Submodule.eq_of_le_of_finrank_le le_top
    (by simpa only [finrank_top] using hbound.trans (hg t le_rfl)))

end Algebra

section SizeThree

variable {K : Type*} [Field K]

local notation "Mat" => Matrix (Fin 3) (Fin 3) K

private theorem finrank_matrix_three : Module.finrank K Mat = 9 := by
  simp [Module.finrank_matrix]

/-- A proper seventh power in the invertible case forces dimensions two and three
in the first two degrees. -/
theorem finrank_eq_two_and_three_of_pow_seven_ne_top
    (L : Submodule K Mat) (u : Matˣ) (hu : (u : Mat) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hseven : L ^ 7 ≠ ⊤) :
    Module.finrank K L = 2 ∧ Module.finrank K ↥(L ^ 2) = 3 := by
  have hline : Submodule.span K ({(u : Mat)} : Set Mat) ≤ L :=
    (Submodule.span_singleton_le_iff_mem _ _).2 hu
  have hone : Module.finrank K (Submodule.span K ({(u : Mat)} : Set Mat)) = 1 :=
    finrank_span_singleton u.ne_zero
  have hlower : 1 ≤ Module.finrank K L := hone ▸ Submodule.finrank_mono hline
  have hnotone : Module.finrank K L ≠ 1 := by
    intro heq
    have hL := Submodule.eq_of_le_of_finrank_le hline (heq.trans_le hone.ge)
    obtain ⟨m, _, hm⟩ := hfull
    rw [← hL, Submodule.span_pow, Set.singleton_pow] at hm
    have he : Module.finrank K (Submodule.span K ({(u : Mat) ^ m} : Set Mat)) = 1 :=
      finrank_span_singleton (by simpa only [Units.val_pow_eq_pow_val] using (u ^ m).ne_zero)
    rw [hm, finrank_top, finrank_matrix_three] at he
    omega
  have hfirst : Module.finrank K L < 3 := by
    by_contra! h
    apply hseven
    exact pow_eq_top_of_finrank_add_le L u hu hfull (j := 1) (t := 6) (by decide)
      (by rw [finrank_matrix_three, pow_one]; omega)
  have hsecond : Module.finrank K ↥(L ^ 2) < 4 := by
    by_contra! h
    exact hseven (pow_eq_top_of_finrank_add_le L u hu hfull (j := 2) (t := 5) (by decide)
      (by rw [finrank_matrix_three]; omega))
  have hproper : L ^ 1 ≠ ⊤ := by
    intro ht
    exact hseven (pow_eq_top_of_le L (by decide : 0 < 1) ht (by decide))
  have hg := finrank_pow_lt_of_unit_mem L 1 1 u hfull (by decide)
    (by simpa using hu) hproper
  rw [pow_one, show 1 + 1 = 2 by decide] at hg
  omega

private theorem span_pair_of_finrank_two (L : Submodule K Mat) {A : Mat}
    (hA : A ∈ L) (hAnz : A ≠ 0) (hdim : Module.finrank K L = 2) :
    ∃ B ∈ L, B ∉ Submodule.span K ({A} : Set Mat) ∧
      Submodule.span K ({A, B} : Set Mat) = L := by
  classical
  let P := Submodule.span K ({A} : Set Mat)
  have hp : P ≤ L := (Submodule.span_singleton_le_iff_mem _ _).2 hA
  have hdimP : Module.finrank K P = 1 := finrank_span_singleton hAnz
  have hnot : ¬ L ≤ P := by
    intro h
    have hl := Submodule.finrank_mono h
    omega
  obtain ⟨B, hB, hBP⟩ : ∃ B ∈ L, B ∉ P := by
    simpa only [IsConcreteLE.le_iff, not_forall, exists_prop] using hnot
  refine ⟨B, hB, hBP, ?_⟩
  let Q := Submodule.span K ({A, B} : Set Mat)
  have hpq : P ≤ Q := Submodule.span_mono (by simp)
  have hlt : P < Q := lt_of_le_not_ge hpq
    (fun h => hBP (h (Submodule.subset_span (by simp))))
  have hq : Q ≤ L := Submodule.span_le.2 (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hA
    · exact hB)
  have hr := Submodule.finrank_lt_finrank_of_lt hlt
  have heq : Q = L := Submodule.eq_of_le_of_finrank_le hq (by omega)
  exact heq

private theorem exists_quadratic_relation (L : Submodule K Mat)
    (A : Matˣ) {B : Mat} (hA : (A : Mat) ∈ L) (hB : B ∈ L)
    (hBA : B ∉ Submodule.span K ({(A : Mat)} : Set Mat))
    (hdim : Module.finrank K ↥(L ^ 2) < 4) :
    ∃ a b c d : K, (c ≠ 0 ∨ d ≠ 0) ∧
      B * (c • (A : Mat) + d • B) = (A : Mat) * (a • (A : Mat) + b • B) := by
  let w : Fin 4 → Mat := ![(A : Mat) * A, (A : Mat) * B, B * A, B * B]
  have hmem (i : Fin 4) : w i ∈ L ^ 2 := by
    rw [pow_two]
    fin_cases i
    · exact Submodule.mul_mem_mul hA hA
    · exact Submodule.mul_mem_mul hA hB
    · exact Submodule.mul_mem_mul hB hA
    · exact Submodule.mul_mem_mul hB hB
  have hdep : ¬ LinearIndependent K w := by
    intro hi
    have hle := Submodule.finrank_mono (Submodule.span_le.2
      (fun _ ⟨i, hi⟩ => hi ▸ hmem i) : Submodule.span K (Set.range w) ≤ L ^ 2)
    rw [finrank_span_eq_card hi, Fintype.card_fin] at hle
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hdep
  rw [Fin.sum_univ_four] at hg
  change g 0 • ((A : Mat) * A) + g 1 • ((A : Mat) * B) +
    g 2 • (B * A) + g 3 • (B * B) = 0 at hg
  have hc : g 2 ≠ 0 ∨ g 3 ≠ 0 := by
    by_contra! hz
    have h := hg
    rw [hz.1, hz.2, zero_smul, zero_smul, add_zero, add_zero, ← mul_smul_comm,
      ← mul_smul_comm, ← mul_add] at h
    have hlin := Units.mul_right_inj A |>.mp (h.trans (mul_zero (A : Mat)).symm)
    have hb : g 1 = 0 := by
      by_contra hb
      apply hBA
      refine Submodule.mem_span_singleton.2 ⟨-(g 1)⁻¹ * g 0, ?_⟩
      have he : g 1 • B = -(g 0 • (A : Mat)) := eq_neg_of_add_eq_zero_right hlin
      calc
        _ = (g 1)⁻¹ • (-(g 0 • (A : Mat))) := by simp [smul_smul, neg_mul]
        _ = B := by rw [← he, smul_smul, inv_mul_cancel₀ hb, one_smul]
    have ha : g 0 = 0 := by
      rw [hb, zero_smul, add_zero] at hlin
      exact (smul_eq_zero.1 hlin).resolve_right A.ne_zero
    fin_cases i
    · exact hi ha
    · exact hi hb
    · exact hi hz.1
    · exact hi hz.2
  refine ⟨-g 0, -g 1, g 2, g 3, hc, ?_⟩
  simp only [mul_add, mul_smul_comm, neg_smul, ← neg_add, mul_neg]
  apply eq_neg_of_add_eq_zero_left
  simpa [add_assoc, add_left_comm, add_comm] using hg

-- Products preserve an invariant vector subspace whenever the generators do.
private def preserving (W : Submodule K (Fin 3 → K)) : Subalgebra K Mat where
  carrier := {M | ∀ v ∈ W, M *ᵥ v ∈ W}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro A B hA hB v hv
    rw [Matrix.add_mulVec]
    exact W.add_mem (hA v hv) (hB v hv)
  mul_mem' := by
    intro A B hA hB v hv
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hB _ hv)
  algebraMap_mem' := by
    intro c v hv
    simpa [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec] using W.smul_mem c hv

private theorem pow_le_of_le_subalgebra (L : Submodule K Mat) (S : Subalgebra K Mat)
    (hL : L ≤ S.toSubmodule) (m : ℕ) : L ^ m ≤ S.toSubmodule := by
  induction m with
  | zero =>
      rw [pow_zero, Submodule.one_eq_span]
      exact Submodule.span_singleton_le_iff_mem _ _ |>.2 S.one_mem
  | succ m ih =>
      rw [pow_succ]
      exact Submodule.mul_le.2 (fun x hx y hy => S.mul_mem (ih hx) (hL hy))

private theorem invariant_eq_top (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (W : Submodule K (Fin 3 → K)) {x : Fin 3 → K} (hx : x ∈ W) (hx0 : x ≠ 0)
    (hL : L ≤ (preserving W).toSubmodule) : W = ⊤ := by
  obtain ⟨m, _, hm⟩ := hfull
  have htop := pow_le_of_le_subalgebra L (preserving W) hL m
  rw [hm] at htop
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! h
    exact hx0 (funext h)
  apply top_unique
  intro y _
  let M : Mat := Matrix.vecMulVec ((x j)⁻¹ • y) (Pi.single j 1)
  have hMy : M *ᵥ x = y := by
    dsimp only [M]
    rw [Matrix.vecMulVec_mulVec, single_dotProduct, one_mul]
    ext i
    change (x j)⁻¹ * y i * x j = y i
    rw [mul_right_comm, inv_mul_cancel₀ hj, one_mul]
  rw [← hMy]
  exact (show ∀ v ∈ W, M *ᵥ v ∈ W from htop (show M ∈ (⊤ : Submodule K Mat) from trivial)) x hx

private def conjugateByInverse (A : Matˣ) : Mat →ₐ[K] Mat where
  toFun X := (↑A⁻¹ : Mat) * X * A
  map_one' := by simp
  map_mul' X Y := by
    change (↑A⁻¹ : Mat) * (X * Y) * A = ((↑A⁻¹ : Mat) * X * A) * ((↑A⁻¹ : Mat) * Y * A)
    calc
      _ = (↑A⁻¹ : Mat) * X * (((A : Mat) * (↑A⁻¹ : Mat)) * Y) * A := by
        rw [Units.mul_inv, one_mul, mul_assoc (↑A⁻¹ : Mat) X Y]
      _ = _ := by noncomm_ring
  map_zero' := by simp
  map_add' X Y := by simp [mul_add, add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp

private theorem impossible_of_unit_factor (L : Submodule K Mat) (A : Matˣ) (C : Mat)
    (hspan : L = Submodule.span K ({(A : Mat), (A : Mat) * C} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    {a b c d : K} (hunit : IsUnit (c • (1 : Mat) + d • C))
    (hrel : conjugateByInverse A C * (c • (1 : Mat) + d • C) = a • (1 : Mat) + b • C) :
    False := by
  let S := Algebra.adjoin K ({C} : Set Mat)
  have hC : C ∈ S := Algebra.self_mem_adjoin_singleton K C
  let X : S := ⟨c • (1 : Mat) + d • C, S.add_mem (S.smul_mem S.one_mem c) (S.smul_mem hC d)⟩
  let Y : S := ⟨a • (1 : Mat) + b • C, S.add_mem (S.smul_mem S.one_mem a) (S.smul_mem hC b)⟩
  let f : S →ₗ[K] S :=
    { toFun p := p * X
      map_add' p q := add_mul p q X
      map_smul' r p := smul_mul_assoc r p X }
  have hinj : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact hunit.mul_left_inj.1 (congrArg Subtype.val h)
  obtain ⟨p, hp⟩ := (LinearMap.injective_iff_surjective.1 hinj) Y
  have hp' : (p : Mat) * (X : Mat) = (Y : Mat) := congrArg Subtype.val hp
  have hfC : conjugateByInverse A C ∈ S := by
    have he : conjugateByInverse A C = (p : Mat) := hunit.mul_left_inj.1 (hrel.trans hp'.symm)
    rw [he]
    exact p.property
  have hmap : S.map (conjugateByInverse A) ≤ S := by
    dsimp only [S]
    rw [AlgHom.map_adjoin_singleton]
    exact Algebra.adjoin_singleton_le hfC
  let V (m : ℕ) := S.toSubmodule.map (Algebra.lmul K Mat ((A : Mat) ^ m))
  have hbase : L ≤ V 1 := by
    rw [hspan]
    apply Submodule.span_le.2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.mem_map.2 ⟨1, S.one_mem, by simp⟩
    · exact Submodule.mem_map.2 ⟨C, hC, by simp⟩
  have hpows (m : ℕ) : L ^ m ≤ V m := by
    induction m with
    | zero =>
        rw [pow_zero, Submodule.one_eq_span]
        exact (Submodule.span_singleton_le_iff_mem _ _).2
          (Submodule.mem_map.2 ⟨1, S.one_mem, by simp⟩)
    | succ m ih =>
        rw [pow_succ]
        apply Submodule.mul_le.2
        intro x hx y hy
        obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 (ih hx)
        obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 (hbase hy)
        have hm : conjugateByInverse A p ∈ S :=
          hmap (Subalgebra.mem_map.2 ⟨p, hp, rfl⟩)
        refine Submodule.mem_map.2 ⟨conjugateByInverse A p * q, S.mul_mem hm hq, ?_⟩
        change (A : Mat) ^ (m + 1) * ((↑A⁻¹ : Mat) * p * A * q) =
          ((A : Mat) ^ m * p) * ((A : Mat) ^ 1 * q)
        rw [pow_succ, pow_one]
        simp [mul_assoc, ← mul_assoc (A : Mat)]
  obtain ⟨m, _, hm⟩ := hfull
  have hV : V m = ⊤ := top_unique (hm ▸ hpows m)
  have hS : S.toSubmodule = ⊤ := by
    apply top_unique
    intro x _
    have hx : (A : Mat) ^ m * x ∈ V m := hV.symm ▸ Submodule.mem_top
    obtain ⟨z, hz, he⟩ := Submodule.mem_map.1 hx
    have he' : (A : Mat) ^ m * z = (A : Mat) ^ m * x := he
    have heq : z = x := ((A.isUnit.pow m).mul_right_inj).1 he'
    exact heq ▸ hz
  let E : Mat := Matrix.single 0 1 1
  let F : Mat := Matrix.single 1 0 1
  have hE : E ∈ S := show E ∈ S.toSubmodule from hS.symm ▸ Submodule.mem_top
  have hF : F ∈ S := show F ∈ S.toSubmodule from hS.symm ▸ Submodule.mem_top
  have hcomm : E * F = F * E := congrArg Subtype.val
    (mul_comm (⟨E, hE⟩ : S) (⟨F, hF⟩ : S))
  have hentries := congrFun₂ hcomm 0 0
  simp [E, F] at hentries

private theorem singular_factor_eq_zero_or_invariant (L : Submodule K Mat) (A : Matˣ)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (X : Mat)
    (hL : L = Submodule.span K ({(A : Mat), X} : Set Mat))
    (hX : X ≠ 0) (hSing : ¬ IsUnit X) {mu : K} (hr : X * X = mu • ((A : Mat) * X)) :
    X * X = 0 := by
  by_cases hm : mu = 0
  · simpa [hm] using hr
  let W := LinearMap.range X.mulVecLin
  have hXa : ∀ w ∈ W, (A : Mat) *ᵥ w ∈ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨mu⁻¹ • (X *ᵥ v), ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hr, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hm, one_smul]
    exact (Matrix.mulVec_mulVec v (A : Mat) X).symm
  have hXw : ∀ w ∈ W, X *ᵥ w ∈ W := fun w _ => ⟨w, rfl⟩
  have hW : W ≠ ⊥ := by
    intro he
    apply hX
    exact Matrix.toLin'.injective (by
      change X.mulVecLin = (0 : Mat).mulVecLin
      rw [LinearMap.range_eq_bot.mp he, Matrix.mulVecLin_zero])
  obtain ⟨w, hw, hw0⟩ := (W.ne_bot_iff).1 hW
  have htop := invariant_eq_top L hfull W hw hw0 (by
    rw [hL]
    apply Submodule.span_le.2
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hXa
    · exact hXw)
  have hunit : IsUnit X := Matrix.mulVec_surjective_iff_isUnit.1
    (LinearMap.range_eq_top.1 htop)
  exact (hSing hunit).elim

/-- In dimension three an eventually full two-generator space with an invertible
generator and a three-dimensional square has a square-zero generator of rank one. -/
theorem exists_rank_one_square_zero_of_finrank_two_and_three
    (L : Submodule K Mat) (A : Matˣ) (hA : (A : Mat) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hL : Module.finrank K L = 2) (hL2 : Module.finrank K ↥(L ^ 2) = 3) :
    ∃ X : Mat, L = Submodule.span K ({(A : Mat), X} : Set Mat) ∧
      X * X = 0 ∧ X.rank = 1 := by
  obtain ⟨B, hB, hBA, hspan⟩ := span_pair_of_finrank_two L hA A.ne_zero hL
  obtain ⟨a, b, c, d, hcd, hrel⟩ := exists_quadratic_relation L A hA hB hBA (by omega)
  let C : Mat := (↑A⁻¹ : Mat) * B
  have hB' : (A : Mat) * C = B := by simp [C, ← mul_assoc]
  let X : Mat := c • (A : Mat) + d • B
  let Y : Mat := a • (A : Mat) + b • B
  change B * X = (A : Mat) * Y at hrel
  have hXC : (A : Mat) * (c • (1 : Mat) + d • C) = X := by
    simp [X, mul_add, hB']
  have hYC : (A : Mat) * (a • (1 : Mat) + b • C) = Y := by
    simp [Y, mul_add, hB']
  have hSing : ¬ IsUnit X := by
    intro hU
    have hf : IsUnit (c • (1 : Mat) + d • C) := by
      have he : c • (1 : Mat) + d • C = (↑A⁻¹ : Mat) * X := by
        rw [← hXC, ← mul_assoc, Units.inv_mul, one_mul]
      rw [he]
      exact A⁻¹.isUnit.mul hU
    apply impossible_of_unit_factor L A C (by rw [hB', hspan]) hfull hf
    apply A.mul_right_inj.1
    apply A.mul_right_inj.1
    have hconj : (A : Mat) * conjugateByInverse A C = C * A := by
      change (A : Mat) * ((↑A⁻¹ : Mat) * C * A) = C * A
      rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    calc
      _ = (A : Mat) * (C * X) := by
        rw [← mul_assoc (A : Mat) (conjugateByInverse A C), hconj, mul_assoc C, hXC]
      _ = B * X := by rw [← mul_assoc, hB']
      _ = _ := by rw [hrel, hYC]
  have hd : d ≠ 0 := by
    intro hd
    have hc := hcd.resolve_right (by simp [hd])
    apply hSing
    have he : X = algebraMap K Mat c * (A : Mat) := by
      simp [X, hd, Algebra.smul_def]
    rw [he]
    exact (hc.isUnit.map (algebraMap K Mat)).mul A.isUnit
  have hshift : B = d⁻¹ • X + (-(d⁻¹ * c)) • (A : Mat) := by
    dsimp only [X]
    rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hd, one_smul, neg_smul]
    abel
  have hX : X ≠ 0 := by
    intro hz
    apply hBA
    exact Submodule.mem_span_singleton.2 ⟨-(d⁻¹ * c), by simpa [hz] using hshift.symm⟩
  have hxspan : L = Submodule.span K ({(A : Mat), X} : Set Mat) := by
    apply le_antisymm
    · rw [← hspan]
      apply Submodule.span_le.2
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.mem_span_pair.2 ⟨-(d⁻¹ * c), d⁻¹, by rw [add_comm]; exact hshift.symm⟩
    · apply Submodule.span_le.2
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hA
      · exact L.add_mem (L.smul_mem c hA) (L.smul_mem d hB)
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin 3 → K, v ≠ 0 ∧ X *ᵥ v = 0 := by
    have hker : LinearMap.ker X.mulVecLin ≠ ⊥ := by
      exact fun h => hSing (Matrix.mulVec_injective_iff_isUnit.1 (LinearMap.ker_eq_bot.1 h))
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hker
    exact ⟨v, hv0, hv⟩
  have hYv : Y *ᵥ v = 0 := by
    apply (Matrix.mulVec_injective_of_isUnit A.isUnit)
    calc
      (A : Mat) *ᵥ (Y *ᵥ v) = (B * X) *ᵥ v := by rw [Matrix.mulVec_mulVec, hrel]
      _ = (A : Mat) *ᵥ (0 : Fin 3 → K) := by rw [← Matrix.mulVec_mulVec, hv]; simp
  have hcross : d • Y - b • X = (d * a - b * c) • (A : Mat) := by
    simp only [X, Y, smul_add, smul_smul, sub_smul, mul_comm d b]
    abel
  have hcoeff : d * a - b * c = 0 := by
    have hv' : (d * a - b * c) • ((A : Mat) *ᵥ v) = 0 := by
      rw [← Matrix.smul_mulVec, ← hcross, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hYv, hv]
      simp
    refine (smul_eq_zero.1 hv').resolve_right fun h => hv0 ?_
    exact Matrix.mulVec_injective_of_isUnit A.isUnit (by simpa using h)
  have hscale : d • Y = b • X := sub_eq_zero.1 (by rw [hcross, hcoeff, zero_smul])
  have hquad : X * X = (c + b) • ((A : Mat) * X) := calc
    X * X = c • ((A : Mat) * X) + d • (B * X) := by
      rw [show X = c • (A : Mat) + d • B from rfl, add_mul, smul_mul_assoc, smul_mul_assoc]
    _ = (c + b) • ((A : Mat) * X) := by
      rw [hrel, ← mul_smul_comm d (A : Mat) Y, hscale, mul_smul_comm, add_smul]
  have hz := singular_factor_eq_zero_or_invariant L A hfull X hxspan hX hSing hquad
  refine ⟨X, hxspan, hz, ?_⟩
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
  rw [Fintype.card_fin] at hle
  have hpos : X.rank ≠ 0 := by
    intro he
    apply hX
    have hr : LinearMap.range X.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 he
    apply Matrix.toLin'.injective
    change X.mulVecLin = (0 : Mat).mulVecLin
    rw [LinearMap.range_eq_bot.mp hr, Matrix.mulVecLin_zero]
  omega

private theorem exists_outer_product_of_rank_one {B : Mat} (hB : B.rank = 1) :
    ∃ u v : Fin 3 → K, u ≠ 0 ∧ v ≠ 0 ∧ B = Matrix.vecMulVec u v := by
  classical
  let W := Submodule.span K (Set.range B.col)
  have hW : Module.finrank K W = 1 := (Matrix.rank_eq_finrank_span_cols B).symm.trans hB
  have hn : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW
    contradiction
  obtain ⟨u, hu, hu0⟩ := W.ne_bot_iff.1 hn
  have hcol (j : Fin 3) : ∃ c : K, c • (⟨u, hu⟩ : W) =
      (⟨B.col j, Submodule.subset_span ⟨j, rfl⟩⟩ : W) :=
    exists_smul_eq_of_finrank_eq_one hW (by intro h; exact hu0 (congrArg Subtype.val h)) _
  choose v hv using hcol
  have he : B = Matrix.vecMulVec u v := by
    ext i j
    have hc : (v j) • u = B.col j := congrArg Subtype.val (hv j)
    have h := congrFun hc i
    change v j * u i = B i j at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h.symm
  refine ⟨u, v, hu0, ?_, he⟩
  intro hv0
  rw [he, hv0, Matrix.vecMulVec_zero] at hB
  simp at hB

private theorem third_power_eq (A : Mat) :
    ∃ x y : K, A ^ 3 = x • A ^ 2 + y • A + A.det • (1 : Mat) := by
  have h := Matrix.aeval_self_charpoly A
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h
  have hc : A.charpoly.coeff 3 = 1 := by
    have he : A.charpoly.coeff A.charpoly.natDegree = 1 :=
      A.charpoly_monic.coeff_natDegree
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using he
  change (∑ i ∈ Finset.range 4, A.charpoly.coeff i • A ^ i) = 0 at h
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, hc, one_smul, pow_zero, pow_one] at h
  have hdet : A.det = -A.charpoly.coeff 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
    ring
  refine ⟨-A.charpoly.coeff 2, -A.charpoly.coeff 1, ?_⟩
  rw [hdet]
  rw [eq_neg_of_add_eq_zero_right h]
  simp only [neg_smul, neg_add]
  abel

private theorem span_column_orbit
    (L : Submodule K Mat) {A : Mat} {u v : Fin 3 → K} (hu : u ≠ 0)
    (hL : L = Submodule.span K ({A, Matrix.vecMulVec u v} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    Submodule.span K (Set.range (fun i : Fin 3 => A ^ (i : ℕ) *ᵥ u)) = ⊤ := by
  let w (i : Fin 3) := A ^ (i : ℕ) *ᵥ u
  let W := Submodule.span K (Set.range w)
  have hw (i : Fin 3) : w i ∈ W := Submodule.subset_span (Set.mem_range_self i)
  have hw0 : w 0 = u := by simp [w]
  have hA : ∀ z ∈ W, A *ᵥ z ∈ W := by
    intro z hz
    change A.mulVecLin z ∈ W
    refine (show W ≤ W.comap A.mulVecLin from Submodule.span_le.2 ?_) hz
    rintro _ ⟨i, rfl⟩
    change A *ᵥ w i ∈ W
    fin_cases i
    · simpa [w] using hw 1
    · simpa [w, Matrix.mulVec_mulVec, pow_two] using hw 2
    · obtain ⟨a, b, h⟩ := third_power_eq A
      have hs : a • w 2 + b • w 1 + A.det • w 0 ∈ W :=
        W.add_mem (W.add_mem (W.smul_mem a (hw 2)) (W.smul_mem b (hw 1))) (W.smul_mem A.det (hw 0))
      change A *ᵥ (A ^ 2 *ᵥ u) ∈ W
      rw [Matrix.mulVec_mulVec, ← pow_succ', h]
      change a • (A ^ 2 *ᵥ u) + b • (A ^ 1 *ᵥ u) + A.det • (A ^ 0 *ᵥ u) ∈ W at hs
      simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, pow_zero, pow_one] using hs
  have hB : ∀ z ∈ W, Matrix.vecMulVec u v *ᵥ z ∈ W := by
    intro z _
    rw [Matrix.vecMulVec_mulVec]
    rw [op_smul_eq_smul]
    exact W.smul_mem (v ⬝ᵥ z) (hw0 ▸ hw 0)
  exact invariant_eq_top L hfull W (hw0 ▸ hw 0) hu (by
    rw [hL]
    apply Submodule.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hA
    · exact hB)

private theorem span_row_orbit
    (L : Submodule K Mat) {A : Mat} {u v : Fin 3 → K} (hv : v ≠ 0)
    (hL : L = Submodule.span K ({A, Matrix.vecMulVec u v} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    Submodule.span K (Set.range (fun i : Fin 3 => v ᵥ* A ^ (i : ℕ))) = ⊤ := by
  let e : Mat ≃ₗ[K] Mat := Matrix.transposeLinearEquiv _ _ _ _
  have hmap (m : ℕ) : (L ^ m).map e.toLinearMap = L.map e.toLinearMap ^ m := by
    induction m with
    | zero =>
        simp only [pow_zero, Submodule.one_eq_span, Submodule.map_span, Set.image_singleton]
        change Submodule.span K ({(1 : Mat)ᵀ} : Set Mat) = _
        rw [Matrix.transpose_one]
    | succ m ih =>
        rw [pow_succ, pow_succ' (L.map e.toLinearMap), ← ih]
        apply le_antisymm
        · rw [Submodule.map_le_iff_le_comap]
          apply Submodule.mul_le.2
          intro x hx y hy
          change (x * y)ᵀ ∈ L.map e.toLinearMap * (L ^ m).map e.toLinearMap
          rw [Matrix.transpose_mul]
          exact Submodule.mul_mem_mul (Submodule.mem_map_of_mem (f := e.toLinearMap) hy)
            (Submodule.mem_map_of_mem (f := e.toLinearMap) hx)
        · apply Submodule.mul_le.2
          rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
          refine Submodule.mem_map.2 ⟨x * y, Submodule.mul_mem_mul hx hy, ?_⟩
          change (x * y)ᵀ = yᵀ * xᵀ
          exact Matrix.transpose_mul _ _
  have hspan : L.map e.toLinearMap = Submodule.span K ({Aᵀ, Matrix.vecMulVec v u} : Set Mat) := by
    rw [hL, Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    congr 1
    change {Aᵀ, (Matrix.vecMulVec u v)ᵀ} = {Aᵀ, Matrix.vecMulVec v u}
    rw [Matrix.transpose_vecMulVec]
  have hf : ∃ m : ℕ, 0 < m ∧ L.map e.toLinearMap ^ m = ⊤ := by
    obtain ⟨m, hm, he⟩ := hfull
    exact ⟨m, hm, by rw [← hmap, he, Submodule.map_eq_top_iff]⟩
  simpa only [← Matrix.transpose_pow, Matrix.mulVec_transpose] using
    span_column_orbit (L.map e.toLinearMap) hv hspan hf

private theorem return_product (A : Mat) (u v : Fin 3 → K) (j : ℕ) :
    Matrix.vecMulVec u v * A ^ j * Matrix.vecMulVec u v =
      (v ⬝ᵥ (A ^ j *ᵥ u)) • Matrix.vecMulVec u v := by
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec,
    Matrix.vecMulVec_smul]

/-- A square-zero rank-one generator has a return of order one or two.
If both returns are nonzero, insertions of lengths two and three give fullness at length seven. -/
theorem rank_one_returns
    (L : Submodule K Mat) {A : Matˣ} {B : Mat}
    (hB : B.rank = 1) (hzero : B * B = 0)
    (hL : L = Submodule.span K ({(A : Mat), B} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    ∃ u v : Fin 3 → K, B = Matrix.vecMulVec u v ∧ v ⬝ᵥ u = 0 ∧
      ((v ⬝ᵥ ((A : Mat) *ᵥ u)) ≠ 0 ∨ (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) ≠ 0) ∧
      ((v ⬝ᵥ ((A : Mat) *ᵥ u)) ≠ 0 → (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) ≠ 0 → L ^ 7 = ⊤) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_outer_product_of_rank_one hB
  let M := Matrix.vecMulVec u v
  have hM : M ≠ 0 := by
    intro he
    change M.rank = 1 at hB
    rw [he, Matrix.rank_zero] at hB
    contradiction
  let P : Mat := A
  let c (j : ℕ) := v ⬝ᵥ (P ^ j *ᵥ u)
  have hreturn (j : ℕ) : M * P ^ j * M = c j • M := return_product P u v j
  have h0 : v ⬝ᵥ u = 0 := by
    have h := hreturn 0
    simp only [c, pow_zero, mul_one, Matrix.one_mulVec, M, hzero] at h
    exact (smul_eq_zero.1 h.symm).resolve_right hM
  have huorb := span_column_orbit L hu hL hfull
  have hvorb := span_row_orbit L hv hL hfull
  have hn : (v ⬝ᵥ (P *ᵥ u)) ≠ 0 ∨ (v ⬝ᵥ (P ^ 2 *ᵥ u)) ≠ 0 := by
    by_contra! hz
    let f : (Fin 3 → K) →ₗ[K] K := (dotProductBilin K K) v
    have hle : Submodule.span K (Set.range (fun i : Fin 3 => P ^ (i : ℕ) *ᵥ u)) ≤ f.ker := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      change v ⬝ᵥ (P ^ (i : ℕ) *ᵥ u) = 0
      fin_cases i
      · simpa using h0
      · simpa using hz.1
      · exact hz.2
    change _ ≤ f.ker at hle
    rw [huorb] at hle
    apply hv
    ext i
    have hi : Pi.single i (1 : K) ∈ f.ker := hle Submodule.mem_top
    change v ⬝ᵥ Pi.single i 1 = 0 at hi
    simpa only [dotProduct_single, mul_one, Pi.zero_apply] using hi
  refine ⟨u, v, rfl, h0, hn, ?_⟩
  intro h1 h2
  have hP : P ∈ L := hL.symm ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hML : M ∈ L := hL.symm ▸ Submodule.subset_span (by simp [M])
  have hmul {m n : ℕ} {X Y : Mat} (hX : X ∈ L ^ m) (hY : Y ∈ L ^ n) :
      X * Y ∈ L ^ (m + n) := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hX hY
  have hM1 : M ∈ L ^ 1 := by simpa using hML
  have hpad (n : ℕ) (hn : M ∈ L ^ n) (j : ℕ) (hj : c j ≠ 0) :
      M ∈ L ^ (n + j + 1) := by
    have hw := hmul (hmul hn (Submodule.pow_mem_pow L hP j)) hM1
    rw [hreturn] at hw
    simpa only [smul_smul, inv_mul_cancel₀ hj, one_smul] using (L ^ (n + j + 1)).smul_mem (c j)⁻¹ hw
  have hM3 : M ∈ L ^ 3 := hpad 1 hM1 1 (by simpa [c] using h1)
  have hM4 : M ∈ L ^ 4 := hpad 1 hM1 2 h2
  have hM5 : M ∈ L ^ 5 := hpad 3 hM3 1 (by simpa [c] using h1)
  have hM6 : M ∈ L ^ 6 := hpad 4 hM4 1 (by simpa [c] using h1)
  have hM7 : M ∈ L ^ 7 := hpad 5 hM5 1 (by simpa [c] using h1)
  have hout (i j : Fin 3) : Matrix.vecMulVec (P ^ (i : ℕ) *ᵥ u) (v ᵥ* P ^ (j : ℕ)) ∈ L ^ 7 := by
    rw [← Matrix.mul_vecMulVec, ← Matrix.vecMulVec_mul]
    have hlength : ∃ n : ℕ, M ∈ L ^ n ∧ (i : ℕ) + (j : ℕ) + n = 7 := by
      fin_cases i <;> fin_cases j <;> first
        | exact ⟨3, hM3, rfl⟩
        | exact ⟨4, hM4, rfl⟩
        | exact ⟨5, hM5, rfl⟩
        | exact ⟨6, hM6, rfl⟩
        | exact ⟨7, hM7, rfl⟩
    obtain ⟨n, hn, he⟩ := hlength
    rw [show 7 = (i : ℕ) + (n + (j : ℕ)) by omega]
    exact hmul (Submodule.pow_mem_pow L hP _) (hmul hn (Submodule.pow_mem_pow L hP _))
  have houter (x y : Fin 3 → K) : Matrix.vecMulVec x y ∈ L ^ 7 := by
    let V := L ^ 7
    change Matrix.vecMulVec x y ∈ V
    have hx : x ∈ Submodule.span K (Set.range (fun i : Fin 3 => P ^ (i : ℕ) *ᵥ u)) :=
      huorb.symm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have hy : y ∈ Submodule.span K (Set.range (fun j : Fin 3 => v ᵥ* P ^ (j : ℕ))) :=
          hvorb.symm ▸ Submodule.mem_top
        induction hy using Submodule.span_induction with
        | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hout i j
        | zero => simp
        | add y z _ _ hy hz => simpa only [Matrix.vecMulVec_add] using V.add_mem hy hz
        | smul a y _ hy => simpa only [Matrix.vecMulVec_smul] using V.smul_mem a hy
    | zero => simp
    | add x z _ _ hx hz => simpa only [Matrix.add_vecMulVec] using V.add_mem hx hz
    | smul a x _ hx => simpa only [Matrix.smul_vecMulVec] using V.smul_mem a hx
  classical
  apply top_unique
  intro T _
  rw [Matrix.matrix_eq_sum_single T]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  have he : (T i j) • (Matrix.single i j (1 : K)) = Matrix.single i j (T i j) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [← he, Matrix.single_eq_single_vecMulVec_single]
  exact (L ^ 7).smul_mem _ (houter _ _)

/-- Any eventually full size-three example with an invertible generator whose
seventh power is proper has a square-zero outer-product generator and exactly
one nonzero return among the first two. -/
theorem single_rank_one_return_of_pow_seven_ne_top
    (L : Submodule K Mat) (A : Matˣ) (hA : (A : Mat) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hseven : L ^ 7 ≠ ⊤) :
    ∃ u v : Fin 3 → K,
      L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat) ∧
      (Matrix.vecMulVec u v).rank = 1 ∧ v ⬝ᵥ u = 0 ∧
      (((v ⬝ᵥ ((A : Mat) *ᵥ u)) ≠ 0 ∧ (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) = 0) ∨
       ((v ⬝ᵥ ((A : Mat) *ᵥ u)) = 0 ∧ (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) ≠ 0)) := by
  classical
  obtain ⟨hL, hL2⟩ := finrank_eq_two_and_three_of_pow_seven_ne_top L A hA hfull hseven
  obtain ⟨B, hspan, hzero, hrank⟩ :=
    exists_rank_one_square_zero_of_finrank_two_and_three L A hA hfull hL hL2
  obtain ⟨u, v, rfl, h0, hreturn, hpair⟩ := rank_one_returns L hrank hzero hspan hfull
  refine ⟨u, v, hspan, hrank, h0, ?_⟩
  rcases hreturn with h1 | h2
  · exact Or.inl ⟨h1, by_contra fun h2 => hseven (hpair h1 h2)⟩
  · exact Or.inr ⟨by_contra fun h1 => hseven (hpair h1 h2), h2⟩

private theorem isUnit_of_span_columns (P : Mat)
    (h : Submodule.span K (Set.range P.col) = ⊤) : IsUnit P :=
  Matrix.mulVec_surjective_iff_isUnit.1
    (LinearMap.range_eq_top.1 ((Matrix.range_mulVecLin P).trans h))

private theorem periodic_outer_five_linearIndependent (x y z : K)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    LinearIndependent K ![
      (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
      x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 0) +
        y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 0) +
        z • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
      x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 2) +
        y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 1) +
        z • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
      (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 1),
      (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 2)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrFun₂ hg 0 0
  have h20 := congrFun₂ hg 2 0
  have h10 := congrFun₂ hg 1 0
  have h02 := congrFun₂ hg 0 2
  have h01 := congrFun₂ hg 0 1
  have h21 := congrFun₂ hg 2 1
  have h12 := congrFun₂ hg 1 2
  simp [Fin.sum_univ_succ, Matrix.stdBasis, Pi.single_apply] at h00 h20 h10 h02 h01 h21 h12
  have g1 : g 1 = 0 := by
    rcases hxy with hx | hy
    · exact h20.resolve_right hx
    · exact h10.resolve_right hy
  have g2 : g 2 = 0 := by
    rcases hxy with hx | hy
    · exact h02.resolve_right hx
    · exact h01.resolve_right hy
  have g0 : g 0 = 0 := by simpa [g1, g2] using h00
  have g3 : g 3 = 0 := by simpa using h21
  have g4 : g 4 = 0 := by simpa using h12
  intro i
  fin_cases i <;> assumption

/-- A nonzero first return and zero second return force at least five independent
matrices in the exact cube of an eventually full span with an invertible generator. -/
theorem five_le_finrank_cube_of_first_return
    (L : Submodule K Mat) (A : Matˣ) (u v : Fin 3 → K)
    (hL : L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (h0 : v ⬝ᵥ u = 0) (h1 : v ⬝ᵥ ((A : Mat) *ᵥ u) ≠ 0)
    (h2 : v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u) = 0) :
    5 ≤ Module.finrank K ↥(L ^ 3) := by
  classical
  let P : Mat := A
  let B := Matrix.vecMulVec u v
  let w (i : Fin 3) := P ^ (i : ℕ) *ᵥ u
  let r (j : Fin 3) := v ᵥ* P ^ (j : ℕ)
  have hu : u ≠ 0 := by rintro rfl; simp at h1
  have hv : v ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨U, hU⟩ := isUnit_of_span_columns (Matrix.of fun i j => w j i)
    (span_column_orbit L hu hL hfull)
  have hVunit : IsUnit (Matrix.of r : Mat) :=
    (Matrix.isUnit_transpose (Matrix.of r : Mat)).1 (isUnit_of_span_columns (Matrix.of r)ᵀ
      (span_row_orbit L hv hL hfull))
  obtain ⟨V, hV⟩ := hVunit
  have hcol (i : Fin 3) : (U : Mat).col i = w i := by rw [hU]; rfl
  have hrow (j : Fin 3) : (V : Mat).row j = r j := by rw [hV]; rfl
  let e := (U.mulLeftLinearEquiv K Mat).trans (V.mulRightLinearEquiv K)
  let b := (Matrix.stdBasis K (Fin 3) (Fin 3)).map e
  have hb (i j : Fin 3) : b (i, j) = Matrix.vecMulVec (w i) (r j) := by
    change e (Matrix.stdBasis K _ _ (i, j)) = _
    rw [Matrix.stdBasis_eq_single, Matrix.single_eq_single_vecMulVec_single]
    change (U : Mat) * Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) * (V : Mat) = _
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_single_one,
      Matrix.single_one_vecMul, hcol, hrow]
  have hP : P ∈ L := hL.symm ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hB : B ∈ L := hL.symm ▸ Submodule.subset_span (by simp [B])
  have hmul {m n : ℕ} {X Y : Mat} (hX : X ∈ L ^ m) (hY : Y ∈ L ^ n) :
      X * Y ∈ L ^ (m + n) := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hX hY
  have hB1 : B ∈ L ^ 1 := by simpa using hB
  have hB3 : B ∈ L ^ 3 := by
    let c : K := v ⬝ᵥ (P *ᵥ u)
    have hc : c ≠ 0 := h1
    have hw := hmul (hmul hB1 (Submodule.pow_mem_pow L hP 1)) hB1
    rw [return_product P u v 1, pow_one] at hw
    change c • B ∈ L ^ 3 at hw
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using (L ^ 3).smul_mem c⁻¹ hw
  have hword (i j : Fin 3) (hlen : (i : ℕ) + 1 + (j : ℕ) = 3) : b (i, j) ∈ L ^ 3 := by
    rw [hb, ← Matrix.vecMulVec_mul, ← Matrix.mul_vecMulVec]
    have hw := hmul (hmul (Submodule.pow_mem_pow L hP (i : ℕ)) hB1)
      (Submodule.pow_mem_pow L hP (j : ℕ))
    rwa [hlen] at hw
  -- Three cubic words and the padded generator occupy four distinct basis positions.
  let p : Fin 4 → Fin 3 × Fin 3 := ![(2, 0), (1, 1), (0, 2), (0, 0)]
  have hp : Function.Injective p := by
    change ∀ i j : Fin 4, p i = p j → i = j
    decide
  let W := Submodule.span K (Set.range (b ∘ p))
  have hdimW : Module.finrank K W = 4 := by
    simpa [W] using finrank_span_eq_card (b.linearIndependent.comp p hp)
  have hWL : W ≤ L ^ 3 := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hword 2 0 rfl
    · exact hword 1 1 rfl
    · exact hword 0 2 rfl
    · change b (0, 0) ∈ L ^ 3
      simpa [hb, w, r, B] using hB3
  let coord : (Fin 3 → K) →ₗ[K] K :=
    (LinearMap.proj 2).comp (↑U⁻¹ : Mat).mulVecLin
  have hcoord (i : Fin 3) : coord (w i) = (Pi.single i 1 : Fin 3 → K) 2 := by
    change ((↑U⁻¹ : Mat) *ᵥ w i) 2 = _
    rw [← hcol, ← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let eval (k : Fin 3) : Mat →ₗ[K] K := coord.comp ((Matrix.mulVecBilin K K).flip (w k))
  have heval (i j k : Fin 3) :
      eval k (b (i, j)) = (r j ⬝ᵥ w k) * (Pi.single i 1 : Fin 3 → K) 2 := by
    change coord (b (i, j) *ᵥ w k) = _
    rw [hb, Matrix.vecMulVec_mulVec, op_smul_eq_smul, map_smul, hcoord, smul_eq_mul]
  have hker (k : Fin 3) (hk : v ⬝ᵥ w k = 0) : W ≤ (eval k).ker := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    change eval k (b (p i)) = 0
    fin_cases i
    · change eval k (b (2, 0)) = 0
      rw [heval]
      simpa [r] using hk
    · change eval k (b (1, 1)) = 0
      simp [heval]
    · change eval k (b (0, 2)) = 0
      simp [heval]
    · change eval k (b (0, 0)) = 0
      simp [heval]
  -- In the last column-orbit coordinate, only the outer product at (2, 0) contributes.
  -- Its row is v, which annihilates both u and A^2 u.
  have hnot : P ^ 3 ∉ W := by
    intro hW
    obtain ⟨x, y, hrel⟩ := third_power_eq P
    have htest0 : coord (P ^ 3 *ᵥ u) = 0 := by
      have ht := hker 0 (by simpa [w] using h0) hW
      change coord (P ^ 3 *ᵥ w 0) = 0 at ht
      simpa [w] using ht
    have hx : x = 0 := by
      have ht := htest0
      rw [hrel, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, map_add, map_add, map_smul, map_smul, map_smul] at ht
      have ht' : x • coord (w 2) + y • coord (w 1) + P.det • coord (w 0) = 0 := by
        simpa [w] using ht
      simpa [hcoord] using ht'
    have htest2 := hker 2 h2 hW
    change coord (P ^ 3 *ᵥ (P ^ 2 *ᵥ u)) = 0 at htest2
    rw [Matrix.mulVec_mulVec, ← pow_add] at htest2
    have h5 : P ^ 5 = y • P ^ 3 + P.det • P ^ 2 := by
      calc
        P ^ 5 = P ^ 3 * P ^ 2 := pow_add P 3 2
        _ = (y • P + P.det • (1 : Mat)) * P ^ 2 := by
          exact congrArg (· * P ^ 2) (by simpa [hx] using hrel)
        _ = y • P ^ 3 + P.det • P ^ 2 := by
          rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_succ']
    rw [h5, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      map_add, map_smul, map_smul] at htest2
    change y • coord (P ^ 3 *ᵥ u) + P.det • coord (w 2) = 0 at htest2
    have hd : P.det = 0 := by simpa [htest0, hcoord] using htest2
    exact (isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det P).1 A.isUnit)) hd
  let W' := W ⊔ Submodule.span K ({P ^ 3} : Set Mat)
  have hP3 : P ^ 3 ∈ W' := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  have hlt : W < W' := lt_of_le_not_ge le_sup_left
    (fun h => hnot (h hP3))
  have hW'L : W' ≤ L ^ 3 := sup_le hWL
    ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.pow_mem_pow L hP 3))
  have hdim := (Submodule.finrank_lt_finrank_of_lt hlt).trans_le (Submodule.finrank_mono hW'L)
  omega

/-- A zero first return and nonzero second return give five independent
matrices in the exact fourth power, provided the characteristic-polynomial
coefficients do not both vanish. -/
theorem five_le_finrank_four_of_second_return
    (L : Submodule K Mat) (A : Matˣ) (u v : Fin 3 → K)
    (hL : L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat))
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (h0 : v ⬝ᵥ u = 0) (h1 : v ⬝ᵥ ((A : Mat) *ᵥ u) = 0)
    (h2 : v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u) ≠ 0)
    {x y : K} (hrel : (A : Mat) ^ 3 = x • (A : Mat) ^ 2 + y • (A : Mat) +
      (A : Mat).det • (1 : Mat)) (hxy : x ≠ 0 ∨ y ≠ 0) :
    5 ≤ Module.finrank K ↥(L ^ 4) := by
  classical
  let P : Mat := A
  let B := Matrix.vecMulVec u v
  let w (i : Fin 3) := P ^ (i : ℕ) *ᵥ u
  let r (j : Fin 3) := v ᵥ* P ^ (j : ℕ)
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h2
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨U, hU⟩ := isUnit_of_span_columns (Matrix.of fun i j => w j i)
    (span_column_orbit L hu hL hfull)
  have hVunit : IsUnit (Matrix.of r : Mat) :=
    (Matrix.isUnit_transpose (Matrix.of r : Mat)).1 (isUnit_of_span_columns (Matrix.of r)ᵀ
      (span_row_orbit L hv hL hfull))
  obtain ⟨V, hV⟩ := hVunit
  have hcol (i : Fin 3) : (U : Mat).col i = w i := by rw [hU]; rfl
  have hrow (j : Fin 3) : (V : Mat).row j = r j := by rw [hV]; rfl
  let e := (U.mulLeftLinearEquiv K Mat).trans (V.mulRightLinearEquiv K)
  let b := (Matrix.stdBasis K (Fin 3) (Fin 3)).map e
  have hb (i j : Fin 3) : b (i, j) = Matrix.vecMulVec (w i) (r j) := by
    change e (Matrix.stdBasis K _ _ (i, j)) = _
    rw [Matrix.stdBasis_eq_single, Matrix.single_eq_single_vecMulVec_single]
    change (U : Mat) * Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) * (V : Mat) = _
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_single_one,
      Matrix.single_one_vecMul, hcol, hrow]
  have hbcoord (i j a c : Fin 3) :
      (e.symm (b (a, c))) i j = if i = a ∧ j = c then 1 else 0 := by
    dsimp [b]
    by_cases hia : i = a <;> by_cases hjc : j = c <;>
      simp [Matrix.stdBasis, Pi.single_apply, hia, hjc]
  have hP : P ∈ L := hL.symm ▸ Submodule.subset_span (Set.mem_insert _ _)
  have hP1 : P ∈ L ^ 1 := by simpa using hP
  have hB : B ∈ L := hL.symm ▸ Submodule.subset_span (by simp [B])
  have hmul {m n : ℕ} {X Y : Mat} (hX : X ∈ L ^ m) (hY : Y ∈ L ^ n) :
      X * Y ∈ L ^ (m + n) := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hX hY
  have hB1 : B ∈ L ^ 1 := by simpa using hB
  have hB4 : B ∈ L ^ 4 := by
    let c : K := v ⬝ᵥ (P ^ 2 *ᵥ u)
    have hc : c ≠ 0 := h2
    have hw := hmul (hmul hB1 (Submodule.pow_mem_pow L hP 2)) hB1
    rw [return_product P u v 2] at hw
    change c • B ∈ L ^ 4 at hw
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using (L ^ 4).smul_mem c⁻¹ hw
  have hqmem (i : Fin 5) :
      (![B, P ^ 3 * B, B * P ^ 3, P ^ 2 * B * P, P * B * P ^ 2] i) ∈ L ^ 4 := by
    fin_cases i
    · exact hB4
    · change P ^ 3 * B ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul (Submodule.pow_mem_pow L hP 3) hB1)
    · change B * P ^ 3 ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul hB1 (Submodule.pow_mem_pow L hP 3))
    · change P ^ 2 * B * P ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul (hmul (Submodule.pow_mem_pow L hP 2) hB1) hP1)
    · change P * B * P ^ 2 ∈ L ^ 4
      simpa only [Nat.reduceAdd] using
        (hmul (hmul hP1 hB1) (Submodule.pow_mem_pow L hP 2))
  let q : Fin 5 → Mat := ![B, P ^ 3 * B, B * P ^ 3, P ^ 2 * B * P, P * B * P ^ 2]
  have he00 : e.symm B = (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0) := by
    have h : B = b (0, 0) := by simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 0 <;> by_cases hjc : c = 0 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he20 : e.symm (P ^ 2 * B) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 0) := by
    have h : P ^ 2 * B = b (2, 0) := by
      change P ^ 2 * Matrix.vecMulVec u v = b (2, 0)
      rw [Matrix.mul_vecMulVec]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 2 <;> by_cases hjc : c = 0 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he10 : e.symm (P * B) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 0) := by
    have h : P * B = b (1, 0) := by
      change P * Matrix.vecMulVec u v = b (1, 0)
      rw [Matrix.mul_vecMulVec]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 1 <;> by_cases hjc : c = 0 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he02 : e.symm (B * P ^ 2) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 2) := by
    have h : B * P ^ 2 = b (0, 2) := by
      change Matrix.vecMulVec u v * P ^ 2 = b (0, 2)
      rw [Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 0 <;> by_cases hjc : c = 2 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he01 : e.symm (B * P) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 1) := by
    have h : B * P = b (0, 1) := by
      change Matrix.vecMulVec u v * P = b (0, 1)
      rw [Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 0 <;> by_cases hjc : c = 1 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he21 : e.symm (P ^ 2 * B * P) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 1) := by
    have h : P ^ 2 * B * P = b (2, 1) := by
      change P ^ 2 * Matrix.vecMulVec u v * P = b (2, 1)
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 2 <;> by_cases hjc : c = 1 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have he12 : e.symm (P * B * P ^ 2) = (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 2) := by
    have h : P * B * P ^ 2 = b (1, 2) := by
      change P * Matrix.vecMulVec u v * P ^ 2 = b (1, 2)
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
      simpa [B, hb, w, r]
    rw [h]
    ext a c
    rw [hbcoord]
    by_cases hia : a = 1 <;> by_cases hjc : c = 2 <;>
      simp [Matrix.stdBasis, Matrix.single_apply, Pi.single_apply, hia, hjc]
  have hqrepr :
      (fun i => e.symm (q i)) = ![
        (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
        x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 0) +
          y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 0) +
          P.det • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
        x • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 2) +
          y • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 1) +
          P.det • (Matrix.stdBasis K (Fin 3) (Fin 3)) (0, 0),
        (Matrix.stdBasis K (Fin 3) (Fin 3)) (2, 1),
        (Matrix.stdBasis K (Fin 3) (Fin 3)) (1, 2)] := by
    funext i
    fin_cases i
    · ext a c
      change (e.symm B) a c = _
      rw [he00]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (P ^ 3 * B)) a c = _
      have hrelP : P ^ 3 = x • P ^ 2 + y • P + P.det • (1 : Mat) := by
        simpa [P] using hrel
      have h : P ^ 3 * B = x • (P ^ 2 * B) + y • (P * B) + P.det • B := by
        rw [hrelP]
        simp only [add_mul, smul_mul_assoc, one_mul]
      rw [h]
      simp only [map_add, map_smul, he20, he10, he00]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (B * P ^ 3)) a c = _
      have hrelP : P ^ 3 = x • P ^ 2 + y • P + P.det • (1 : Mat) := by
        simpa [P] using hrel
      have h : B * P ^ 3 = x • (B * P ^ 2) + y • (B * P) + P.det • B := by
        rw [hrelP]
        simp only [mul_add, mul_smul_comm, mul_one]
      rw [h]
      simp only [map_add, map_smul, he02, he01, he00]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (P ^ 2 * B * P)) a c = _
      rw [he21]
      simp [Matrix.stdBasis]
    · ext a c
      change (e.symm (P * B * P ^ 2)) a c = _
      rw [he12]
      simp [Matrix.stdBasis]
  have hq : LinearIndependent K q := by
    have hq' := periodic_outer_five_linearIndependent x y P.det hxy
    rw [← hqrepr] at hq'
    have hm := hq'.map' e.toLinearMap (by simp)
    simpa [Function.comp_def] using hm
  let W := Submodule.span K (Set.range q)
  have hdimW : Module.finrank K W = 5 := by
    simpa [W] using finrank_span_eq_card hq
  have hWL : W ≤ L ^ 4 := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact hqmem i
  have hdim := Submodule.finrank_mono hWL
  rw [hdimW] at hdim
  exact hdim

/-- In the invertible-generator case, a proper seventh power requires the
second return to be the unique nonzero return of order one or two. -/
theorem second_rank_one_return_of_pow_seven_ne_top
    (L : Submodule K Mat) (A : Matˣ) (hA : (A : Mat) ∈ L)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hseven : L ^ 7 ≠ ⊤) :
    ∃ u v : Fin 3 → K,
      L = Submodule.span K ({(A : Mat), Matrix.vecMulVec u v} : Set Mat) ∧
      (Matrix.vecMulVec u v).rank = 1 ∧ v ⬝ᵥ u = 0 ∧
      (v ⬝ᵥ ((A : Mat) *ᵥ u)) = 0 ∧ (v ⬝ᵥ ((A : Mat) ^ 2 *ᵥ u)) ≠ 0 := by
  obtain ⟨u, v, hL, hrank, h0, hreturns⟩ :=
    single_rank_one_return_of_pow_seven_ne_top L A hA hfull hseven
  refine ⟨u, v, hL, hrank, h0, hreturns.resolve_left ?_⟩
  rintro ⟨h1, h2⟩
  have hdim := five_le_finrank_cube_of_first_return L A u v hL hfull h0 h1 h2
  exact hseven (pow_eq_top_of_finrank_add_le L A hA hfull (j := 3) (t := 4) (by decide)
    (by rw [finrank_matrix_three]; omega))

private theorem no_common_kernel_of_positive_full (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    ∀ v : Fin 3 → K, (∀ A ∈ L, A *ᵥ v = 0) → v = 0 := by
  intro v hv
  have hpow : ∀ n : ℕ, 0 < n → ∀ X ∈ L ^ n, X *ᵥ v = 0 := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        rw [pow_succ]
        intro Z hZ
        refine Submodule.mul_induction_on hZ ?_ ?_
        · intro X hX Y hY
          rw [← Matrix.mulVec_mulVec, hv Y hY]
          simp
        · intro X Y hX hY
          rw [Matrix.add_mulVec, hX, hY, add_zero]
  obtain ⟨m, hm, htop⟩ := hfull
  have h1 : (1 : Mat) ∈ L ^ m := by rw [htop]; trivial
  simpa using hpow m hm 1 h1

private theorem no_common_cokernel_of_positive_full (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    ∀ v : Fin 3 → K, (∀ A ∈ L, v ᵥ* A = 0) → v = 0 := by
  intro v hv
  have hpow : ∀ n : ℕ, 0 < n → ∀ X ∈ L ^ n, v ᵥ* X = 0 := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
        rw [pow_succ']
        intro Z hZ
        refine Submodule.mul_induction_on hZ ?_ ?_
        · intro X hX Y hY
          rw [← Matrix.vecMul_vecMul, hv X hX]
          simp
        · intro X Y hX hY
          rw [Matrix.vecMul_add, hX, hY, add_zero]
  obtain ⟨m, hm, htop⟩ := hfull
  have h1 : (1 : Mat) ∈ L ^ m := by rw [htop]; trivial
  simpa using hpow m hm 1 h1

/-- A positive full power has neither a common right kernel nor a common left kernel. -/
theorem eventually_full_reduced
    (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) :
    (∀ v : Fin 3 → K, (∀ A ∈ L, A *ᵥ v = 0) → v = 0) ∧
      (∀ v : Fin 3 → K, (∀ A ∈ L, v ᵥ* A = 0) → v = 0) := by
  exact ⟨no_common_kernel_of_positive_full L hfull,
    no_common_cokernel_of_positive_full L hfull⟩

/-- The rank-one branch is impossible as soon as its common-kernel/common-cokernel
    alternative has been established. -/
theorem exclude_rank_one_branch
    (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (hbranch :
      (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, A *ᵥ v = 0) ∨
      (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, v ᵥ* A = 0)) :
    False := by
  rcases hbranch with ⟨v, hv, hkill⟩ | ⟨v, hv, hkill⟩
  · exact hv (no_common_kernel_of_positive_full L hfull v hkill)
  · exact hv (no_common_cokernel_of_positive_full L hfull v hkill)

/-- Linear estimates close either the alternating-square branch or the compression
    certificate branch of the size-three singular classification. -/
theorem pow_seven_eq_top_of_singular_alternatives
    (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤)
    (halt : (L ^ 2 = ⊤) ∨
      (∃ U : Matˣ, (U : Mat) ∈ L ^ 2 ∧
        7 ≤ Module.finrank K ↥(L ^ 3))) :
    L ^ 7 = ⊤ := by
  rcases halt with hsq | ⟨U, hU, hdim⟩
  · exact pow_eq_top_of_le L (by decide) hsq (by decide)
  by_cases h3 : L ^ 3 = ⊤
  · exact pow_eq_top_of_le L (by decide) h3 (by decide)
  by_cases h5 : L ^ 5 = ⊤
  · exact pow_eq_top_of_le L (by decide) h5 (by decide)
  have hg3 := finrank_pow_lt_of_unit_mem L 3 2 U hfull (by decide) hU h3
  have hg5 := finrank_pow_lt_of_unit_mem L 5 2 U hfull (by decide) hU h5
  have hdim7 : 9 ≤ Module.finrank K ↥(L ^ 7) := by
    have h3le : 7 ≤ Module.finrank K ↥(L ^ 3) := hdim
    have h5le : Module.finrank K ↥(L ^ 5) ≥ Module.finrank K ↥(L ^ 3) + 1 := by
      have hg3' : Module.finrank K ↥(L ^ 3) < Module.finrank K ↥(L ^ 5) := by
        simpa using hg3
      omega
    have h7le : Module.finrank K ↥(L ^ 7) ≥ Module.finrank K ↥(L ^ 5) + 1 := by
      have hg5' : Module.finrank K ↥(L ^ 5) < Module.finrank K ↥(L ^ 7) := by
        simpa using hg5
      omega
    omega
  apply Submodule.eq_of_le_of_finrank_le le_top
  simpa [Module.finrank_matrix] using hdim7

private theorem exists_diagonal_rank_normal_form (A : Mat) :
    ∃ P Q : Matˣ, (P : Mat) * A * (Q : Mat) =
      Matrix.diagonal (fun i : Fin 3 => if i.val < A.rank then 1 else 0) := by
  obtain ⟨V, U, e, hV, hU, hA⟩ := Matrix.exists_rank_normal_form A
  have hsize : A.rank + (Fintype.card (Fin 3) - A.rank) = 3 := by
    have hr := A.rank_le_width
    simp only [Fintype.card_fin]
    omega
  let f : Fin A.rank ⊕ Fin (Fintype.card (Fin 3) - A.rank) ≃ Fin 3 :=
    finSumFinEquiv.trans (finCongr hsize)
  let σ : Fin 3 ≃ Fin 3 := f.symm.trans e.symm
  let S : Mat := (1 : Mat).submatrix σ id
  let T : Mat := (1 : Mat).submatrix id σ
  have hST : S * T = 1 := by
    change (1 : Mat).submatrix σ (Equiv.refl _) * T = 1
    rw [Matrix.one_submatrix_mul]
    simp [T, Matrix.submatrix_submatrix]
  obtain ⟨P, hP⟩ := ((isUnit_iff_exists_inv).2 ⟨T, hST⟩).mul hV
  obtain ⟨Q, hQ⟩ := hU.mul ((isUnit_iff_exists_inv').2 ⟨S, hST⟩)
  refine ⟨P, Q, ?_⟩
  rw [hP, hQ, mul_assoc S V A, ← mul_assoc (S * (V * A)) U T,
    mul_assoc S (V * A) U]
  change (1 : Mat).submatrix σ (Equiv.refl _) * (V * A * U) *
    (1 : Mat).submatrix (Equiv.refl _) σ = _
  rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one, hA]
  ext i j
  obtain ⟨i, rfl⟩ := f.surjective i
  obtain ⟨j, rfl⟩ := f.surjective j
  simp only [Matrix.submatrix_apply, Function.comp_apply, id_eq, Equiv.refl_symm,
    Equiv.refl_apply, σ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
    Matrix.diagonal_apply, f.injective.eq_iff]
  rcases i with i | i <;> rcases j with j | j
  · simp [f, Matrix.one_apply, i.isLt]
  · simp [f]
  · simp [f]
  · simp [f, show ¬ A.rank + i.val < A.rank by omega]

/-- A size-three matrix subspace of upper rank one has a nonzero common right or left
kernel vector. The rank bound applies to every member of the subspace. -/
theorem rank_le_one_common_kernel_or_left_kernel (L : Submodule K Mat)
    (hrank : ∀ A ∈ L, A.rank ≤ 1) :
    (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, A *ᵥ v = 0) ∨
    (∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ A ∈ L, v ᵥ* A = 0) := by
  classical
  let v : Fin 3 → K := Pi.single (1 : Fin 3) 1
  have hv : v ≠ 0 := by
    intro h
    simpa [v] using congrFun h 1
  by_cases hex : ∃ A ∈ L, A ≠ 0
  swap
  · push Not at hex
    exact Or.inl ⟨v, hv, fun A hA => by simp [hex A hA]⟩
  obtain ⟨A, hA, hne⟩ := hex
  have hrA : A.rank = 1 := by
    have hpos : A.rank ≠ 0 := by
      intro hz
      rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hz
      exact hne (Matrix.toLin'.injective (by simpa [Matrix.toLin'_apply'] using hz))
    have := hrank A hA
    omega
  obtain ⟨P, Q, hpivot⟩ := exists_diagonal_rank_normal_form A
  let e := (P.mulLeftLinearEquiv K Mat).trans (Q.mulRightLinearEquiv K)
  let M := L.map e.toLinearMap
  have he (B : Mat) : e B = (P : Mat) * B * (Q : Mat) := rfl
  let E : Mat := Matrix.diagonal (fun i : Fin 3 => if i.val < 1 then 1 else 0)
  have hE : E ∈ M := by
    refine Submodule.mem_map.mpr ⟨A, hA, ?_⟩
    change e A = E
    simpa only [he, E, hrA] using hpivot
  have hminor (B : Mat) (hB : B ∈ M) (i j : Fin 3) :
      B 0 0 * B i j - B 0 j * B i 0 = 0 := by
    obtain ⟨C, hC, rfl⟩ := Submodule.mem_map.mp hB
    have hr : (e C).rank ≤ 1 := by
      rw [he, Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
      · exact hrank C hC
      · exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      · exact (Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit
    let N := (e C).submatrix (![0, i] : Fin 2 → Fin 3) (![0, j] : Fin 2 → Fin 3)
    have hn : N.det = 0 := by
      by_contra h
      have hle := (Matrix.rank_submatrix_le (e C) (![0, i] : Fin 2 → Fin 3)
        (![0, j] : Fin 2 → Fin 3)).trans hr
      change N.rank ≤ 1 at hle
      rw [Matrix.rank_of_det_ne_zero h, Fintype.card_fin] at hle
      omega
    rw [Matrix.det_fin_two] at hn
    exact hn
  have hblock (B : Mat) (hB : B ∈ M) (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
      B i j = 0 := by
    have h : (1 + B 0 0) * B i j - B 0 j * B i 0 = 0 := by
      simpa [E, Matrix.diagonal_apply, hi, Ne.symm hj] using
        hminor (E + B) (M.add_mem hE hB) i j
    linear_combination h - hminor B hB i j
  have hcross (B : Mat) (hB : B ∈ M) (i j : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) :
      B 0 j * B i 0 = 0 := by
    simpa [hblock B hB i j hi hj] using hminor B hB i j
  by_cases hrows : ∀ B ∈ M, ∀ i : Fin 3, i ≠ 0 → B i 0 = 0
  · refine Or.inr ⟨v ᵥ* (P : Mat), ?_, ?_⟩
    · intro h
      apply hv
      simpa [Matrix.vecMul_vecMul] using congrArg (fun w => w ᵥ* (↑P⁻¹ : Mat)) h
    · intro B hB
      have hmem : e B ∈ M := Submodule.mem_map.mpr ⟨B, hB, rfl⟩
      have hkill : v ᵥ* e B = 0 := by
        change Pi.single (1 : Fin 3) 1 ᵥ* e B = 0
        rw [Matrix.single_one_vecMul]
        funext j
        by_cases hj : j = 0
        · simpa [hj] using hrows (e B) hmem 1 (by decide)
        · exact hblock (e B) hmem 1 j (by decide) hj
      have hcancel := congrArg (fun w => w ᵥ* (↑Q⁻¹ : Mat)) hkill
      simpa only [he, Matrix.vecMul_vecMul, mul_assoc, Units.mul_inv, mul_one,
        Matrix.zero_vecMul] using hcancel
  · push Not at hrows
    obtain ⟨C, hC, i, hi, hCi⟩ := hrows
    have hcols (B : Mat) (hB : B ∈ M) (j : Fin 3) (hj : j ≠ 0) : B 0 j = 0 := by
      by_contra hBj
      have hCj := (mul_eq_zero.mp (hcross C hC i j hi hj)).resolve_right hCi
      have hBi := (mul_eq_zero.mp (hcross B hB i j hi hj)).resolve_left hBj
      have hsum := hcross (C + B) (M.add_mem hC hB) i j hi hj
      exact (mul_ne_zero hBj hCi) (by simpa [hCj, hBi] using hsum)
    refine Or.inl ⟨(Q : Mat) *ᵥ v, ?_, ?_⟩
    · intro h
      apply hv
      simpa [Matrix.mulVec_mulVec] using congrArg (fun w => (↑Q⁻¹ : Mat) *ᵥ w) h
    · intro B hB
      have hmem : e B ∈ M := Submodule.mem_map.mpr ⟨B, hB, rfl⟩
      have hkill : e B *ᵥ v = 0 := by
        change e B *ᵥ Pi.single (1 : Fin 3) 1 = 0
        rw [Matrix.mulVec_single_one]
        funext i
        by_cases hi : i = 0
        · simpa [hi] using hcols (e B) hmem 1 (by decide)
        · exact hblock (e B) hmem i 1 hi (by decide)
      have hcancel := congrArg (fun w => (↑P⁻¹ : Mat) *ᵥ w) hkill
      simpa only [he, Matrix.mulVec_mulVec, ← mul_assoc, Units.inv_mul, one_mul,
        Matrix.mulVec_zero] using hcancel

/-- An all-singular size-three subspace with a positive full power contains a rank-two matrix. -/
theorem exists_rank_two_of_eventually_full_of_det_eq_zero (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hsing : ∀ A ∈ L, A.det = 0) :
    ∃ A ∈ L, A.rank = 2 := by
  by_contra h
  apply exclude_rank_one_branch L hfull
  apply rank_le_one_common_kernel_or_left_kernel L
  intro A hA
  have htwo : A.rank ≠ 2 := fun hr => h ⟨A, hA, hr⟩
  have hthree : A.rank ≠ 3 := by
    intro hr
    have hsurj : Function.Surjective A.mulVec :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hr)
    have hunit := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hunit
    exact hdet.ne_zero (hsing A hA)
  have hwidth := A.rank_le_width
  omega

/-- Normalizing a rank-two pivot in an all-singular space over an infinite field gives
the bottom-right, quadratic, and cubic constraints for every normalized member. -/
theorem rank_two_pencil_constraints [Infinite K] (L : Submodule K Mat)
    (hsing : ∀ B ∈ L, B.det = 0) {A : Mat} (hA : A ∈ L) (hrank : A.rank = 2) :
    ∃ P Q : Matˣ, (P : Mat) * A * (Q : Mat) =
        Matrix.diagonal (fun i : Fin 3 => if i.val < 2 then 1 else 0) ∧
      ∀ B ∈ L,
        let M := (P : Mat) * B * (Q : Mat)
        let U : Matrix (Fin 2) (Fin 2) K := M.submatrix Fin.castSucc Fin.castSucc
        let u : Fin 2 → K := fun i => M i.castSucc 2
        let v : Fin 2 → K := fun j => M 2 j.castSucc
        M 2 2 = 0 ∧ v ⬝ᵥ u = 0 ∧ v ⬝ᵥ (U *ᵥ u) = 0 := by
  obtain ⟨P, Q, hPQ⟩ := exists_diagonal_rank_normal_form A
  let D : Mat := Matrix.diagonal (fun i : Fin 3 => if i.val < 2 then 1 else 0)
  let e := (P.mulLeftLinearEquiv K Mat).trans (Q.mulRightLinearEquiv K)
  have hD : e A = D := by
    change (P : Mat) * A * (Q : Mat) = D
    simpa only [D, hrank] using hPQ
  refine ⟨P, Q, hD, ?_⟩
  intro B hB M U u v
  have heB : e B = M := rfl
  have hdet (t : K) : (D + t • M).det = 0 := by
    rw [← hD, ← heB, ← map_smul, ← map_add]
    change ((P : Mat) * (A + t • B) * (Q : Mat)).det = 0
    simp [Matrix.det_mul, hsing _ (L.add_mem hA (L.smul_mem t hB))]
  let d := M 2 2
  let traceU := M 0 0 + M 1 1
  let detU := M 0 0 * M 1 1 - M 0 1 * M 1 0
  let vu := M 2 0 * M 0 2 + M 2 1 * M 1 2
  let vUu := M 2 0 * (M 0 0 * M 0 2 + M 0 1 * M 1 2) +
    M 2 1 * (M 1 0 * M 0 2 + M 1 1 * M 1 2)
  let p := Polynomial.C d * Polynomial.X + Polynomial.C (d * traceU - vu) * Polynomial.X ^ 2 +
    Polynomial.C (d * detU - traceU * vu + vUu) * Polynomial.X ^ 3
  have hp : p = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    calc
      p.eval t = (D + t • M).det := by
        rw [Matrix.det_fin_three]
        simp only [p, Polynomial.eval_add, Polynomial.eval_C_mul, Polynomial.eval_X,
          Polynomial.eval_X_pow, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        norm_num [D, Matrix.diagonal_apply, d, traceU, detU, vu, vUu]
        ring
      _ = 0 := hdet t
  have hd : d = 0 := by
    have h : p.coeff 1 = 0 := by rw [hp, Polynomial.coeff_zero]
    norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, if_true, if_false, add_zero] at h
    exact h
  have hvu : vu = 0 := by
    have h : p.coeff 2 = 0 := by rw [hp, Polynomial.coeff_zero]
    norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, if_true, if_false, add_zero, zero_add, hd, zero_mul,
      zero_sub] at h
    exact neg_eq_zero.mp h
  have hvUu : vUu = 0 := by
    have h : p.coeff 3 = 0 := by rw [hp, Polynomial.coeff_zero]
    norm_num only [p, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, if_true, if_false, zero_add, hd, hvu, zero_mul,
      mul_zero, sub_zero] at h
    exact h
  refine ⟨hd, ?_, ?_⟩
  · rw [dotProduct, Fin.sum_univ_two]
    exact hvu
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact hvUu

private abbrev pencilColumn (B : Mat) : Fin 2 → K := ![B 0 2, B 1 2]

private abbrev pencilRow (B : Mat) : Fin 2 → K := ![B 2 0, B 2 1]

private abbrev pencilBlock (B : Mat) : Matrix (Fin 2) (Fin 2) K :=
  B.submatrix Fin.castSucc Fin.castSucc

private theorem pencil_polarization (M : Submodule K Mat)
    (hquad : ∀ B ∈ M, pencilRow B ⬝ᵥ pencilColumn B = 0)
    {B C : Mat} (hB : B ∈ M) (hC : C ∈ M) :
    pencilRow B ⬝ᵥ pencilColumn C + pencilRow C ⬝ᵥ pencilColumn B = 0 := by
  have h := hquad (B + C) (M.add_mem hB hC)
  simp only [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.add_apply] at *
  linear_combination h - hquad B hB - hquad C hC

private theorem fin_two_exists_smul_of_cross_eq_zero {a z : Fin 2 → K} (ha : a ≠ 0)
    (h : a 0 * z 1 - a 1 * z 0 = 0) : ∃ s : K, s • a = z := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ⟨z i / a i, ?_⟩
  ext j
  fin_cases i <;> fin_cases j <;> simp only [Pi.smul_apply, smul_eq_mul] at *
  · exact div_mul_cancel₀ _ hi
  · change z 0 / a 0 * a 1 = z 1
    change a 0 ≠ 0 at hi
    rw [div_mul_eq_mul_div₀, div_eq_iff hi]
    linear_combination -h
  · change z 1 / a 1 * a 0 = z 0
    change a 1 ≠ 0 at hi
    rw [div_mul_eq_mul_div₀, div_eq_iff hi]
    linear_combination h
  · exact div_mul_cancel₀ _ hi

private theorem normalized_pencil_compression [Infinite K] (M : Submodule K Mat)
    (hdiag : ∀ B ∈ M, B 2 2 = 0)
    (hcube : ∀ B ∈ M, pencilRow B ⬝ᵥ (pencilBlock B *ᵥ pencilColumn B) = 0)
    (hu : ∃ B ∈ M, pencilColumn B ≠ 0) (hv : ∃ B ∈ M, pencilRow B ≠ 0)
    {a : Fin 2 → K} (ha : a ≠ 0)
    (hcol : ∀ B ∈ M, a 0 * B 1 2 - a 1 * B 0 2 = 0)
    (hrow : ∀ B ∈ M, B 2 0 * a 0 + B 2 1 * a 1 = 0) :
    ∃ H D : Submodule K (Fin 3 → K),
      Module.finrank K H = 2 ∧ Module.finrank K D = 1 ∧
      ∀ B ∈ M, ∀ z ∈ H, B *ᵥ z ∈ D := by
  let w : Fin 2 → K := ![-a 1, a 0]
  have hw : w ≠ 0 := by
    intro h
    apply ha
    have h0 : a 1 = 0 := by simpa [w] using congrFun h 0
    have h1 : a 0 = 0 := by simpa [w] using congrFun h 1
    funext k
    fin_cases k
    · exact h1
    · exact h0
  have hcol' (B : Mat) (hB : B ∈ M) : ∃ x : K, x • a = pencilColumn B :=
    fin_two_exists_smul_of_cross_eq_zero ha (hcol B hB)
  have hrow' (B : Mat) (hB : B ∈ M) : ∃ y : K, y • w = pencilRow B :=
    fin_two_exists_smul_of_cross_eq_zero hw (by
      simp only [w, pencilRow, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -hrow B hB)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  let f := Matrix.entryLinearMap K K i.castSucc (2 : Fin 3)
  let g := Matrix.entryLinearMap K K (2 : Fin 3) j.castSucc
  have hf (B : Mat) : f B = pencilColumn B i := by fin_cases i <;> rfl
  have hg (B : Mat) : g B = pencilRow B j := by fin_cases j <;> rfl
  let k : Module.Dual K Mat :=
    (w 0 * a 0) • Matrix.entryLinearMap K K 0 0 +
    (w 0 * a 1) • Matrix.entryLinearMap K K 0 1 +
    (w 1 * a 0) • Matrix.entryLinearMap K K 1 0 +
    (w 1 * a 1) • Matrix.entryLinearMap K K 1 1
  have hk (B : Mat) : k B = w 0 * (B 0 0 * a 0 + B 0 1 * a 1) +
      w 1 * (B 1 0 * a 0 + B 1 1 * a 1) := by
    simp [k]
    ring
  have hfne : ∃ B ∈ M, f B ≠ 0 := by
    obtain ⟨B, hB, hne⟩ := hu
    obtain ⟨x, hx⟩ := hcol' B hB
    have hxne : x ≠ 0 := by rintro rfl; exact hne (by simpa using hx.symm)
    refine ⟨B, hB, ?_⟩
    rw [hf, ← hx, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hxne hi
  have hgne : ∃ B ∈ M, g B ≠ 0 := by
    obtain ⟨B, hB, hne⟩ := hv
    obtain ⟨y, hy⟩ := hrow' B hB
    have hyne : y ≠ 0 := by rintro rfl; exact hne (by simpa using hy.symm)
    refine ⟨B, hB, ?_⟩
    rw [hg, ← hy, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hyne hj
  -- The cubic identity rules out a point where all three linear forms are nonzero.
  have hkzero (B : Mat) (hB : B ∈ M) : k B = 0 := by
    by_contra hne
    let forms : Fin 3 → Module.Dual K Mat := ![f, g, k]
    have hforms : ∀ n, ∃ X ∈ M, forms n X ≠ 0 := by
      intro n
      fin_cases n
      · exact hfne
      · exact hgne
      · exact ⟨B, hB, hne⟩
    obtain ⟨X, hX, hall⟩ :=
      Module.Dual.exists_forall_mem_ne_zero_of_forall_exists M forms hforms
    obtain ⟨x, hx⟩ := hcol' X hX
    obtain ⟨y, hy⟩ := hrow' X hX
    have hxne : x ≠ 0 := by
      rintro rfl
      exact hall 0 (by rw [show forms 0 = f from rfl, hf, ← hx]; simp)
    have hyne : y ≠ 0 := by
      rintro rfl
      exact hall 1 (by rw [show forms 1 = g from rfl, hg, ← hy]; simp)
    have hc := hcube X hX
    rw [← hx, ← hy, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul] at hc
    have hval : w ⬝ᵥ (pencilBlock X *ᵥ a) = k X := by
      rw [hk]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rfl
    rw [hval] at hc
    exact (mul_ne_zero hxne (mul_ne_zero hyne (hall 2))) hc
  let a₃ : Fin 3 → K := ![a 0, a 1, 0]
  let e₃ : Fin 3 → K := Pi.single 2 1
  let H := Submodule.span K (Set.range (![a₃, e₃] : Fin 2 → Fin 3 → K))
  let D := Submodule.span K ({a₃} : Set (Fin 3 → K))
  have ha₃ : a₃ ≠ 0 := by
    intro h
    apply hi
    have he := congrFun h i.castSucc
    fin_cases i <;> exact he
  have hind : LinearIndependent K (![a₃, e₃] : Fin 2 → Fin 3 → K) := by
    apply (LinearIndependent.pair_iff' ha₃).2
    intro s h
    have he := congrFun h (2 : Fin 3)
    simp [a₃, e₃] at he
  refine ⟨H, D, by simpa [H] using finrank_span_eq_card hind, finrank_span_singleton ha₃, ?_⟩
  intro B hB
  have hea : B *ᵥ a₃ ∈ D := by
    let z := pencilBlock B *ᵥ a
    have hz : a 0 * z 1 - a 1 * z 0 = 0 := by
      have h := hkzero B hB
      rw [hk] at h
      simp only [z, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      change a 0 * (B 1 0 * a 0 + B 1 1 * a 1) -
        a 1 * (B 0 0 * a 0 + B 0 1 * a 1) = 0
      simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      linear_combination h
    obtain ⟨s, hs⟩ := fin_two_exists_smul_of_cross_eq_zero ha hz
    apply Submodule.mem_span_singleton.mpr
    refine ⟨s, ?_⟩
    ext n
    fin_cases n
    · have he := congrFun hs 0
      simpa [a₃, z, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] using he
    · have he := congrFun hs 1
      simpa [a₃, z, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] using he
    · simpa [a₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using (hrow B hB).symm
  have hee : B *ᵥ e₃ ∈ D := by
    obtain ⟨s, hs⟩ := hcol' B hB
    apply Submodule.mem_span_singleton.mpr
    refine ⟨s, ?_⟩
    rw [show e₃ = Pi.single (2 : Fin 3) 1 from rfl, Matrix.mulVec_single_one]
    ext n
    fin_cases n
    · simpa [a₃, pencilColumn] using congrFun hs 0
    · simpa [a₃, pencilColumn] using congrFun hs 1
    · simpa [a₃] using (hdiag B hB).symm
  have hle : H ≤ D.comap B.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro v ⟨n, rfl⟩
    fin_cases n
    · exact hea
    · exact hee
  exact fun z hz => hle hz

private abbrev rankTwoPivot : Mat :=
  Matrix.diagonal (fun i : Fin 3 => if i.val < 2 then 1 else 0)

private theorem normalized_pencil_alternating [NeZero (2 : K)] (M : Submodule K Mat)
    (hA : rankTwoPivot ∈ M)
    (hdiag : ∀ B ∈ M, B 2 2 = 0)
    (hquad : ∀ B ∈ M, pencilRow B ⬝ᵥ pencilColumn B = 0)
    (hcube : ∀ B ∈ M, pencilRow B ⬝ᵥ (pencilBlock B *ᵥ pencilColumn B) = 0)
    (hv : ∃ B ∈ M, pencilRow B ≠ 0)
    (hsurj : ∀ x y : K, ∃ B ∈ M, B 0 2 = x ∧ B 1 2 = y) :
    ∃ P Q : Matˣ, ∀ C : Mat, C.transpose = -C ↔
      ∃ B ∈ M, (P : Mat) * B * (Q : Mat) = C := by
  obtain ⟨X, hX, hx₀, hx₁⟩ := hsurj 1 0
  obtain ⟨Y, hY, hy₀, hy₁⟩ := hsurj 0 1
  have hpol (B C : Mat) (hB : B ∈ M) (hC : C ∈ M) :
      B 2 0 * C 0 2 + B 2 1 * C 1 2 + (C 2 0 * B 0 2 + C 2 1 * B 1 2) = 0 := by
    simpa only [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] using pencil_polarization M hquad hB hC
  have hX20 : X 2 0 = 0 := by
    simpa [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two, hx₀, hx₁] using hquad X hX
  have hY21 : Y 2 1 = 0 := by
    simpa [pencilColumn, pencilRow, dotProduct, Fin.sum_univ_two, hy₀, hy₁] using hquad Y hY
  let c := X 2 1
  have hY20 : Y 2 0 = -c := by
    have h := hpol X Y hX hY
    simp [hx₀, hx₁, hy₀, hy₁] at h
    dsimp [c]
    linear_combination h
  have hrow (B : Mat) (hB : B ∈ M) :
      B 2 0 = -c * B 1 2 ∧ B 2 1 = c * B 0 2 := by
    have h0 := hpol B X hB hX
    have h1 := hpol B Y hB hY
    simp [hx₀, hx₁, hX20] at h0
    simp [hy₀, hy₁, hY20, hY21] at h1
    constructor
    · dsimp [c]
      linear_combination h0
    · linear_combination h1
  have hc : c ≠ 0 := by
    obtain ⟨B, hB, hn⟩ := hv
    intro h
    obtain ⟨h0, h1⟩ := hrow B hB
    exact hn (by ext i; fin_cases i <;> simp [pencilRow, h0, h1, h])
  have hpoly (B : Mat) (hB : B ∈ M) :
      B 1 0 * B 0 2 ^ 2 + (B 1 1 - B 0 0) * B 0 2 * B 1 2 -
        B 0 1 * B 1 2 ^ 2 = 0 := by
    obtain ⟨h0, h1⟩ := hrow B hB
    have h := hcube B hB
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
    change B 2 0 * (B 0 0 * B 0 2 + B 0 1 * B 1 2) +
      B 2 1 * (B 1 0 * B 0 2 + B 1 1 * B 1 2) = 0 at h
    rw [h0, h1] at h
    apply (mul_eq_zero.mp (show c * _ = 0 from ?_)).resolve_left hc
    linear_combination h
  -- Adding a zero-column member to the three test columns forces its block to be scalar.
  have hker (B : Mat) (hB : B ∈ M) (h0 : B 0 2 = 0) (h1 : B 1 2 = 0) :
      B 1 0 = 0 ∧ B 0 1 = 0 ∧ B 0 0 = B 1 1 := by
    have h10 : B 1 0 = 0 := by
      have h := hpoly (X + B) (M.add_mem hX hB)
      simp [Matrix.add_apply, hx₀, hx₁, h0, h1] at h
      have hx := hpoly X hX
      simp [hx₀, hx₁] at hx
      linear_combination h - hx
    have h01 : B 0 1 = 0 := by
      have h := hpoly (Y + B) (M.add_mem hY hB)
      simp [Matrix.add_apply, hy₀, hy₁, h0, h1] at h
      have hy := hpoly Y hY
      simp [hy₀, hy₁] at hy
      linear_combination -h - hy
    refine ⟨h10, h01, ?_⟩
    have h := hpoly (X + Y + B) (M.add_mem (M.add_mem hX hY) hB)
    have hxy := hpoly (X + Y) (M.add_mem hX hY)
    simp [Matrix.add_apply, hx₀, hx₁, hy₀, hy₁, h0, h1, h10, h01] at h hxy
    linear_combination hxy - h
  let b₀ := X 0 0 - X 1 1
  let b₁ := X 0 1
  have hX10 : X 1 0 = 0 := by simpa [hx₀, hx₁] using hpoly X hX
  have hY01 : Y 0 1 = 0 := by simpa [hy₀, hy₁] using hpoly Y hY
  have hYparams : Y 1 0 = b₀ ∧ Y 1 1 - Y 0 0 = b₁ := by
    have hp := hpoly (X + Y) (M.add_mem hX hY)
    have hm := hpoly (X - Y) (M.sub_mem hX hY)
    simp [Matrix.add_apply, Matrix.sub_apply, hx₀, hx₁, hy₀, hy₁, hX10, hY01] at hp hm
    constructor
    · apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show (2 : K) * _ = 0 from ?_)).resolve_left two_ne_zero
      dsimp [b₀]
      linear_combination hp - hm
    · apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show (2 : K) * _ = 0 from ?_)).resolve_left two_ne_zero
      dsimp [b₁]
      linear_combination hp + hm
  have hblock (B : Mat) (hB : B ∈ M) :
      B 1 0 = B 1 2 * b₀ ∧ B 0 1 = B 0 2 * b₁ ∧
      B 0 0 - B 1 1 = B 0 2 * b₀ - B 1 2 * b₁ := by
    let C := B - B 0 2 • X - B 1 2 • Y
    have hC : C ∈ M := M.sub_mem (M.sub_mem hB (M.smul_mem _ hX)) (M.smul_mem _ hY)
    have hc0 : C 0 2 = 0 := by simp [C, Matrix.sub_apply, Matrix.smul_apply, hx₀, hy₀]
    have hc1 : C 1 2 = 0 := by simp [C, Matrix.sub_apply, Matrix.smul_apply, hx₁, hy₁]
    obtain ⟨h10, h01, hd⟩ := hker C hC hc0 hc1
    simp only [C, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h10 h01 hd
    refine ⟨?_, ?_, ?_⟩
    · simpa [hX10, hYparams.1, sub_eq_zero] using h10
    · simpa [hY01, b₁, sub_eq_zero] using h01
    · dsimp [b₀, b₁]
      linear_combination hd - B 1 2 * hYparams.2
  let S : Mat := !![0, 1, 0; -1, 0, 0; 0, 0, c⁻¹]
  let T : Mat := !![1, 0, 0; 0, 1, 0; -b₀, -b₁, 1]
  have hS : IsUnit S := by
    apply (Matrix.isUnit_iff_isUnit_det S).mpr
    simpa [S, Matrix.det_fin_three] using (inv_ne_zero hc).isUnit
  have hT : IsUnit T := by
    apply (Matrix.isUnit_iff_isUnit_det T).mpr
    simp [T, Matrix.det_fin_three]
  obtain ⟨P, hP⟩ := hS
  obtain ⟨Q, hQ⟩ := hT
  let skew (s x y : K) : Mat := !![0, s, y; -s, 0, -x; -y, x, 0]
  have hskew (s x y : K) : (skew s x y).transpose = -skew s x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [skew, Matrix.transpose_apply]
  let scalar (B : Mat) := B 1 1 - B 1 2 * b₁
  have htransform (B : Mat) (hB : B ∈ M) :
      S * B * T = skew (scalar B) (B 0 2) (B 1 2) := by
    obtain ⟨h10, h01, hdiff⟩ := hblock B hB
    obtain ⟨h20, h21⟩ := hrow B hB
    have h00 : B 0 0 = B 1 1 + (B 0 2 * b₀ - B 1 2 * b₁) := by
      linear_combination hdiff
    have hd := hdiag B hB
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [S, T, scalar, skew, h00, h10, h01, h20, h21, hd, ← mul_assoc, hc] <;> ring
  refine ⟨P, Q, fun C => ⟨?_, ?_⟩⟩
  · intro hC
    have hc (i j : Fin 3) : C j i = -C i j := congr_fun (congr_fun hC i) j
    have hz (i : Fin 3) : C i i = 0 := by
      apply (mul_eq_zero.mp (show (2 : K) * C i i = 0 from ?_)).resolve_left two_ne_zero
      linear_combination hc i i
    have hshape : C = skew (C 0 1) (-C 1 2) (C 0 2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [skew, hz, hc 0 1, hc 0 2, hc 1 2]
    let x := -C 1 2
    let y := C 0 2
    let t := C 0 1 - x * scalar X - y * scalar Y
    let B := x • X + y • Y + t • (rankTwoPivot : Mat)
    have hB : B ∈ M := M.add_mem (M.add_mem (M.smul_mem x hX) (M.smul_mem y hY))
      (M.smul_mem t hA)
    refine ⟨B, hB, ?_⟩
    have hb₀ : B 0 2 = x := by
      simp [B, Matrix.add_apply, Matrix.smul_apply, rankTwoPivot, hx₀, hy₀]
    have hb₁ : B 1 2 = y := by
      simp [B, Matrix.add_apply, Matrix.smul_apply, rankTwoPivot, hx₁, hy₁]
    have hs : scalar B = C 0 1 := by
      simp [scalar, B, t, Matrix.add_apply, Matrix.smul_apply,
        rankTwoPivot, hx₁, hy₁]
      ring
    rw [hP, hQ, htransform B hB, hb₀, hb₁, hs]
    exact hshape.symm
  · rintro ⟨B, hB, rfl⟩
    rw [hP, hQ, htransform B hB]
    exact hskew _ _ _

private def unitMulVecEquiv (P : Matˣ) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
  LinearEquiv.ofLinearMap (f := (P : Mat).mulVecLin) (g := (↑P⁻¹ : Mat).mulVecLin)
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])

/-- An all-singular subspace of size-three matrices with a positive full power either
maps a fixed plane into a fixed line, or is equivalent under independent invertible
left and right multiplication to the whole skew-symmetric matrix space. -/
theorem singular_space_classification [Infinite K] [NeZero (2 : K)] (L : Submodule K Mat)
    (hfull : ∃ m : ℕ, 0 < m ∧ L ^ m = ⊤) (hsing : ∀ B ∈ L, B.det = 0) :
    (∃ H D : Submodule K (Fin 3 → K),
      Module.finrank K H = 2 ∧ Module.finrank K D = 1 ∧
      ∀ B ∈ L, ∀ z ∈ H, B *ᵥ z ∈ D) ∨
    (∃ P Q : Matˣ, ∀ C : Mat, C.transpose = -C ↔
      ∃ B ∈ L, (P : Mat) * B * (Q : Mat) = C) := by
  classical
  obtain ⟨A, hA, hrank⟩ := exists_rank_two_of_eventually_full_of_det_eq_zero L hfull hsing
  obtain ⟨P, Q, hPQ, hconstraints⟩ := rank_two_pencil_constraints L hsing hA hrank
  let e := (P.mulLeftLinearEquiv K Mat).trans (Q.mulRightLinearEquiv K)
  let M := L.map e.toLinearMap
  have he (B : Mat) : e B = (P : Mat) * B * (Q : Mat) := rfl
  have hM (B : Mat) (hB : B ∈ L) : e B ∈ M := Submodule.mem_map.mpr ⟨B, hB, rfl⟩
  have hPivot : (rankTwoPivot : Mat) ∈ M := by
    have h : e A = rankTwoPivot := (he A).trans hPQ
    rw [← h]
    exact hM A hA
  have hnorm (B : Mat) (hB : B ∈ M) :
      B 2 2 = 0 ∧ pencilRow B ⬝ᵥ pencilColumn B = 0 ∧
      pencilRow B ⬝ᵥ (pencilBlock B *ᵥ pencilColumn B) = 0 := by
    obtain ⟨C, hC, rfl⟩ := Submodule.mem_map.mp hB
    have hcol (B : Mat) : (fun i : Fin 2 => B i.castSucc 2) = pencilColumn B := by
      funext i
      fin_cases i <;> rfl
    have hrow (B : Mat) : (fun i : Fin 2 => B 2 i.castSucc) = pencilRow B := by
      funext i
      fin_cases i <;> rfl
    change (e C) 2 2 = 0 ∧ pencilRow (e C) ⬝ᵥ pencilColumn (e C) = 0 ∧
      pencilRow (e C) ⬝ᵥ (pencilBlock (e C) *ᵥ pencilColumn (e C)) = 0
    simpa only [he, hcol, hrow] using hconstraints C hC
  have hd (B : Mat) (hB : B ∈ M) := (hnorm B hB).1
  have hquad (B : Mat) (hB : B ∈ M) := (hnorm B hB).2.1
  have hcube (B : Mat) (hB : B ∈ M) := (hnorm B hB).2.2
  let z : Fin 3 → K := Pi.single 2 1
  have hz : z ≠ 0 := by intro h; simpa [z] using congrFun h 2
  have hu : ∃ B ∈ M, pencilColumn B ≠ 0 := by
    by_contra! h
    have hk : ∀ B ∈ L, B *ᵥ ((Q : Mat) *ᵥ z) = 0 := by
      intro B hB
      have hc := h (e B) (hM B hB)
      have h0 : e B 0 2 = 0 := congrFun hc 0
      have h1 : e B 1 2 = 0 := congrFun hc 1
      have hkill : e B *ᵥ z = 0 := by
        rw [show z = Pi.single (2 : Fin 3) 1 from rfl, Matrix.mulVec_single_one]
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact hd (e B) (hM B hB)
      have hcancel := congrArg (fun w => (↑P⁻¹ : Mat) *ᵥ w) hkill
      simpa only [he, Matrix.mulVec_mulVec, ← mul_assoc, Units.inv_mul, one_mul,
        Matrix.mulVec_zero] using hcancel
    have hcancel := congrArg (fun w => (↑Q⁻¹ : Mat) *ᵥ w)
      (no_common_kernel_of_positive_full L hfull _ hk)
    exact hz (by simpa [Matrix.mulVec_mulVec] using hcancel)
  have hv : ∃ B ∈ M, pencilRow B ≠ 0 := by
    by_contra! h
    have hk : ∀ B ∈ L, (z ᵥ* (P : Mat)) ᵥ* B = 0 := by
      intro B hB
      have hc := h (e B) (hM B hB)
      have h0 : e B 2 0 = 0 := congrFun hc 0
      have h1 : e B 2 1 = 0 := congrFun hc 1
      have hkill : z ᵥ* e B = 0 := by
        rw [show z = Pi.single (2 : Fin 3) 1 from rfl, Matrix.single_one_vecMul]
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact hd (e B) (hM B hB)
      have hcancel := congrArg (fun w => w ᵥ* (↑Q⁻¹ : Mat)) hkill
      simpa only [he, Matrix.vecMul_vecMul, mul_assoc, Units.mul_inv, mul_one,
        Matrix.zero_vecMul] using hcancel
    have hcancel := congrArg (fun w => w ᵥ* (↑P⁻¹ : Mat))
      (no_common_cokernel_of_positive_full L hfull _ hk)
    exact hz (by simpa [Matrix.vecMul_vecMul] using hcancel)
  by_cases hsurj : ∀ x y : K, ∃ B ∈ M, B 0 2 = x ∧ B 1 2 = y
  · obtain ⟨S, T, hST⟩ := normalized_pencil_alternating M hPivot hd hquad hcube hv hsurj
    refine Or.inr ⟨S * P, Q * T, fun C => ?_⟩
    rw [hST C]
    constructor
    · rintro ⟨B, hB, h⟩
      obtain ⟨B₀, hB₀, rfl⟩ := Submodule.mem_map.mp hB
      change (S : Mat) * e B₀ * (T : Mat) = C at h
      exact ⟨B₀, hB₀, by simpa only [he, Units.val_mul, mul_assoc] using h⟩
    · rintro ⟨B, hB, h⟩
      exact ⟨e B, hM B hB, by simpa only [he, Units.val_mul, mul_assoc] using h⟩
  · obtain ⟨X, hX, hx⟩ := hu
    let a := pencilColumn X
    have hc (B : Mat) (hB : B ∈ M) : a 0 * B 1 2 - a 1 * B 0 2 = 0 := by
      by_contra! h
      apply hsurj
      intro x y
      let Δ := a 0 * B 1 2 - a 1 * B 0 2
      let s := (x * B 1 2 - y * B 0 2) / Δ
      let t := (a 0 * y - a 1 * x) / Δ
      refine ⟨s • X + t • B, M.add_mem (M.smul_mem s hX) (M.smul_mem t hB), ?_, ?_⟩
      · change s * a 0 + t * B 0 2 = x
        dsimp [s, t]
        field_simp [show Δ ≠ 0 from h]
        dsimp [Δ]
        ring
      · change s * a 1 + t * B 1 2 = y
        dsimp [s, t]
        field_simp [show Δ ≠ 0 from h]
        dsimp [Δ]
        ring
    have hvu (B : Mat) (hB : B ∈ M) : B 2 0 * a 0 + B 2 1 * a 1 = 0 := by
      obtain ⟨s, hs⟩ := fin_two_exists_smul_of_cross_eq_zero hx (z := pencilColumn B) (hc B hB)
      have h := pencil_polarization M hquad hB hX
      rw [← hs, dotProduct_smul, show pencilRow X ⬝ᵥ a = 0 from hquad X hX,
        smul_zero, add_zero] at h
      simpa [a, pencilRow, dotProduct, Fin.sum_univ_two] using h
    obtain ⟨H, D, hH, hD, hmap⟩ :=
      normalized_pencil_compression M hd hcube ⟨X, hX, hx⟩ hv hx hc hvu
    let q := unitMulVecEquiv Q
    let p := unitMulVecEquiv P⁻¹
    refine Or.inl ⟨H.map q.toLinearMap, D.map p.toLinearMap,
      (q.finrank_map_eq H).trans hH, (p.finrank_map_eq D).trans hD, ?_⟩
    intro B hB w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    refine Submodule.mem_map.mpr ⟨e B *ᵥ v, hmap (e B) (hM B hB) v hv, ?_⟩
    change (↑P⁻¹ : Mat) *ᵥ (e B *ᵥ v) = B *ᵥ ((Q : Mat) *ᵥ v)
    rw [he, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul,
      ← Matrix.mulVec_mulVec]

end SizeThree
end OmegaMath.HomogeneousWordPowers
