/- GID: D5/S3/Matrix/HomogeneousWordPowersRankOne
   generality: G
   mirror-B: none(waiver:covered-by-shitov-size-three-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reduction of the size-three invertible case to rank-one generators and return pairings. -/

import D5.S3.Matrix.HomogeneousWordPowers

/-! Omega original.

Reduction of the size-three invertible case to rank-one generators and return pairings. -/

set_option autoImplicit false

open scoped Pointwise
open Matrix

namespace OmegaMath.HomogeneousWordPowers

section SizeThree

variable {K : Type*} [Field K]

local notation "Mat" => Matrix (Fin 3) (Fin 3) K

theorem finrank_matrix_three : Module.finrank K Mat = 9 := by
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

theorem third_power_eq (A : Mat) :
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

theorem span_column_orbit
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

theorem span_row_orbit
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

theorem return_product (A : Mat) (u v : Fin 3 → K) (j : ℕ) :
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

end SizeThree
end OmegaMath.HomogeneousWordPowers
