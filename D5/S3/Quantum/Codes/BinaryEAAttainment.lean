/- GID: D5/S3/Quantum/Codes/BinaryEAAttainment
   generality: I
   mirror-B: D5/B/S3/Quantum/Codes/BinaryEAAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate kernel counts constrain binary entanglement-assisted Singleton attainment. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.FieldTheory.Finiteness
import OmegaBuild.Commands

/-! Coordinate-kernel and support reductions for binary stabilizer codes. [Helper escape audits](https://github.com/the-omega-institute/trureturing/issues/34915). -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Codes.BinaryEAAttainment

open D5.S3.Quantum.Information.BinaryLagrangianGraphForm (sp)
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (spForm sp_alt sp_nondegenerate)

local notation "F" => ZMod 2
local notation "E" n:arg => ((Fin n → ZMod 2) × (Fin n → ZMod 2))
local notation "dim" => Module.finrank (ZMod 2)

variable {n : ℕ}

/-- Coordinate pair at a single site. -/
def site (i : Fin n) : E n →ₗ[F] F × F where
  toFun v := (v.1 i, v.2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Retain the coordinate pairs indexed by a set of sites. -/
def restrictSites (I : Finset (Fin n)) : E n →ₗ[F] (I → F × F) where
  toFun v i := site i v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The radical of the restriction of the ambient form to a subspace. -/
def radical (U : Submodule F (E n)) : Submodule F (E n) :=
  U ⊓ (spForm n).orthogonal U

/-- The number of sites at which both binary coordinates vanish. -/
def zeroCount (v : E n) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => site i v = 0).card

/-- Attainment of minimum symplectic weight exactly `n - 3` outside the radical. -/
def Attainment : Prop :=
  ∃ (n : ℕ), 6 ≤ n ∧ ∃ U : Submodule F (E n),
    dim U = 8 ∧ dim (radical U) = 4 ∧
    (∀ v ∈ U, v ∉ radical U → n - 3 ≤ n - zeroCount v) ∧
    (∃ v ∈ U, v ∉ radical U ∧ n - zeroCount v = n - 3)

/-- Every nonradical word has at most three zero coordinate pairs. -/
def ZeroBound (U : Submodule F (E n)) : Prop :=
  ∀ v ∈ U, v ∉ radical U → zeroCount v ≤ 3

private theorem zeroCount_le (v : E n) : zeroCount v ≤ n := by
  simpa [zeroCount] using Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => site i v = 0)

/-- The lower bound on minimum weight implies the zero-count hypothesis. -/
theorem zeroBound_of_weight_bound (U : Submodule F (E n)) (hn : 6 ≤ n)
    (h : ∀ v ∈ U, v ∉ radical U → n - 3 ≤ n - zeroCount v) : ZeroBound U := by
  intro v hv hrad
  have := h v hv hrad
  have := zeroCount_le v
  omega

/-- The subspace of words in `W` vanishing on every site of `I`. -/
def siteKernel (W : Submodule F (E n)) (I : Finset (Fin n)) : Submodule F (E n) :=
  W ⊓ LinearMap.ker (restrictSites I)

/-- Cardinality of the common coordinate kernel. -/
noncomputable def kernelCount (W : Submodule F (E n)) (I : Finset (Fin n)) : ℕ :=
  2 ^ dim (siteKernel W I)

private theorem mem_siteKernel {W : Submodule F (E n)} {I : Finset (Fin n)} {v : E n} :
    v ∈ siteKernel W I ↔ v ∈ W ∧ ∀ i ∈ I, site i v = 0 := by
  simp only [siteKernel, Submodule.mem_inf, LinearMap.mem_ker]
  refine and_congr_right fun _ => ?_
  exact ⟨fun h i hi => congrFun h ⟨i, hi⟩, fun h => funext fun i => h i i.property⟩

private theorem siteKernel_mono {W W' : Submodule F (E n)} {I J : Finset (Fin n)}
    (hW : W ≤ W') (hI : I ⊆ J) : siteKernel W J ≤ siteKernel W' I := by
  intro v hv
  obtain ⟨hv, hz⟩ := mem_siteKernel.mp hv
  exact mem_siteKernel.mpr ⟨hW hv, fun i hi => hz i (hI hi)⟩

private theorem kernelCount_mono {W W' : Submodule F (E n)} {I J : Finset (Fin n)}
    (hW : W ≤ W') (hI : I ⊆ J) : kernelCount W J ≤ kernelCount W' I :=
  Nat.pow_le_pow_right (by decide) (Submodule.finrank_mono (siteKernel_mono hW hI))

private theorem dim_ker_domRestrict (W : Submodule F (E n)) (I : Finset (Fin n)) :
    dim (LinearMap.ker ((restrictSites I).domRestrict W)) = dim (siteKernel W I) := by
  rw [← Submodule.finrank_map_subtype_eq W (LinearMap.ker ((restrictSites I).domRestrict W))]
  apply congrArg (fun P : Submodule F (E n) => dim P)
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hv, hz⟩
    exact ⟨⟨v, hv⟩, hz, rfl⟩

theorem dim_kernel_add_rank (W : Submodule F (E n)) (I : Finset (Fin n)) :
    dim (siteKernel W I) + dim (LinearMap.range ((restrictSites I).domRestrict W)) = dim W := by
  rw [← dim_ker_domRestrict, add_comm, LinearMap.finrank_range_add_finrank_ker]

private theorem dim_siteKernel_lower (W : Submodule F (E n)) (I : Finset (Fin n)) :
    dim W ≤ dim (siteKernel W I) + 2 * I.card := by
  have h := dim_kernel_add_rank W I
  have hr : dim (LinearMap.range ((restrictSites I).domRestrict W)) ≤ dim (I → F × F) :=
    Submodule.finrank_le _
  have hsize : dim (I → F × F) = 2 * I.card := by
    simp [Module.finrank_pi_fintype, Module.finrank_prod, Nat.mul_comm]
  rw [hsize] at hr
  omega

private theorem dim_siteKernel_insert (W : Submodule F (E n)) (I : Finset (Fin n)) (j : Fin n) :
    dim (siteKernel W I) ≤ dim (siteKernel W (insert j I)) + 2 := by
  have h := dim_siteKernel_lower (siteKernel W I) {j}
  have he : siteKernel (siteKernel W I) {j} = siteKernel W (insert j I) := by
    ext v
    simp only [mem_siteKernel, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
    tauto
  rw [congrArg (fun P : Submodule F (E n) => dim P) he] at h
  simpa using h

private theorem kernelCount_insert (W : Submodule F (E n)) (I : Finset (Fin n)) (j : Fin n) :
    kernelCount W I ≤ 4 * kernelCount W (insert j I) := by
  have h := Nat.pow_le_pow_right (n := 2) (by decide) (dim_siteKernel_insert W I j)
  simpa [kernelCount, pow_add, Nat.mul_comm] using h

open scoped BigOperators

private noncomputable def words (W : Submodule F (E n)) (I : Finset (Fin n)) :
    Finset (E n) := by
  classical
  exact Finset.univ.filter fun v => v ∈ siteKernel W I

private theorem mem_words {W : Submodule F (E n)} {I : Finset (Fin n)} {v : E n} :
    v ∈ words W I ↔ v ∈ siteKernel W I := by
  classical
  simp [words]

private theorem card_words (W : Submodule F (E n)) (I : Finset (Fin n)) :
    (words W I).card = kernelCount W I := by
  classical
  let e : (words W I : Type) ≃ siteKernel W I :=
    Equiv.subtypeEquivRight fun _ => mem_words
  rw [← Fintype.card_coe, Fintype.card_congr e, Module.card_eq_pow_finrank (K := F), ZMod.card]
  rfl

private noncomputable def nonradicalWords (U : Submodule F (E n)) (I : Finset (Fin n)) :
    Finset (E n) := by
  classical
  exact (words U I) \ (words (radical U) I)

private theorem mem_nonradicalWords {U : Submodule F (E n)} {I : Finset (Fin n)} {v : E n} :
    v ∈ nonradicalWords U I ↔ v ∈ U ∧ v ∉ radical U ∧ ∀ i ∈ I, site i v = 0 := by
  classical
  simp only [nonradicalWords, Finset.mem_sdiff, mem_words, mem_siteKernel]
  tauto

private theorem card_nonradicalWords (U : Submodule F (E n)) (I : Finset (Fin n)) :
    (nonradicalWords U I).card = kernelCount U I - kernelCount (radical U) I := by
  classical
  rw [nonradicalWords, Finset.card_sdiff_of_subset, card_words, card_words]
  intro v hv
  exact mem_words.mpr (siteKernel_mono ((show radical U ≤ U from inf_le_left)) (Finset.Subset.refl I) (mem_words.mp hv))

private theorem count_extensions (U : Submodule F (E n)) (hU : ZeroBound U)
    (I : Finset (Fin n)) :
    ∑ j ∈ Iᶜ, (nonradicalWords U (insert j I)).card ≤
      (3 - I.card) * (nonradicalWords U I).card := by
  classical
  let V := nonradicalWords U I
  have hf (j : Fin n) :
      nonradicalWords U (insert j I) = V.filter fun v => site j v = 0 := by
    ext v
    simp only [V, mem_nonradicalWords, Finset.mem_filter, Finset.forall_mem_insert]
    tauto
  simp_rw [hf, Finset.card_filter]
  rw [Finset.sum_comm, mul_comm,
    ← Finset.sum_const_nat (s := V) (f := fun _ => 3 - I.card) (by simp)]
  apply Finset.sum_le_sum
  intro v hv
  obtain ⟨hvU, hvH, hz⟩ := mem_nonradicalWords.mp hv
  let Z := (Finset.univ : Finset (Fin n)).filter fun j => site j v = 0
  have hIZ : I ⊆ Z := fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz j hj⟩
  have he : (Iᶜ.filter fun j => site j v = 0) = Z \ I := by
    ext j
    simp [Z, and_comm]
  rw [← Finset.card_filter, he, Finset.card_sdiff_of_subset hIZ]
  exact Nat.sub_le_sub_right (hU v hvU hvH) _

/-- Integer coordinate-kernel inequality from counting nonradical words and new zero sites. -/
theorem kernelCount_inequality (U : Submodule F (E n)) (hU : ZeroBound U)
    (I : Finset (Fin n)) :
    (n - I.card) * kernelCount U I + 4 * (3 - I.card) * kernelCount (radical U) I ≤
      4 * (3 - I.card) * kernelCount U I +
        4 * ∑ j ∈ Iᶜ, kernelCount (radical U) (insert j I) := by
  classical
  have h := count_extensions U hU I
  have he (j : Fin n) :
      kernelCount U (insert j I) =
        (nonradicalWords U (insert j I)).card + kernelCount (radical U) (insert j I) := by
    rw [card_nonradicalWords, Nat.sub_add_cancel (kernelCount_mono ((show radical U ≤ U from inf_le_left)) (by rfl))]
  have hsum : (n - I.card) * kernelCount U I ≤
      ∑ j ∈ Iᶜ, 4 * kernelCount U (insert j I) := by
    simpa [Finset.card_compl] using
      (Finset.sum_le_sum fun j (_ : j ∈ Iᶜ) => kernelCount_insert U I j)
  simp_rw [he, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hle := Nat.mul_le_mul_left 4 h
  rw [card_nonradicalWords] at hle
  have hsub := Nat.sub_add_cancel
    (kernelCount_mono ((show radical U ≤ U from inf_le_left)) (show I ⊆ I by rfl))
  have hmul := congrArg (fun t : ℕ => 4 * (3 - I.card) * t) hsub
  simp only [Nat.mul_add, Nat.mul_assoc] at hmul ⊢
  omega

private theorem kernelCount_lower (W : Submodule F (E n)) (I : Finset (Fin n))
    (d : ℕ) (hd : d + 2 * I.card ≤ dim W) : 2 ^ d ≤ kernelCount W I := by
  have h := dim_siteKernel_lower W I
  exact Nat.pow_le_pow_right (by decide) (by omega)

private theorem siteKernel_eq_of_count_le {W : Submodule F (E n)} {I J : Finset (Fin n)}
    (hIJ : I ⊆ J) (hc : kernelCount W I ≤ kernelCount W J) :
    siteKernel W J = siteKernel W I := by
  apply Submodule.eq_of_le_of_finrank_le (siteKernel_mono le_rfl hIJ)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

private theorem eq_zero_of_every_site {v : E n} (h : ∀ i, site i v = 0) : v = 0 := by
  apply Prod.ext
  · exact funext fun i => congrArg Prod.fst (h i)
  · exact funext fun i => congrArg Prod.snd (h i)

private theorem kernel_eq_bot_of_extensions (W : Submodule F (E n)) (I : Finset (Fin n))
    (h : ∀ j ∈ Iᶜ, kernelCount W I ≤ kernelCount W (insert j I)) :
    siteKernel W I = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  apply eq_zero_of_every_site
  intro j
  by_cases hj : j ∈ I
  · exact (mem_siteKernel.mp hv).2 j hj
  · have he := siteKernel_eq_of_count_le (Finset.subset_insert j I)
      (h j (Finset.mem_compl.mpr hj))
    have hv' : v ∈ siteKernel W (insert j I) := he ▸ hv
    exact (mem_siteKernel.mp hv').2 j (Finset.mem_insert_self j I)

private theorem pair_sum_upper (W : Submodule F (E n)) (I : Finset (Fin n)) :
    ∑ j ∈ Iᶜ, kernelCount W (insert j I) ≤ (n - I.card) * kernelCount W I := by
  simpa [Finset.card_compl, Nat.nsmul_eq_mul] using
    (Finset.sum_le_sum fun j (_ : j ∈ Iᶜ) =>
      kernelCount_mono (W := W) le_rfl (Finset.subset_insert j I))

private theorem pair_arithmetic (U : Submodule F (E n)) (hU : ZeroBound U)
    (I : Finset (Fin n)) (hI : I.card = 2) (hn : 6 ≤ n) :
    (n - 6) * kernelCount U I + 4 * kernelCount (radical U) I ≤
      4 * ∑ j ∈ Iᶜ, kernelCount (radical U) (insert j I) := by
  have h := kernelCount_inequality U hU I
  rw [hI] at h
  change (n - 2) * kernelCount U I + 4 * kernelCount (radical U) I ≤
    4 * kernelCount U I + 4 * ∑ j ∈ Iᶜ, kernelCount (radical U) (insert j I) at h
  rw [show n - 2 = (n - 6) + 4 by omega, add_mul] at h
  omega

/-- At length at least nine every pair retains a radical kernel of dimension at least two. -/
theorem pair_kernel_dim_ge_two (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hn : 9 ≤ n) (I : Finset (Fin n)) (hI : I.card = 2) :
    2 ≤ dim (siteKernel (radical U) I) := by
  classical
  let H := radical U
  let A := kernelCount U I
  let B := kernelCount H I
  let T := ∑ j ∈ Iᶜ, kernelCount H (insert j I)
  have hA : 16 ≤ A := kernelCount_lower U I 4 (by rw [hI, hdU])
  have hmain : (n - 6) * A + 4 * B ≤ 4 * T := pair_arithmetic U hU I hI (by omega)
  have hsum : T ≤ (n - 2) * B := by simpa [T, B, hI] using pair_sum_upper H I
  by_contra! hdim
  have hB : B ≤ 2 := by
    change 2 ^ dim (siteKernel H I) ≤ 2 ^ 1
    change dim (siteKernel H I) < 2 at hdim
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hn6 : n - 6 = (n - 9) + 3 := by omega
  have hn2 : n - 2 = (n - 9) + 7 := by omega
  rw [hn6, add_mul] at hmain
  rw [hn2, add_mul] at hsum
  have hlo := Nat.mul_le_mul_left (n - 9) hA
  have hhi := Nat.mul_le_mul_left (n - 9) hB
  have hB2 : B = 2 := by omega
  have h9 : n = 9 := by omega
  have hT : T = 14 := by omega
  have he (j : Fin n) (hj : j ∈ Iᶜ) : B ≤ kernelCount H (insert j I) := by
    by_contra! hlt
    have hlt' := Finset.sum_lt_sum
      (s := Iᶜ) (g := fun _ => B)
      (fun k _ => kernelCount_mono (W := H) le_rfl (Finset.subset_insert k I))
      ⟨j, hj, hlt⟩
    rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_compl, Fintype.card_fin,
      hI] at hlt'
    change T < (n - 2) * B at hlt'
    have hright : (n - 2) * B = 14 := by rw [hB2]; omega
    omega
  have hk := kernel_eq_bot_of_extensions H I he
  change 2 ^ dim (siteKernel H I) = 2 at hB2
  rw [congrArg (fun P : Submodule F (E n) => dim P) hk, finrank_bot] at hB2
  omega

/-- At length eight a pair cannot have an injective radical projection. -/
theorem pair_kernel_dim_pos_at_eight (U : Submodule F (E 8)) (hU : ZeroBound U)
    (hdU : dim U = 8) (I : Finset (Fin 8)) (hI : I.card = 2) :
    0 < dim (siteKernel (radical U) I) := by
  by_contra! hdim
  have hB : kernelCount (radical U) I = 1 := by simp [kernelCount, Nat.eq_zero_of_le_zero hdim]
  have hA : 16 ≤ kernelCount U I := kernelCount_lower U I 4 (by rw [hI, hdU])
  have hmain := pair_arithmetic U hU I hI (by decide)
  have hsum := pair_sum_upper (radical U) I
  rw [hI, hB] at hsum
  rw [hB] at hmain
  omega

/-- At length at least nine the radical projects to at most a line on each site. -/
theorem radical_site_rank_le_one (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) (hn : 9 ≤ n) (i : Fin n) :
    dim (LinearMap.range ((restrictSites {i}).domRestrict (radical U))) ≤ 1 := by
  classical
  let H := radical U
  have hdim := dim_kernel_add_rank H {i}
  by_contra! hr
  have hsmall : dim (siteKernel H {i}) ≤ 2 := by
    change dim H = 4 at hdH
    change 1 < dim (LinearMap.range ((restrictSites {i}).domRestrict H)) at hr
    omega
  have hbot := kernel_eq_bot_of_extensions H {i} (fun j hj => by
    have hne : j ≠ i := by simpa using hj
    have hp := pair_kernel_dim_ge_two U hU hdU hn (insert j {i}) (by simp [hne])
    change 2 ≤ dim (siteKernel H (insert j {i})) at hp
    exact Nat.pow_le_pow_right (by decide) (hsmall.trans hp))
  have hh := dim_siteKernel_lower H {i}
  rw [congrArg (fun P : Submodule F (E n) => dim P) hbot] at hh
  simp at hh
  change dim H = 4 at hdH
  omega

/-- The sites on which at least one word in the subspace has a nonzero coordinate pair. -/
noncomputable def support (W : Submodule F (E n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∃ v ∈ W, site i v ≠ 0

theorem mem_support {W : Submodule F (E n)} {i : Fin n} :
    i ∈ support W ↔ ∃ v ∈ W, site i v ≠ 0 := by
  classical
  simp [support]

private theorem site_zero_outside_support {W : Submodule F (E n)} {i : Fin n}
    (hi : i ∉ support W) {v : E n} (hv : v ∈ W) : site i v = 0 := by
  by_contra h
  exact hi (mem_support.mpr ⟨v, hv, h⟩)

/-- The ambient words supported on a specified set of sites. -/
def supportedOn (I : Finset (Fin n)) : Submodule F (E n) := siteKernel ⊤ Iᶜ

private theorem mem_supportedOn {I : Finset (Fin n)} {v : E n} :
    v ∈ supportedOn I ↔ ∀ i ∉ I, site i v = 0 := by
  simp [supportedOn, mem_siteKernel]

private theorem supportedOn_mono {I J : Finset (Fin n)} (h : I ⊆ J) :
    supportedOn I ≤ supportedOn J :=
  fun _ hv => mem_supportedOn.mpr (fun i hi => mem_supportedOn.mp hv i (fun hi' => hi (h hi')))

private theorem le_supportedOn_support (W : Submodule F (E n)) :
    W ≤ supportedOn (support W) :=
  fun _ hv => mem_supportedOn.mpr (fun _ hi => site_zero_outside_support hi hv)

/-- Zero all the sites outside the given set in the ambient space. -/
def mask (I : Finset (Fin n)) : E n →ₗ[F] E n where
  toFun v := (fun i => if i ∈ I then v.1 i else 0, fun i => if i ∈ I then v.2 i else 0)
  map_add' u v := by
    ext i <;> by_cases hi : i ∈ I <;> simp [hi]
  map_smul' a u := by
    ext i <;> by_cases hi : i ∈ I <;> simp [hi]

private theorem site_mask (I : Finset (Fin n)) (i : Fin n) (v : E n) :
    site i (mask I v) = if i ∈ I then site i v else 0 := by
  by_cases hi : i ∈ I <;> simp [mask, site, hi]

private theorem mask_mem_supportedOn (I : Finset (Fin n)) (v : E n) :
    mask I v ∈ supportedOn I :=
  mem_supportedOn.mpr (fun i hi => by simp [site_mask, hi])

private theorem mask_eq_self {I : Finset (Fin n)} {v : E n} (h : v ∈ supportedOn I) :
    mask I v = v := by
  have hs (i : Fin n) : site i (mask I v) = site i v := by
    by_cases hi : i ∈ I <;> simp [site_mask, hi, mem_supportedOn.mp h]
  exact Prod.ext (funext fun i => congrArg Prod.fst (hs i))
    (funext fun i => congrArg Prod.snd (hs i))

private theorem dim_ambient : dim (E n) = 2 * n := by
  simp [Module.finrank_prod, two_mul]

private theorem dim_supportedOn (I : Finset (Fin n)) :
    dim (supportedOn I) = 2 * I.card := by
  have hs : Function.Surjective ((restrictSites Iᶜ).domRestrict (⊤ : Submodule F (E n))) := by
    intro f
    let v : E n := (fun i => if h : i ∈ Iᶜ then (f ⟨i, h⟩).1 else 0,
                    fun i => if h : i ∈ Iᶜ then (f ⟨i, h⟩).2 else 0)
    refine ⟨⟨v, Submodule.mem_top⟩, ?_⟩
    funext i
    change site i v = f i
    have hi := Finset.mem_compl.mp i.property
    simp [site, v, hi]
  have hd := dim_kernel_add_rank (⊤ : Submodule F (E n)) Iᶜ
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_top, dim_ambient] at hd
  have hr : dim (↥(Iᶜ) → F × F) = 2 * (n - I.card) := by
    simp [Module.finrank_pi_fintype, Module.finrank_prod, Finset.card_compl, Nat.mul_comm]
  rw [hr] at hd
  have hI : I.card ≤ n := by simpa using I.card_le_univ
  change dim (supportedOn I) + 2 * (n - I.card) = 2 * n at hd
  omega

private theorem sp_eq_zero_of_disjoint_support {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    {u v : E n} (hu : u ∈ supportedOn I) (hv : v ∈ supportedOn J) :
    spForm n u v = 0 := by
  change sp u v = 0
  unfold sp
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ I
  · have hv0 := mem_supportedOn.mp hv i (fun hj => Finset.disjoint_left.mp hIJ hi hj)
    have h1 : v.1 i = 0 := congrArg Prod.fst hv0
    have h2 : v.2 i = 0 := congrArg Prod.snd hv0
    simp [h1, h2]
  · have hu0 := mem_supportedOn.mp hu i hi
    have h1 : u.1 i = 0 := congrArg Prod.fst hu0
    have h2 : u.2 i = 0 := congrArg Prod.snd hu0
    simp [h1, h2]

private theorem supportedOn_orthogonal (I : Finset (Fin n)) :
    (spForm n).orthogonal (supportedOn I) = supportedOn Iᶜ := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · intro v hv
    exact fun u hu => sp_eq_zero_of_disjoint_support (disjoint_compl_right) hu hv
  · rw [LinearMap.BilinForm.finrank_orthogonal (sp_nondegenerate n), dim_ambient,
      dim_supportedOn, dim_supportedOn]
    simp only [Finset.card_compl, Fintype.card_fin]
    have hI : I.card ≤ n := by simpa using I.card_le_univ
    omega

private theorem radical_le_orthogonal (U : Submodule F (E n)) :
    U ≤ (spForm n).orthogonal (radical U) := by
  intro u hu h hh
  exact (sp_alt n).isRefl _ _ (hh.2 u hu)

private theorem sp_mask_eq (I : Finset (Fin n)) {h u : E n} (hh : h ∈ supportedOn I) :
    spForm n h (mask I u) = spForm n h u := by
  change sp h (mask I u) = sp h u
  unfold sp
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I
  · simp [mask, hi]
  · have hs := mem_supportedOn.mp hh i hi
    have h1 : h.1 i = 0 := congrArg Prod.fst hs
    have h2 : h.2 i = 0 := congrArg Prod.snd hs
    simp [h1, h2]

private theorem kernel_le_radical (U : Submodule F (E n)) (hU : ZeroBound U)
    (I : Finset (Fin n)) (hI : 4 ≤ I.card) : siteKernel U I ≤ radical U := by
  intro v hv
  obtain ⟨hvU, hz⟩ := mem_siteKernel.mp hv
  by_contra h
  have hle : I.card ≤ zeroCount v := Finset.card_le_card (fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz i hi⟩)
  have := hU v hvU h
  omega

theorem core_injective (U : Submodule F (E n)) (hU : ZeroBound U)
    (hS : 4 ≤ (support (radical U)).card) :
    Function.Injective ((mask (support (radical U))).domRestrict U) := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro u hu
  have hu0 : mask (support (radical U)) (u : E n) = 0 := hu
  have hz : (u : E n) ∈ siteKernel U (support (radical U)) := by
    refine mem_siteKernel.mpr ⟨u.property, fun i hi => ?_⟩
    have he := congrArg (site i) hu0
    simpa [site_mask, hi] using he
  have hr := kernel_le_radical U hU _ hS hz
  have hs := mask_eq_self (le_supportedOn_support (radical U) hr)
  exact Subtype.ext (hs.symm.trans hu0)

theorem core_le_orthogonal (U : Submodule F (E n)) :
    U.map (mask (support (radical U))) ≤
      (spForm n).orthogonal (radical U) ⊓ supportedOn (support (radical U)) := by
  rintro v ⟨u, hu, rfl⟩
  refine ⟨?_, mask_mem_supportedOn _ _⟩
  intro h hh
  rw [sp_mask_eq _ (le_supportedOn_support (radical U) hh)]
  exact radical_le_orthogonal U hu h hh

private theorem dim_orthogonal_supportedOn (H : Submodule F (E n)) (J : Finset (Fin n)) :
    dim ((spForm n).orthogonal H ⊓ supportedOn J : Submodule F (E n)) + dim H =
      2 * J.card + dim (H ⊓ supportedOn Jᶜ : Submodule F (E n)) := by
  let B := spForm n
  have hspace : B.orthogonal (H ⊔ supportedOn Jᶜ) = B.orthogonal H ⊓ supportedOn J := by
    have hj : (spForm n).orthogonal (supportedOn Jᶜ) = supportedOn J := by
      rw [supportedOn_orthogonal, compl_compl]
    change (spForm n).orthogonal (H ⊔ supportedOn Jᶜ) =
      (spForm n).orthogonal H ⊓ supportedOn J
    rw [← hj]
    ext v
    simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
        fun u hu => h u (Submodule.mem_sup_right hu)⟩
    · rintro ⟨hH, hJ⟩ u hu
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
      simp [hH x hx, hJ y hy]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq H (supportedOn Jᶜ)
  rw [dim_supportedOn, Finset.card_compl, Fintype.card_fin] at hdim
  have horth := LinearMap.BilinForm.finrank_orthogonal (sp_nondegenerate n) (H ⊔ supportedOn Jᶜ)
  change dim (B.orthogonal (H ⊔ supportedOn Jᶜ)) =
    dim (E n) - dim (H ⊔ supportedOn Jᶜ : Submodule F (E n)) at horth
  rw [congrArg (fun P : Submodule F (E n) => dim P) hspace, dim_ambient] at horth
  have hsup := Submodule.finrank_le (H ⊔ supportedOn Jᶜ)
  have hJ : J.card ≤ n := by simpa using J.card_le_univ
  rw [dim_ambient] at hsup
  change dim (B.orthogonal H ⊓ supportedOn J : Submodule F (E n)) + dim H = _
  omega

private theorem dim_core_orthogonal (U : Submodule F (E n)) :
    dim ((spForm n).orthogonal (radical U) ⊓ supportedOn (support (radical U)) :
      Submodule F (E n)) + dim (radical U) = 2 * (support (radical U)).card := by
  have h := dim_orthogonal_supportedOn (radical U) (support (radical U))
  have hbot : radical U ⊓ supportedOn (support (radical U))ᶜ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    apply eq_zero_of_every_site
    intro i
    by_cases hi : i ∈ support (radical U)
    · exact mem_supportedOn.mp hv.2 i (by simpa using hi)
    · exact site_zero_outside_support hi hv.1
  rw [congrArg (fun P : Submodule F (E n) => dim P) hbot, finrank_bot, add_zero] at h
  exact h

private theorem dim_core (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdH : dim (radical U) = 4) :
    dim (U.map (mask (support (radical U)))) = dim U := by
  have hle : radical U ≤
      (spForm n).orthogonal (radical U) ⊓ supportedOn (support (radical U)) :=
    fun _ hv => ⟨radical_le_orthogonal U ((show radical U ≤ U from inf_le_left) hv),
      le_supportedOn_support (radical U) hv⟩
  have hS := Submodule.finrank_mono hle
  have hdim := dim_core_orthogonal U
  have hinj := core_injective U hU (by omega)
  have h := LinearMap.finrank_range_of_inj hinj
  rw [congrArg (fun P : Submodule F (E n) => dim P)
    (LinearMap.range_domRestrict U (mask (support (radical U))))] at h
  exact h

private theorem six_le_support (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) : 6 ≤ (support (radical U)).card := by
  have h := dim_core_orthogonal U
  have hle := Submodule.finrank_mono (core_le_orthogonal U)
  rw [dim_core U hU hdH, hdU] at hle
  omega

private theorem core_full_at_six (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) (hS : (support (radical U)).card = 6) :
    U.map (mask (support (radical U))) =
      (spForm n).orthogonal (radical U) ⊓ supportedOn (support (radical U)) := by
  apply Submodule.eq_of_le_of_finrank_le (core_le_orthogonal U)
  have h := dim_core_orthogonal U
  rw [dim_core U hU hdH, hdU]
  omega

private theorem orthogonal_on_pair_at_six (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) (hS : (support (radical U)).card = 6)
    (J : Finset (Fin n)) (hJ : J ⊆ support (radical U)) (hJ2 : J.card = 2) :
    (spForm n).orthogonal (radical U) ⊓ supportedOn J = radical U ⊓ supportedOn J := by
  classical
  let H := radical U
  let S := support H
  apply le_antisymm _ (inf_le_inf_right _ (fun _ h => radical_le_orthogonal U ((show radical U ≤ U from inf_le_left) h)))
  intro v hv
  have hv' : v ∈ (spForm n).orthogonal H ⊓ supportedOn S :=
    ⟨hv.1, supportedOn_mono hJ hv.2⟩
  have hm : v ∈ U.map (mask S) := (core_full_at_six U hU hdU hdH hS).symm ▸ hv'
  obtain ⟨u, hu, rfl⟩ := hm
  have hcard : 4 ≤ (S \ J).card := by
    change J ⊆ S at hJ
    rw [Finset.card_sdiff_of_subset hJ]
    change S.card = 6 at hS
    omega
  have hk : u ∈ siteKernel U (S \ J) := by
    refine mem_siteKernel.mpr ⟨hu, fun i hi => ?_⟩
    obtain ⟨hiS, hiJ⟩ := Finset.mem_sdiff.mp hi
    have hh := mem_supportedOn.mp hv.2 i hiJ
    rwa [site_mask, ite_eq_left hiS] at hh
  have hr := kernel_le_radical U hU _ hcard hk
  have he := mask_eq_self (le_supportedOn_support H hr)
  exact ⟨he.symm ▸ hr, hv.2⟩

private theorem pair_balance_at_six (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) (hS : (support (radical U)).card = 6)
    (J : Finset (Fin n)) (hJ : J ⊆ support (radical U)) (hJ2 : J.card = 2) :
    dim (radical U ⊓ supportedOn J : Submodule F (E n)) =
      dim (radical U ⊓ supportedOn (support (radical U) \ J) : Submodule F (E n)) := by
  let H := radical U
  have he : H ⊓ supportedOn Jᶜ = H ⊓ supportedOn (support H \ J) := by
    ext v
    simp only [Submodule.mem_inf, mem_supportedOn]
    refine and_congr_right fun hv => ⟨?_, ?_⟩
    · intro h i hi
      by_cases hiS : i ∈ support H
      · apply h
        simpa using (show i ∈ J from by
          by_contra hiJ
          exact hi (Finset.mem_sdiff.mpr ⟨hiS, hiJ⟩))
      · exact site_zero_outside_support hiS hv
    · intro h i hi
      exact h i (fun hmem => hi (Finset.mem_compl.mpr (Finset.mem_sdiff.mp hmem).2))
  have hh := dim_orthogonal_supportedOn H J
  rw [congrArg (fun P : Submodule F (E n) => dim P) he,
    congrArg (fun P : Submodule F (E n) => dim P)
      (orthogonal_on_pair_at_six U hU hdU hdH hS J hJ hJ2), hJ2] at hh
  change dim H = 4 at hdH
  change dim (H ⊓ supportedOn J : Submodule F (E n)) + dim H =
    2 * 2 + dim (H ⊓ supportedOn (support H \ J) : Submodule F (E n)) at hh
  change dim (H ⊓ supportedOn J : Submodule F (E n)) =
    dim (H ⊓ supportedOn (support H \ J) : Submodule F (E n))
  omega

private theorem disjoint_supportedOn {J K : Finset (Fin n)} (h : Disjoint J K) :
    Disjoint (supportedOn J) (supportedOn K) := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro v hv
  apply eq_zero_of_every_site
  intro i
  by_cases hi : i ∈ J
  · exact mem_supportedOn.mp hv.2 i (fun hk => Finset.disjoint_left.mp h hi hk)
  · exact mem_supportedOn.mp hv.1 i hi

private theorem pair_orthogonal_bot_at_six (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) (hS : (support (radical U)).card = 6)
    (J : Finset (Fin n)) (hJ : J ⊆ support (radical U)) (hJ2 : J.card = 2) :
    (spForm n).orthogonal (radical U) ⊓ supportedOn J = ⊥ := by
  classical
  let H := radical U
  let S := support H
  let h (L : Finset (Fin n)) := dim (H ⊓ supportedOn L : Submodule F (E n))
  have hmono {A B : Finset (Fin n)} (hab : A ⊆ B) : h A ≤ h B :=
    Submodule.finrank_mono (inf_le_inf_left _ (supportedOn_mono hab))
  have hbalance (A : Finset (Fin n)) (ha : A ⊆ S) (ha2 : A.card = 2) :
      h A = h (S \ A) := pair_balance_at_six U hU hdU hdH hS A ha ha2
  have hd (A B : Finset (Fin n)) (ha : A ⊆ S) (hb : B ⊆ S)
      (ha2 : A.card = 2) (hb2 : B.card = 2) (hab : Disjoint A B) : h A = h B := by
    apply le_antisymm
    · rw [hbalance B hb hb2]
      exact hmono (Finset.subset_sdiff.mpr ⟨ha, hab⟩)
    · rw [hbalance A ha ha2]
      exact hmono (Finset.subset_sdiff.mpr ⟨hb, hab.symm⟩)
  have heq (A B : Finset (Fin n)) (ha : A ⊆ S) (hb : B ⊆ S)
      (ha2 : A.card = 2) (hb2 : B.card = 2) : h A = h B := by
    have hu : (A ∪ B).card ≤ 4 := by
      have := Finset.card_union_le A B
      omega
    have hs : 2 ≤ (S \ (A ∪ B)).card := by
      rw [Finset.card_sdiff_of_subset (Finset.union_subset ha hb)]
      change S.card = 6 at hS
      omega
    obtain ⟨C, hc, hc2⟩ := Finset.exists_subset_card_eq hs
    have hcS : C ⊆ S := hc.trans Finset.sdiff_subset
    have hdis := (Finset.subset_sdiff.mp hc).2
    have hca : Disjoint C A := hdis.mono_right Finset.subset_union_left
    have hcb : Disjoint C B := hdis.mono_right Finset.subset_union_right
    exact (hd A C ha hcS ha2 hc2 hca.symm).trans (hd C B hcS hb hc2 hb2 hcb)
  have hcomp : (S \ J).card = 4 := by
    change J ⊆ S at hJ
    rw [Finset.card_sdiff_of_subset hJ]
    change S.card = 6 at hS
    omega
  obtain ⟨A, ha, ha2⟩ := Finset.exists_subset_card_eq (s := S \ J) (n := 2) (by omega)
  let B := (S \ J) \ A
  have hb : B ⊆ S \ J := Finset.sdiff_subset
  have hb2 : B.card = 2 := by simp [B, Finset.card_sdiff_of_subset ha, hcomp, ha2]
  have hab : Disjoint A B :=
    (Finset.subset_sdiff.mp (show B ⊆ (S \ J) \ A from le_rfl)).2.symm
  have hs : h A + h B ≤ h (S \ J) := by
    let P : Submodule F (E n) := H ⊓ supportedOn A
    let Q : Submodule F (E n) := H ⊓ supportedOn B
    have hpq : Disjoint P Q :=
      (disjoint_supportedOn hab).mono inf_le_right inf_le_right
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [congrArg (fun R : Submodule F (E n) => dim R) hpq.eq_bot, finrank_bot, add_zero] at hsum
    have hle : P ⊔ Q ≤ H ⊓ supportedOn (S \ J) :=
      sup_le (inf_le_inf_left _ (supportedOn_mono ha)) (inf_le_inf_left _ (supportedOn_mono hb))
    exact hsum ▸ Submodule.finrank_mono hle
  have haJ := heq A J (ha.trans Finset.sdiff_subset) hJ ha2 hJ2
  have hbJ := heq B J (hb.trans Finset.sdiff_subset) hJ hb2 hJ2
  have hj := hbalance J hJ hJ2
  rw [orthogonal_on_pair_at_six U hU hdU hdH hS J hJ hJ2]
  apply Submodule.finrank_eq_zero.mp
  change h J = 0
  omega

private def errorSites {S : Finset (Fin n)} :
    Option (S × {p : F × F // p ≠ 0}) → Finset (Fin n)
  | none => ∅
  | some (i, _) => {i.val}

private def errorWord {S : Finset (Fin n)} : Option (S × {p : F × F // p ≠ 0}) → E n
  | none => 0
  | some (i, p) => (Pi.single i.val p.val.1, Pi.single i.val p.val.2)

private theorem site_errorWord {S : Finset (Fin n)} (i : S) (p : {p : F × F // p ≠ 0})
    (j : Fin n) : site j (errorWord (some (i, p))) = if j = i.val then p.val else 0 := by
  by_cases h : j = i.val <;> simp [site, errorWord, h]

private theorem errorSites_subset {S : Finset (Fin n)}
    (a : Option (S × {p : F × F // p ≠ 0})) : errorSites a ⊆ S := by
  cases a with
  | none => simp [errorSites]
  | some a => rcases a with ⟨i, p⟩; simp [errorSites]

private theorem errorSites_card {S : Finset (Fin n)} (a : Option (S × {p : F × F // p ≠ 0})) :
    (errorSites a).card ≤ 1 := by
  rcases a with _ | ⟨i, p⟩ <;> simp [errorSites]

private theorem errorWord_mem {S : Finset (Fin n)} (a : Option (S × {p : F × F // p ≠ 0})) :
    errorWord a ∈ supportedOn (errorSites a) := by
  cases a with
  | none => exact Submodule.zero_mem _
  | some a =>
    rcases a with ⟨i, p⟩
    exact mem_supportedOn.mpr (fun j hj => by
      have h : j ≠ i.val := by simpa [errorSites] using hj
      simp [site_errorWord, h])

private theorem errorWord_injective (S : Finset (Fin n)) :
    Function.Injective (errorWord (S := S)) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      rcases b with ⟨j, q⟩
      have h := congrArg (site j.val) hab
      rw [site_errorWord, ite_eq_left rfl] at h
      have hq : (q : F × F) = 0 := by simpa [errorWord] using h.symm
      exact (q.property hq).elim
  | some a =>
    rcases a with ⟨i, p⟩
    have hp := congrArg (site i.val) hab
    rw [site_errorWord, ite_eq_left rfl] at hp
    cases b with
    | none => exact (p.property (by simpa [errorWord] using hp)).elim
    | some b =>
      rcases b with ⟨j, q⟩
      rw [site_errorWord] at hp
      split at hp
      · rename_i hij
        obtain rfl : i = j := Subtype.ext hij
        obtain rfl : p = q := Subtype.ext hp
        rfl
      · exact (p.property hp).elim

/-- An eight-dimensional code with a four-dimensional radical and the zero bound has support
at least seven on its radical. -/
theorem seven_le_support (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) : 7 ≤ (support (radical U)).card := by
  classical
  let H := radical U
  let S := support H
  let O := (spForm n).orthogonal H
  have h6 : 6 ≤ S.card := six_le_support U hU hdU hdH
  by_contra! h7
  have hS : S.card = 6 := by change S.card < 7 at h7; omega
  let L := Option (↥S × {p : F × F // p ≠ 0})
  let f : L → E n ⧸ O := fun a => O.mkQ (errorWord a)
  have hinj : Function.Injective f := by
    intro a b hab
    have hq : errorWord a - errorWord b ∈ O := by
      change O.mkQ (errorWord a) = O.mkQ (errorWord b) at hab
      rw [← sub_eq_zero, ← map_sub] at hab
      exact (Submodule.Quotient.mk_eq_zero O).mp hab
    let K := errorSites a ∪ errorSites b
    have hkS : K ⊆ S := Finset.union_subset (errorSites_subset a) (errorSites_subset b)
    have hk2 : K.card ≤ 2 := by
      have := Finset.card_union_le (errorSites a) (errorSites b)
      have := errorSites_card a
      have := errorSites_card b
      change (errorSites a ∪ errorSites b).card ≤ 2
      omega
    obtain ⟨D, hD, hDcard⟩ := Finset.exists_subset_card_eq
      (s := S \ K) (n := 2 - K.card) (by rw [Finset.card_sdiff_of_subset hkS]; omega)
    let J := K ∪ D
    have hJ : J ⊆ S := Finset.union_subset hkS (hD.trans Finset.sdiff_subset)
    have hJ2 : J.card = 2 := by
      rw [show J = K ∪ D from rfl, Finset.card_union_of_disjoint
        (Finset.subset_sdiff.mp hD).2.symm, hDcard]
      omega
    have haJ : errorSites a ⊆ J := Finset.subset_union_left.trans Finset.subset_union_left
    have hbJ : errorSites b ⊆ J := Finset.subset_union_right.trans Finset.subset_union_left
    have hvJ := (supportedOn J).sub_mem (supportedOn_mono haJ (errorWord_mem a))
      (supportedOn_mono hbJ (errorWord_mem b))
    have hv : errorWord a - errorWord b ∈ O ⊓ supportedOn J := ⟨hq, hvJ⟩
    rw [show O ⊓ supportedOn J = ⊥ from
      pair_orthogonal_bot_at_six U hU hdU hdH hS J hJ hJ2] at hv
    exact errorWord_injective S (sub_eq_zero.mp ((Submodule.mem_bot F).mp hv))
  let _ : Fintype (E n ⧸ O) := Fintype.ofFinite _
  have hcard := Fintype.card_le_of_injective f hinj
  have hL : Fintype.card L = 19 := by
    have hpair : Fintype.card {p : F × F // p ≠ 0} = 3 := by decide
    simp [L, hpair, hS]
  have hO := LinearMap.BilinForm.finrank_orthogonal (sp_nondegenerate n) H
  change dim O = dim (E n) - dim H at hO
  change dim H = 4 at hdH
  have hQ := Submodule.finrank_quotient_add_finrank O
  have hdim : dim (E n ⧸ O) = 4 := by
    rw [dim_ambient, hdH] at hO
    rw [dim_ambient] at hQ
    have hn : 6 ≤ n := h6.trans (by simpa using S.card_le_univ)
    omega
  rw [hL, Module.card_eq_pow_finrank (K := F), ZMod.card, hdim] at hcard
  omega

private theorem siteKernel_single_eq_self {H : Submodule F (E n)} {i : Fin n}
    (hi : i ∉ support H) : siteKernel H {i} = H := by
  refine le_antisymm inf_le_left fun v hv => mem_siteKernel.mpr ⟨hv, ?_⟩
  intro j hj
  obtain rfl := Finset.mem_singleton.mp hj
  exact site_zero_outside_support hi hv

private theorem dim_occupied_kernel (H : Submodule F (E n)) (hdH : dim H = 4)
    (hr : ∀ i, dim (LinearMap.range ((restrictSites {i}).domRestrict H)) ≤ 1)
    (i : Fin n) (hi : i ∈ support H) : dim (siteKernel H {i}) = 3 := by
  have hne : siteKernel H {i} ≠ H := by
    intro he
    obtain ⟨v, hv, hz⟩ := mem_support.mp hi
    exact hz ((mem_siteKernel.mp (he.symm ▸ hv)).2 i (by simp))
  have hh : dim (siteKernel H {i}) < dim H := Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne inf_le_left hne)
  have := dim_kernel_add_rank H {i}
  have := hr i
  omega

private theorem siteKernel_pair (H : Submodule F (E n)) (i j : Fin n) :
    siteKernel H (insert j {i}) = siteKernel H {i} ⊓ siteKernel H {j} := by
  ext v
  simp only [mem_siteKernel, Submodule.mem_inf, Finset.forall_mem_insert,
    Finset.mem_singleton, forall_eq]
  tauto

private theorem occupied_type_size (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) (hn : 9 ≤ n)
    (i : Fin n) (hi : i ∈ support (radical U)) :
    3 * n ≤ 30 + (n - (support (radical U)).card) +
      ((support (radical U)).filter fun j =>
        siteKernel (radical U) {j} = siteKernel (radical U) {i}).card := by
  classical
  let H := radical U
  let S := support H
  let K (j : Fin n) := siteKernel H {j}
  let M := S.filter fun j => K j = K i
  let Q := Sᶜ ∪ M
  have hdim := dim_occupied_kernel H hdH (radical_site_rank_le_one U hU hdU hdH hn)
  change i ∈ S at hi
  have hKi : dim (K i) = 3 := hdim i hi
  have hcount (j : Fin n) : kernelCount H (insert j {i}) = 4 + (if j ∈ Q then 4 else 0) := by
    have hK : K i ≤ H := inf_le_left
    rw [kernelCount, congrArg (fun P : Submodule F (E n) => dim P) (siteKernel_pair H i j)]
    change 2 ^ dim (K i ⊓ K j : Submodule F (E n)) = _
    by_cases hj : j ∈ S
    · by_cases he : K j = K i
      · have hQ : j ∈ Q := Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, he⟩)
        have hinf : K i ⊓ K j = K i := by rw [he, inf_idem]
        rw [congrArg (fun P : Submodule F (E n) => dim P) hinf, hKi]
        simp [hQ]
      · have hQ : j ∉ Q := by simp [Q, M, hj, he]
        have hKj := hdim j hj
        change dim (K j) = 3 at hKj
        have hsub : K i < K i ⊔ K j := by
          apply lt_of_le_of_ne le_sup_left
          intro hh
          apply he
          apply Submodule.eq_of_le_of_finrank_le
          · rw [hh]
            exact le_sup_right
          · omega
        have hlt := Submodule.finrank_lt_finrank_of_lt hsub
        have hle := Submodule.finrank_mono (sup_le hK (show K j ≤ H from inf_le_left))
        have hsup := Submodule.finrank_sup_add_finrank_inf_eq (K i) (K j)
        have hd : dim (K i ⊓ K j : Submodule F (E n)) = 2 := by
          change dim H = 4 at hdH
          omega
        simp [hQ, hd]
    · have hQ : j ∈ Q := Finset.mem_union_left _ (Finset.mem_compl.mpr hj)
      rw [show K j = H from siteKernel_single_eq_self hj, inf_of_le_left hK, hKi]
      simp [hQ]
  have hdis : Disjoint Sᶜ M := Finset.disjoint_left.mpr fun j hj hm =>
    (Finset.mem_compl.mp hj) (Finset.mem_filter.mp hm).1
  have hiQ : i ∈ Q := Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  have hcardQ : Q.card = (n - S.card) + M.card := by
    simp [Q, Finset.card_union_of_disjoint hdis, Finset.card_compl]
  have hsum : (∑ j ∈ ({i} : Finset (Fin n))ᶜ, kernelCount H (insert j {i})) =
      (n - 1) * 4 + (Q.card - 1) * 4 := by
    have hf : ((({i} : Finset (Fin n))ᶜ).filter fun j => j ∈ Q) = Q.erase i := by
      ext j
      simp
    simp_rw [hcount]
    rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero, hf]
    simp [Finset.card_compl, Finset.card_erase_of_mem hiQ, Nat.nsmul_eq_mul]
  have hA : 64 ≤ kernelCount U {i} := kernelCount_lower U {i} 6 (by simp [hdU])
  have hB : kernelCount H {i} = 8 :=
    show 2 ^ dim (K i) = 8 by rw [hKi]; decide
  have h := kernelCount_inequality U hU {i}
  change ((n - 1) * kernelCount U {i} + 8 * kernelCount H {i} ≤
    8 * kernelCount U {i} +
      4 * ∑ j ∈ ({i} : Finset (Fin n))ᶜ, kernelCount H (insert j {i})) at h
  rw [show n - 1 = (n - 9) + 8 by omega, add_mul, hB, hsum] at h
  have hlo := Nat.mul_le_mul_left (n - 9) hA
  change 3 * n ≤ 30 + (n - S.card) + M.card
  omega

private theorem dim_le_inf_card (H : Submodule F (E n)) (T : Finset (Submodule F (E n)))
    (hT : ∀ K ∈ T, K ≤ H ∧ dim H = dim K + 1) :
    dim H ≤ dim (H ⊓ T.inf id : Submodule F (E n)) + T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [congrArg (fun R : Submodule F (E n) => dim R)
      (show H ⊓ (∅ : Finset (Submodule F (E n))).inf id = H by simp), Finset.card_empty, add_zero]
  | @insert K T hk ih =>
    have hrest := ih (fun L hL => hT L (Finset.mem_insert_of_mem hL))
    obtain ⟨hle, hK⟩ := hT K (Finset.mem_insert_self K T)
    let P := H ⊓ T.inf id
    have hsup := Submodule.finrank_mono (sup_le (show P ≤ H from inf_le_left) hle)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq P K
    have he : H ⊓ (insert K T).inf id = P ⊓ K := by
      rw [Finset.inf_insert, id_eq]
      change H ⊓ (K ⊓ T.inf id) = (H ⊓ T.inf id) ⊓ K
      ac_rfl
    rw [congrArg (fun R : Submodule F (E n) => dim R) he, Finset.card_insert_of_notMem hk]
    change dim H ≤ dim P + T.card at hrest
    omega

/-- The occupied rank-one types bound the length and the size of the radical support. -/
theorem radical_support_upper_bound (U : Submodule F (E n)) (hU : ZeroBound U)
    (hdU : dim U = 8) (hdH : dim (radical U) = 4) (hn : 9 ≤ n) :
    8 * n + 3 * (support (radical U)).card ≤ 120 ∧ (support (radical U)).card ≤ 10 := by
  classical
  let H := radical U
  let S := support H
  let K (i : Fin n) := siteKernel H {i}
  let T := S.image K
  have hdim (P : Submodule F (E n)) (hP : P ∈ T) : P ≤ H ∧ dim H = dim P + 1 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    have hd := dim_occupied_kernel H hdH (radical_site_rank_le_one U hU hdU hdH hn) i hi
    exact ⟨inf_le_left, by change dim H = 4 at hdH; change dim (K i) = 3 at hd; omega⟩
  have hbot : H ⊓ T.inf id = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    apply eq_zero_of_every_site
    intro i
    by_cases hi : i ∈ S
    · have hKi : K i ∈ T := Finset.mem_image_of_mem K hi
      have hm : v ∈ K i := (Finset.inf_le (f := id) hKi) hv.2
      exact (mem_siteKernel.mp hm).2 i (by simp)
    · exact site_zero_outside_support hi hv.1
  have hcard := dim_le_inf_card H T hdim
  rw [congrArg (fun R : Submodule F (E n) => dim R) hbot, finrank_bot, zero_add] at hcard
  change dim H = 4 at hdH
  obtain ⟨Q, hQT, hQ4⟩ := Finset.exists_subset_card_eq (show 4 ≤ T.card by omega)
  have htype (P : Submodule F (E n)) (hP : P ∈ Q) :
      3 * n ≤ 30 + (n - S.card) + (S.filter fun j => K j = P).card := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hQT hP)
    exact occupied_type_size U hU hdU hdH hn i hi
  have hsum := Finset.sum_le_sum htype
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, hQ4] at hsum
  rw [Finset.sum_card_fiberwise_eq_card_filter] at hsum
  have hmass := Finset.card_filter_le (s := S) (p := fun j => K j ∈ Q)
  have hS : S.card ≤ n := by simpa using S.card_le_univ
  change 8 * n + 3 * S.card ≤ 120 ∧ S.card ≤ 10
  omega

end D5.S3.Quantum.Codes.BinaryEAAttainment
