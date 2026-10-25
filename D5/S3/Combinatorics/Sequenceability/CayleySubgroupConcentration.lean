/- GID: D5/S3/Combinatorics/Sequenceability/CayleySubgroupConcentration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/CayleySubgroupConcentration
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rounded displacement packing and proper stabilizers for Cayley concentration. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! Displacement localization underlying the finite-group concentration argument
of Bedert, Bucić, Kravitz, Montgomery and Müyesser, arXiv:2508.18254v1,
Section 4. The integer shell count is rounded explicitly. The stopping condition
for the subsequent descent is a numerical quadratic-form bound, including for
nonsymmetric sets in nonabelian groups. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration

open scoped BigOperators Pointwise

noncomputable section
attribute [local instance] Classical.propDecidable

def density {K : Type*} [Fintype K] (T : Finset K) : ℝ :=
  (T.card : ℝ) / Fintype.card K

def retained {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (H : Subgroup G) : Finset H :=
  Finset.univ.filter (fun t : H => (t : G) ∈ S)

private def regularIso {K : Type*} [Group K] [Fintype K] (g : K) :
    EuclideanSpace ℝ K ≃ₗᵢ[ℝ] EuclideanSpace ℝ K :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    { toFun := fun x => x * g⁻¹
      invFun := fun x => x * g
      left_inv := by intro x; simp [mul_assoc]
      right_inv := by intro x; simp [mul_assoc] }

private theorem regularIso_apply {K : Type*} [Group K] [Fintype K]
    (g : K) (v : EuclideanSpace ℝ K) (x : K) :
    regularIso g v x = v (x * g) := rfl

private theorem regularIso_one {K : Type*} [Group K] [Fintype K]
    (v : EuclideanSpace ℝ K) : regularIso (1 : K) v = v := by
  ext x
  simp [regularIso_apply]

private theorem regularIso_mul {K : Type*} [Group K] [Fintype K]
    (g h : K) (v : EuclideanSpace ℝ K) :
    regularIso (g * h) v = regularIso g (regularIso h v) := by
  ext x
  simp [regularIso_apply, mul_assoc]

private theorem regularIso_orbit_sum {K : Type*} [Group K] [Fintype K]
    (v : EuclideanSpace ℝ K) (hmean : ∑ x : K, v x = 0) :
    ∑ g : K, regularIso g v = 0 := by
  ext x
  change (∑ g : K, regularIso g v) x = 0
  rw [show (∑ g : K, regularIso g v) x = ∑ g : K, v (x * g) by
    simp [regularIso_apply]]
  rw [Fintype.sum_equiv (Equiv.mulLeft x) (fun g => v (x * g)) v (fun _ => rfl)]
  exact hmean

private def displacement {K : Type*} [Group K] [Fintype K]
    (v : EuclideanSpace ℝ K) (g : K) : ℝ := ‖regularIso g v - v‖

private theorem displacement_mul {K : Type*} [Group K] [Fintype K]
    (v : EuclideanSpace ℝ K) (g h : K) :
    displacement v (g * h) ≤ displacement v g + displacement v h := by
  calc
    ‖regularIso (g * h) v - v‖ =
        ‖regularIso g (regularIso h v - v) + (regularIso g v - v)‖ := by
          rw [map_sub, ← regularIso_mul]
          congr 1
          abel
    _ ≤ ‖regularIso g (regularIso h v - v)‖ + ‖regularIso g v - v‖ := norm_add_le _ _
    _ = displacement v g + displacement v h := by
      rw [(regularIso g).norm_map]
      simp only [displacement, add_comm]

private theorem displacement_inv {K : Type*} [Group K] [Fintype K]
    (v : EuclideanSpace ℝ K) (g : K) : displacement v g⁻¹ = displacement v g := by
  calc
    ‖regularIso g⁻¹ v - v‖ = ‖regularIso g (regularIso g⁻¹ v - v)‖ :=
      ((regularIso g).norm_map _).symm
    _ = ‖v - regularIso g v‖ := by
      rw [map_sub, ← regularIso_mul, mul_inv_cancel, regularIso_one]
    _ = ‖regularIso g v - v‖ := norm_sub_rev _ _

private def lengthBall {K : Type*} [Fintype K] (D : K → ℝ) (r : ℝ) : Finset K :=
  Finset.univ.filter (fun g => D g ≤ r)

private theorem mem_lengthBall {K : Type*} [Fintype K] (D : K → ℝ) (r : ℝ) (g : K) :
    g ∈ lengthBall D r ↔ D g ≤ r := by
  simp [lengthBall]

private theorem lengthBall_mono {K : Type*} [Fintype K] (D : K → ℝ)
    {r s : ℝ} (hrs : r ≤ s) : lengthBall D r ⊆ lengthBall D s := by
  intro g hg
  exact (mem_lengthBall D s g).mpr (le_trans ((mem_lengthBall D r g).mp hg) hrs)

private theorem rounded_plateau {K : Type*} [Group K] [Fintype K]
    (D : K → ℝ) (hmul : ∀ g h, D (g * h) ≤ D g + D h)
    (hinv : ∀ g, D g⁻¹ = D g)
    (τ : ℝ) (hτ : 0 < τ) (hτone : τ ≤ 1)
    (hlarge : (9 / 10 : ℝ) * τ * Fintype.card K ≤ (lengthBall D (τ / 5)).card) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 4 / τ ∧
      lengthBall D ((k : ℝ) * (τ / 5)) =
        lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) := by
  let M : ℕ := ⌊4 / τ⌋₊
  let q : ℕ := (M + 2) / 3
  have ha : 0 < τ / 5 := by positivity
  have hfour : (4 : ℝ) ≤ 4 / τ := (le_div_iff₀ hτ).mpr (by linarith)
  have hM : 4 ≤ M := (Nat.le_floor_iff (by positivity)).mpr hfour
  have hMle : (M : ℝ) ≤ 4 / τ := Nat.floor_le (by positivity)
  have hMlt : 4 / τ < (M : ℝ) + 1 := Nat.lt_floor_add_one (4 / τ)
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hMq : M ≤ 3 * q := by dsimp [q]; omega
  by_contra hplateau
  have hshell (i : Fin q) : ∃ g : K,
      (3 * (i.val : ℝ)) * (τ / 5) < D g ∧
        D g ≤ (3 * (i.val : ℝ) + 1) * (τ / 5) := by
    let k : ℕ := 3 * i.val + 1
    have hk : 1 ≤ k := by omega
    have hkM : k ≤ M := by dsimp [k, q] at *; omega
    have hkbound : (k : ℝ) ≤ 4 / τ := le_trans (by exact_mod_cast hkM) hMle
    have hne : lengthBall D ((k : ℝ) * (τ / 5)) ≠
        lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) := by
      intro he
      exact hplateau ⟨k, hk, hkbound, he⟩
    have hsub : lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) ⊆
        lengthBall D ((k : ℝ) * (τ / 5)) :=
      lengthBall_mono D (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le k 1) ha.le)
    obtain ⟨g, hg, hng⟩ := Finset.not_subset.mp
      (show ¬ lengthBall D ((k : ℝ) * (τ / 5)) ⊆
        lengthBall D (((k - 1 : ℕ) : ℝ) * (τ / 5)) from
          fun h => hne (Finset.Subset.antisymm h hsub))
    have hu := (mem_lengthBall D _ g).mp hg
    have hl : (((k - 1 : ℕ) : ℝ) * (τ / 5)) < D g :=
      lt_of_not_ge (fun h => hng ((mem_lengthBall D _ g).mpr h))
    refine ⟨g, ?_, ?_⟩
    · simpa [k, Nat.cast_add, Nat.cast_mul] using hl
    · simpa [k, Nat.cast_add, Nat.cast_mul] using hu
  choose c hc using hshell
  let B := lengthBall D (τ / 5)
  let pack : Fin q × {b // b ∈ B} → K := fun z => c z.1 * z.2.val
  have hreverse (g b : K) : D g ≤ D (g * b) + D b := by
    simpa [mul_assoc, hinv] using hmul (g * b) b⁻¹
  have hseparate (i j : Fin q) (hji : j < i) (b e : {b // b ∈ B}) :
      c i * b.val ≠ c j * e.val := by
    intro heq
    have hb : D b.val ≤ τ / 5 := (mem_lengthBall D _ _).mp b.property
    have he : D e.val ≤ τ / 5 := (mem_lengthBall D _ _).mp e.property
    have hlow := (hc i).1
    have hupp := le_trans (hmul (c j) e.val) (add_le_add (hc j).2 he)
    have hrev := hreverse (c i) b.val
    rw [heq] at hrev
    have hij : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hji
    nlinarith [mul_le_mul_of_nonneg_right hij ha.le]
  have hpack : Function.Injective pack := by
    rintro ⟨i, b⟩ ⟨j, e⟩ he
    have hij : i = j := by
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim (hseparate j i h e b he.symm)
      · exact h
      · exact False.elim (hseparate i j h b e he)
    subst j
    have hbe : b = e := Subtype.ext (mul_left_cancel he)
    exact Prod.ext rfl hbe
  have hcard : q * B.card ≤ Fintype.card K := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective pack hpack
  have hcardR : (q : ℝ) * (B.card : ℝ) ≤ Fintype.card K := by exact_mod_cast hcard
  have hMqR : (M : ℝ) ≤ 3 * (q : ℝ) := by exact_mod_cast hMq
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hround : 4 < (3 * (q : ℝ) + 1) * τ := by
    have : 4 / τ < 3 * (q : ℝ) + 1 := by linarith
    exact (div_lt_iff₀ hτ).mp this
  have hqtau : (8 / 7 : ℝ) < (q : ℝ) * τ := by
    nlinarith [mul_le_mul_of_nonneg_right hqR hτ.le]
  have hn : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hbig := mul_le_mul_of_nonneg_left hlarge (show (0 : ℝ) ≤ q by positivity)
  dsimp [B] at hcardR
  nlinarith [mul_lt_mul_of_pos_right hqtau hn]

private theorem exists_large_displacement {K : Type*} [Group K] [Fintype K]
    (v : EuclideanSpace ℝ K) (hv : ‖v‖ = 1) (hmean : ∑ x : K, v x = 0) :
    ∃ g : K, (4 / 5 : ℝ) < displacement v g := by
  by_contra! h
  have horbit := regularIso_orbit_sum v hmean
  have hsum : (∑ g : K, (v - regularIso g v)) = (Fintype.card K : ℝ) • v := by
    simp [Finset.sum_sub_distrib, horbit, Nat.cast_smul_eq_nsmul]
  have hnorm := norm_sum_le (Finset.univ : Finset K) (fun g => v - regularIso g v)
  rw [hsum, norm_smul, hv, mul_one, Real.norm_of_nonneg (by positivity)] at hnorm
  have hbound : (∑ g : K, ‖v - regularIso g v‖) ≤
      (Fintype.card K : ℝ) * (4 / 5) := by
    calc
      _ ≤ ∑ _g : K, (4 / 5 : ℝ) := Finset.sum_le_sum (fun g _ => by
        simpa only [displacement, norm_sub_rev] using h g)
      _ = _ := by simp
  have hn : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  linarith

private theorem dense_ball_proper_stabilizer {K : Type*} [Group K] [Fintype K]
    (v : EuclideanSpace ℝ K) (hv : ‖v‖ = 1) (hmean : ∑ x : K, v x = 0)
    (τ : ℝ) (hτ : 0 < τ) (hτone : τ ≤ 1)
    (hlarge : (9 / 10 : ℝ) * τ * Fintype.card K ≤
      (lengthBall (displacement v) (τ / 5)).card) :
    ∃ X : Finset K, 1 ∈ X ∧
      (∀ x ∈ X, displacement v x ≤ 4 / 5) ∧
      MulAction.stabilizer K X ≠ ⊤ ∧
      ∀ b ∈ lengthBall (displacement v) (τ / 5),
        b ∈ MulAction.stabilizer K X := by
  obtain ⟨k, hk, hkbound, hplateau⟩ := rounded_plateau (displacement v)
    (displacement_mul v) (displacement_inv v) τ hτ hτone hlarge
  let X := lengthBall (displacement v) (((k - 1 : ℕ) : ℝ) * (τ / 5))
  have hone : (1 : K) ∈ X := by
    apply (mem_lengthBall _ _ _).mpr
    simp only [displacement, regularIso_one, sub_self, norm_zero]
    positivity
  have hradius : (k : ℝ) * (τ / 5) ≤ 4 / 5 := by
    have := (le_div_iff₀ hτ).mp hkbound
    linarith
  have hsmall : ∀ x ∈ X, displacement v x ≤ 4 / 5 := by
    intro x hx
    exact le_trans ((mem_lengthBall _ _ x).mp hx)
      (le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le k 1)
        (by positivity)) hradius)
  have hstabilize : ∀ b ∈ lengthBall (displacement v) (τ / 5),
      b ∈ MulAction.stabilizer K X := by
    intro b hb
    apply MulAction.mem_stabilizer_finset'.mpr
    intro x hx
    apply (mem_lengthBall _ _ _).mpr
    have hbx : displacement v (b * x) ≤ (k : ℝ) * (τ / 5) := by
      have hb' := (mem_lengthBall _ _ _).mp hb
      have hx' := (mem_lengthBall _ _ _).mp hx
      have hcast : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        exact_mod_cast Nat.sub_add_cancel hk
      have := displacement_mul v b x
      change displacement v (b * x) ≤ _
      nlinarith
    exact (mem_lengthBall _ _ _).mp (hplateau ▸ (mem_lengthBall _ _ _).mpr hbx)
  have hproper : MulAction.stabilizer K X ≠ ⊤ := by
    intro htop
    obtain ⟨g, hg⟩ := exists_large_displacement v hv hmean
    have hgmem : g ∈ MulAction.stabilizer K X := by rw [htop]; trivial
    have hgin : g ∈ X := by
      simpa using MulAction.mem_stabilizer_finset'.mp hgmem hone
    exact (not_lt_of_ge (hsmall g hgin)) hg
  exact ⟨X, hone, hsmall, hproper, hstabilize⟩

/-- A near-invariant mean-zero regular vector localizes almost all original
labels in an actual proper stabilizer. The zero-defect case is included. -/
theorem near_invariant_localization {K : Type*} [Group K] [Fintype K]
    (T : Finset K) (hT : T.Nonempty)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ (density T) ^ 2 / 1000)
    (v : EuclideanSpace ℝ K) (hv : ‖v‖ = 1)
    (hmean : (∑ x : K, v x) = 0)
    (hcorr : (1 - β) * (T.card : ℝ) ≤
      ∑ t ∈ T, ∑ x : K, v x * v (x * t)) :
    ∃ L : Subgroup K, L ≠ ⊤ ∧
      (1 - 50 * β / (density T) ^ 2) * (T.card : ℝ) ≤
        ((retained T L).card : ℝ) := by
  let τ := density T
  have hn : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hτ : 0 < τ := div_pos hd hn
  have hτone : τ ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast T.card_le_univ)
  have hsq (g : K) : displacement v g ^ 2 =
      2 - 2 * ∑ x : K, v x * v (x * g) := by
    simp only [displacement, norm_sub_sq_real, (regularIso g).norm_map, hv,
      PiLp.inner_apply, RCLike.inner_apply, RCLike.conj_to_real, regularIso_apply]
    ring
  have hsecond : (∑ t ∈ T, displacement v t ^ 2) ≤ 2 * β * T.card := by
    simp_rw [hsq]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
      nsmul_eq_mul]
    nlinarith [hcorr]
  let B := lengthBall (displacement v) (τ / 5)
  have hbad : ((T \ B).card : ℝ) * (τ / 5) ^ 2 ≤ 2 * β * T.card := by
    calc
      _ = ∑ _t ∈ T \ B, (τ / 5) ^ 2 := by simp
      _ ≤ ∑ t ∈ T \ B, displacement v t ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        have ht' := Finset.mem_sdiff.mp ht
        have hl : τ / 5 < displacement v t := lt_of_not_ge (fun h =>
          ht'.2 ((mem_lengthBall _ _ _).mpr h))
        nlinarith [show 0 < τ / 5 by positivity]
      _ ≤ ∑ t ∈ T, displacement v t ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hsecond
  have hbad' : ((T \ B).card : ℝ) ≤ 50 * β / τ ^ 2 * T.card := by
    rw [show 50 * β / τ ^ 2 * (T.card : ℝ) =
      (50 * β * T.card) / τ ^ 2 by ring]
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    nlinarith [hbad]
  have hcards : ((T ∩ B).card : ℝ) + ((T \ B).card : ℝ) = T.card := by
    exact_mod_cast Finset.card_inter_add_card_sdiff T B
  have hret : (1 - 50 * β / τ ^ 2) * (T.card : ℝ) ≤ (T ∩ B).card := by
    nlinarith
  have hβsmall : 50 * β / τ ^ 2 ≤ (1 / 20 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hτ)).mpr
    dsimp [τ] at *
    linarith
  have hlarge : (9 / 10 : ℝ) * τ * Fintype.card K ≤ B.card := by
    have hsub : ((T ∩ B).card : ℝ) ≤ B.card := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    have hτn : τ * Fintype.card K = T.card := div_mul_cancel₀ _ hn.ne'
    nlinarith [mul_le_mul_of_nonneg_right hβsmall hd.le]
  obtain ⟨X, _, _, hproper, hcontain⟩ :=
    dense_ball_proper_stabilizer v hv hmean τ hτ hτone hlarge
  let L := MulAction.stabilizer K X
  have hcount : (T ∩ B).card ≤ (retained T L).card := by
    let f : {t // t ∈ T ∩ B} → {t // t ∈ retained T L} := fun t =>
      ⟨⟨t.val, hcontain t.val (Finset.mem_inter.mp t.property).2⟩,
        by simpa [retained] using (Finset.mem_inter.mp t.property).1⟩
    have hf : Function.Injective f := by
      intro t u h
      exact Subtype.ext (congrArg (fun z => (z.val : K)) h)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  refine ⟨L, hproper, le_trans hret ?_⟩
  exact_mod_cast hcount

end
end D5.S3.Combinatorics.Sequenceability.CayleySubgroupConcentration
