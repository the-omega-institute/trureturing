/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal native four-variable collision with two signed spectator slices. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision
import Batteries.Tactic.OpenPrivate

/-! Native power series substitution only. The bivariate signed collision
supplier retains its Carnahan attribution. Both spectator indices may be
negative; no total-degree or spectator positivity premise is imposed.
proof_shape: slice_extend, fourInnerCollision_coeff, fourInnerCollision_signed: bind-only
Consumed by the actual four-field inner iterate transport.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.SupportedFourFieldCollision
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedChannelSeries
open scoped BigOperators
noncomputable section
open private inner_monomial_coeff from
  D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

/-- The original P coordinates become x,y,b+z,z. -/
def fourInnerArguments (R : Type*) [CommRing R] :
    Fin 4 → MvPowerSeries (Fin 4) R :=
  ![MvPowerSeries.X 0, MvPowerSeries.X 1,
    MvPowerSeries.X 2 + MvPowerSeries.X 3, MvPowerSeries.X 3]

theorem fourInner_hasSubst (R : Type*) [CommRing R] :
    MvPowerSeries.HasSubst (fourInnerArguments R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [fourInnerArguments]

def fourInnerCollision {R : Type*} [CommRing R] (P : MvPowerSeries (Fin 4) R) :
    MvPowerSeries (Fin 4) R := MvPowerSeries.subst (fourInnerArguments R) P

def index4 (x y a b : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 x + Finsupp.single 1 y + Finsupp.single 2 a + Finsupp.single 3 b

private def tailLabel : Fin 3 ↪ Fin 4 :=
  ⟨Fin.succ, by intro i j h; exact Fin.succ_inj.mp h⟩

private theorem index4_tail (y a b : ℕ) :
    index4 0 y a b = (SupportedThreeFieldCollision.index3 y a b).embDomain tailLabel := by
  simp [index4, SupportedThreeFieldCollision.index3, Finsupp.embDomain_eq_mapDomain,
    tailLabel, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

private theorem four_monomial_coeff {R : Type*} [CommRing R]
    (d : Fin 4 →₀ ℕ) (x y a b : ℕ) :
    MvPowerSeries.coeff (index4 x y a b)
      (d.prod (fun i n => (fourInnerArguments R i) ^ n)) =
      if d 0 = x ∧ d 1 = y ∧ d 3 ≤ b ∧ d 2 = a + (b - d 3)
      then (d 2).choose a else 0 := by
  classical
  let B : MvPowerSeries (Fin 3) R :=
    (SupportedThreeFieldCollision.index3 (d 1) (d 2) (d 3)).prod
      (fun i n => (SupportedThreeFieldCollision.innerArguments R i) ^ n)
  have B_eq : B = MvPowerSeries.X 0 ^ (d 1) *
      (MvPowerSeries.X 1 + MvPowerSeries.X 2) ^ (d 2) *
        (MvPowerSeries.X 2) ^ (d 3) := by
    dsimp only [B]
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _)]
    · simp [Fin.prod_univ_succ, SupportedThreeFieldCollision.innerArguments,
        SupportedThreeFieldCollision.index3, mul_comm, mul_left_comm, mul_assoc]
    · intro i hi; simp
  have prod_eq : d.prod (fun i n => (fourInnerArguments R i) ^ n) =
      MvPowerSeries.rename tailLabel B *
        MvPowerSeries.monomial (Finsupp.single 0 (d 0)) 1 := by
    rw [Finsupp.prod_of_support_subset d (Finset.subset_univ d.support)]
    · rw [B_eq]
      simp [Fin.prod_univ_succ, fourInnerArguments, tailLabel,
        ← MvPowerSeries.X_pow_eq, mul_comm, mul_left_comm, mul_assoc] <;> ring
    · intro i hi; simp
  rw [prod_eq, MvPowerSeries.coeff_mul_monomial]
  have le_iff : Finsupp.single 0 (d 0) ≤ index4 x y a b ↔ d 0 ≤ x := by
    constructor
    · intro h; simpa [index4] using h 0
    · intro h i; fin_cases i <;> simp [index4, h]
  simp only [le_iff]
  by_cases hx : d 0 ≤ x
  · rw [ite_eq_left hx, mul_one]
    have sub : index4 x y a b - Finsupp.single 0 (d 0) = index4 (x - d 0) y a b := by
      ext i
      fin_cases i <;> simp [index4, Finsupp.tsub_apply]
    rw [sub]
    by_cases he : d 0 = x
    · subst x
      rw [Nat.sub_self, index4_tail, MvPowerSeries.coeff_embDomain_rename]
      dsimp only [B]
      rw [inner_monomial_coeff]
      simp [SupportedThreeFieldCollision.index3]
    · have outside : index4 (x - d 0) y a b ∉
          Set.range (Finsupp.mapDomain (tailLabel : Fin 3 → Fin 4)) := by
        rintro ⟨u, hu⟩
        have hz : u.mapDomain (tailLabel : Fin 3 → Fin 4) 0 = 0 := by
          apply Finsupp.mapDomain_of_notMem_range
          rintro ⟨i, hi⟩
          fin_cases i <;> simp [tailLabel] at hi
        have h0 := congrArg (fun z : Fin 4 →₀ ℕ => z 0) hu
        simp only [hz] at h0
        simp [index4] at h0
        omega
      rw [MvPowerSeries.coeff_rename_eq_zero tailLabel B outside]
      simp [he]
  · rw [ite_eq_right hx]
    have he : d 0 ≠ x := by omega
    simp [he]

/-- The finite native coefficient fiber preserves both original spectator labels. -/
theorem fourInnerCollision_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (x y a b : ℕ) :
    MvPowerSeries.coeff (index4 x y a b) (fourInnerCollision P) =
      ∑ j ∈ Finset.range (b + 1), ((a + j).choose a : ℂ) •
        MvPowerSeries.coeff (index4 x y (a + j) (b - j)) P := by
  classical
  rw [fourInnerCollision, MvPowerSeries.coeff_subst (fourInner_hasSubst R)]
  let indices := (Finset.range (b + 1)).image (fun j => index4 x y (a + j) (b - j))
  rw [finsum_eq_sum_of_support_subset (s := indices)]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      have hjb : j ≤ b := by simpa using Finset.mem_range.mp hj
      rw [four_monomial_coeff]
      have cond : (index4 x y (a + j) (b - j)) 0 = x ∧
          (index4 x y (a + j) (b - j)) 1 = y ∧
          (index4 x y (a + j) (b - j)) 3 ≤ b ∧
          (index4 x y (a + j) (b - j)) 2 =
            a + (b - (index4 x y (a + j) (b - j)) 3) := by
        simp [index4, Nat.sub_sub_self hjb]
      rw [ite_eq_left cond]
      simp [index4, Algebra.smul_def, smul_eq_mul, map_natCast, mul_comm]
    · intro i hi j hj h
      have h2 := congrArg (fun d : Fin 4 →₀ ℕ => d 2) h
      simp [index4] at h2
      omega
  · intro d hd
    rw [Function.mem_support, ne_eq] at hd
    have conditions : d 0 = x ∧ d 1 = y ∧ d 3 ≤ b ∧ d 2 = a + (b - d 3) := by
      by_contra h
      apply hd
      rw [four_monomial_coeff, ite_eq_right h, Nat.cast_zero, smul_zero]
    refine Finset.mem_image.mpr ⟨b - d 3, Finset.mem_range.mpr (by omega), ?_⟩
    ext i
    fin_cases i
    · simpa [index4] using conditions.1.symm
    · simpa [index4] using conditions.2.1.symm
    · simpa [index4] using conditions.2.2.2.symm
    · simpa [index4] using Nat.sub_sub_self conditions.2.2.1

/-- A bivariate slice of the same P, zero in either negative spectator region. -/
def slice {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (x y : ℤ) : MvPowerSeries (Fin 2) R :=
  fun d => signedExtend P ![x, y, (d 0 : ℤ), (d 1 : ℤ)]

theorem slice_extend {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (x y a b : ℤ) :
    extend (slice P x y) a b = signedExtend P ![x,y,a,b] := by
  classical
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [extend, ite_eq_left ⟨ha,hb⟩]
      simp only [MvPowerSeries.coeff_apply, slice, powerIndex, Finsupp.add_apply,
        Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_add, add_zero,
        Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
    · have h : ¬ ∀ i : Fin 4, 0 ≤ (![x,y,a,b] : Fin 4 → ℤ) i := by
        intro h; exact hb (h 3)
      simp [extend, signedExtend, hb, h]
  · have h : ¬ ∀ i : Fin 4, 0 ≤ (![x,y,a,b] : Fin 4 → ℤ) i := by
      intro h; exact ha (h 2)
    simp [extend, signedExtend, ha, h]

/-- Signed guards include both spectator coordinates separately. -/
theorem fourInnerCollision_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (x y a b : ℤ) :
    signedExtend (fourInnerCollision P) ![x,y,a,b] =
      extend (collision (slice P x y)) a b := by
  classical
  by_cases hxy : 0 ≤ x ∧ 0 ≤ y
  · by_cases ha : 0 ≤ a
    · by_cases hb : 0 ≤ b
      · have h : ∀ i : Fin 4, 0 ≤ (![x,y,a,b] : Fin 4 → ℤ) i := by
          intro i; fin_cases i <;> simp_all
        have idx : signedIndex (![x,y,a,b] : Fin 4 → ℤ) =
            index4 x.toNat y.toNat a.toNat b.toNat := by
          ext i
          fin_cases i <;> simp [signedIndex, index4]
        rw [signedExtend, ite_eq_left h, idx]
        change MvPowerSeries.coeff (index4 x.toNat y.toNat a.toNat b.toNat)
          (fourInnerCollision P) = _
        rw [fourInnerCollision_coeff, extend, ite_eq_left ⟨ha,hb⟩, collision_coeff]
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        simp only [MvPowerSeries.coeff_apply, slice, powerIndex, Finsupp.add_apply,
          Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
          Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add]
        change P (index4 x.toNat y.toNat (a.toNat + j) (b.toNat - j)) =
          signedExtend P ![x,y,(a.toNat + j : ℕ),(b.toNat - j : ℕ)]
        have hn : ∀ i : Fin 4,
            0 ≤ (![x,y,((a.toNat + j : ℕ) : ℤ),((b.toNat - j : ℕ) : ℤ)] : Fin 4 → ℤ) i := by
          intro i
          fin_cases i
          · exact hxy.1
          · exact hxy.2
          · exact Int.natCast_nonneg _
          · exact Int.natCast_nonneg _
        rw [signedExtend, ite_eq_left hn]
        congr 1
        ext i
        fin_cases i <;> simp [index4,signedIndex] <;> omega
      · have h : ¬ ∀ i : Fin 4, 0 ≤ (![x,y,a,b] : Fin 4 → ℤ) i := by
          intro h; exact hb (h 3)
        simp [signedExtend, extend, hb, h]
    · have h : ¬ ∀ i : Fin 4, 0 ≤ (![x,y,a,b] : Fin 4 → ℤ) i := by
        intro h; exact ha (h 2)
      simp [signedExtend, extend, ha, h]
  · have hs : slice P x y = 0 := by
      funext d
      have h : ¬ ∀ i : Fin 4,
          0 ≤ (![x,y,(d 0 : ℤ),(d 1 : ℤ)] : Fin 4 → ℤ) i := by
        intro h; exact hxy ⟨h 0,h 1⟩
      change signedExtend P ![x,y,(d 0 : ℤ),(d 1 : ℤ)] = 0
      simp [signedExtend,h]
    have h : ¬ ∀ i : Fin 4, 0 ≤ (![x,y,a,b] : Fin 4 → ℤ) i := by
      intro h; exact hxy ⟨h 0,h 1⟩
    have hz : collision (0 : MvPowerSeries (Fin 2) R) = 0 := by
      ext d
      have hd : d = powerIndex (d 0) (d 1) := by
        ext i
        fin_cases i <;> simp [powerIndex]
      rw [hd,collision_coeff]
      simp
    simp [signedExtend,h,hs,hz,extend]

end
end D5.S3.VertexAlgebra.SupportedFourFieldCollision
