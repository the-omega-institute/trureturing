/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootKernels
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootKernels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnTorusAlignment
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-! Actual diagonal-character kernels intrinsically recognize EVERY positive
root of full SLn. The field-size bound is proved by genuine unit separation;
the accepted rank3 torus-kernel argument is generalized, not assumed. -/
namespace NikolovSegal.SLnRootAction
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "T" => diagonalTorus n F

abbrev PositiveIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

def root (r : PositiveIndex n) (t : F) : G :=
  SpecialLinearGroup.transvection (ne_of_lt r.property) t

theorem root_injective (r : PositiveIndex n) : Function.Injective (root (F := F) r) := by
  intro t s h
  have he := congrArg (fun g : G => g.val r.val.1 r.val.2) h
  simpa [root, SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    ne_of_lt r.property] using he

def rootSubgroup (r : PositiveIndex n) : Subgroup G where
  carrier := {g | ∃ t : F, root r t = g}
  one_mem' := ⟨0, SpecialLinearGroup.transvection_coeff_zero _⟩
  mul_mem' := by
    rintro g h ⟨t,rfl⟩ ⟨s,rfl⟩
    exact ⟨t+s, SpecialLinearGroup.transvection_add _ t s⟩
  inv_mem' := by
    rintro g ⟨t,rfl⟩
    exact ⟨-t,(SpecialLinearGroup.transvection_inv _ t).symm⟩

theorem root_mem_Uplus (r : PositiveIndex n) (t : F) : root r t ∈ Uplus n F :=
  transvection_mem_Uplus r.property t

theorem card_rootSubgroup (r : PositiveIndex n) : Nat.card (rootSubgroup (F := F) r) = Nat.card F := by
  let f : F → rootSubgroup (F := F) r := fun t => ⟨root r t,t,rfl⟩
  have hi : Function.Injective f := fun _ _ h => root_injective r (congrArg Subtype.val h)
  have hs : Function.Surjective f := by rintro ⟨g,t,rfl⟩; exact ⟨t,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm

noncomputable def rootCharacter (r : PositiveIndex n) : T →* Fˣ where
  toFun t := torusDiagonalUnits t r.val.1 / torusDiagonalUnits t r.val.2
  map_one' := by simp
  map_mul' t s := by
    simp only [map_mul, Pi.mul_apply, div_eq_mul_inv, _root_.mul_inv_rev]
    ac_rfl

noncomputable def torusKernel (r : PositiveIndex n) : Subgroup G :=
  (rootCharacter (F := F) r).ker.map (T).subtype

theorem mem_torusKernel_iff (r : PositiveIndex n) (g : G) :
    g ∈ torusKernel r ↔ g ∈ T ∧ g.val r.val.1 r.val.1 = g.val r.val.2 r.val.2 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    change torusDiagonalUnits t r.val.1 / torusDiagonalUnits t r.val.2 = 1 at ht
    refine ⟨t.property, ?_⟩
    have he : torusDiagonalUnits t r.val.1 = torusDiagonalUnits t r.val.2 := by
      simpa using congrArg (fun x : Fˣ => x * torusDiagonalUnits t r.val.2) ht
    exact congrArg (fun x : Fˣ => (x:F)) he
  · rintro ⟨hg, hd⟩
    refine ⟨⟨g,hg⟩, ?_, rfl⟩
    change torusDiagonalUnits ⟨g,hg⟩ r.val.1 / torusDiagonalUnits ⟨g,hg⟩ r.val.2 = 1
    have he : torusDiagonalUnits ⟨g,hg⟩ r.val.1 = torusDiagonalUnits ⟨g,hg⟩ r.val.2 := Units.ext hd
    rw [he]
    simp

theorem rootCharacter_surjective (hn : 2 < n) (r : PositiveIndex n) :
    Function.Surjective (rootCharacter (F := F) r) := by
  classical
  obtain ⟨k,hki,hkj⟩ := Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 hn
  intro z
  let d := SpecialLinearGroup.diag2n hki.symm (z:F) z.ne_zero
  have ht : d ∈ T := diagonal_of_eq _ _ rfl
  refine ⟨⟨d,ht⟩, ?_⟩
  apply Units.ext
  simp [rootCharacter, torusDiagonalUnits, d, SpecialLinearGroup.diag2n_coe,
    hki, hkj, hkj.symm, (ne_of_lt r.property).symm, Units.val_inv_eq_inv_val]

/-- Actual kernel orders agree in every rank at least3. The order is
derived from the surjective actual diagonal character, not a premise. -/
theorem card_torusKernel_mul_units [Finite F] (hn : 2 < n) (r : PositiveIndex n) :
    Nat.card (torusKernel (F := F) r) * Nat.card Fˣ = Nat.card T := by
  have hc : Nat.card (torusKernel (F := F) r) = Nat.card (rootCharacter (F := F) r).ker :=
    (Nat.card_congr ((rootCharacter (F := F) r).ker.equivMapOfInjective
      (T).subtype Subtype.val_injective).toEquiv).symm
  have hi : (rootCharacter (F := F) r).ker.index = Nat.card Fˣ := by
    rw [Subgroup.index_ker, (rootCharacter r).range_eq_top_of_surjective (rootCharacter_surjective hn r),
      Subgroup.card_top]
  rw [hc, ← hi]
  exact (rootCharacter r).ker.card_mul_index

theorem card_torusKernel_eq [Finite F] (hn : 2 < n) (r s : PositiveIndex n) :
    Nat.card (torusKernel (F := F) r) = Nat.card (torusKernel (F := F) s) := by
  apply (mul_left_inj' (Nat.card_pos (α := Fˣ)).ne').mp
  exact (card_torusKernel_mul_units hn r).trans (card_torusKernel_mul_units hn s).symm

private theorem exists_unit_power_ne_one [Fintype F] (hF : 4 < Fintype.card F)
    (k : ℕ) (hk : 0 < k) (hk3 : k ≤ 3) : ∃ x : Fˣ, (x:F)^k ≠ 1 := by
  classical
  have he : ∃ x : Fˣ, x^k ≠ 1 := exists_pow_ne_one_of_isCyclic hk.ne'
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units]; omega)
  obtain ⟨x,hx⟩ := he
  exact ⟨x,fun h => hx (Units.ext h)⟩

private theorem cube_difference (x : Fˣ) (hx : (x:F)^3 ≠ 1) :
    (x:F) ≠ (x:F)⁻¹*(x:F)⁻¹ := by
  intro h
  apply hx
  calc
    (x:F)^3 = (x:F)*((x:F)*(x:F)) := by ring
    _ = ((x:F)⁻¹*(x:F)⁻¹)*((x:F)*(x:F)) := congrArg (fun a : F => a*((x:F)*(x:F))) h
    _ = 1 := by field_simp

private theorem square_difference (x : Fˣ) (hx : (x:F)^2 ≠ 1) :
    (x:F) ≠ (x:F)⁻¹ := by
  intro h
  apply hx
  calc
    (x:F)^2 = (x:F)*(x:F) := pow_two _
    _ = (x:F)⁻¹*(x:F) := congrArg (fun a : F => a*(x:F)) h
    _ = 1 := inv_mul_cancel₀ x.ne_zero

private noncomputable def balancedDiagonal (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (x : Fˣ) : G :=
  SpecialLinearGroup.diag2n hik (x:F) x.ne_zero * SpecialLinearGroup.diag2n hjk (x:F) x.ne_zero

private theorem balancedDiagonal_mem (r : PositiveIndex n) (k : Fin n)
    (hki : k ≠ r.val.1) (hkj : k ≠ r.val.2) (x : Fˣ) :
    balancedDiagonal r.val.1 r.val.2 k hki.symm hkj.symm x ∈ torusKernel r := by
  apply (mem_torusKernel_iff r _).mpr
  have h1 : SpecialLinearGroup.diag2n hki.symm (x:F) x.ne_zero ∈ T := diagonal_of_eq _ _ rfl
  have h2 : SpecialLinearGroup.diag2n hkj.symm (x:F) x.ne_zero ∈ T := diagonal_of_eq _ _ rfl
  refine ⟨(T).mul_mem h1 h2, ?_⟩
  dsimp only [balancedDiagonal]
  rw [upper_mul_diag (diagonalTorus_le_Borel h1) (diagonalTorus_le_Borel h2)]
  rw [upper_mul_diag (diagonalTorus_le_Borel h1) (diagonalTorus_le_Borel h2)]
  simp [SpecialLinearGroup.diag2n_coe, hki.symm, hkj.symm, (ne_of_lt r.property), (ne_of_lt r.property).symm]

private theorem balancedDiagonal_entry (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (x : Fˣ) (t : Fin n) :
    (balancedDiagonal i j k hik hjk x).val t t =
      (if t=i then (x:F) else if t=k then (x:F)⁻¹ else 1) *
      (if t=j then (x:F) else if t=k then (x:F)⁻¹ else 1) := by
  dsimp only [balancedDiagonal]
  simpa only [SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply_eq] using upper_mul_diag
    (diagonalTorus_le_Borel (diagonal_of_eq (SpecialLinearGroup.diag2n hik (x:F) x.ne_zero) _ rfl))
    (diagonalTorus_le_Borel (diagonal_of_eq (SpecialLinearGroup.diag2n hjk (x:F) x.ne_zero) _ rfl)) t

/-- A genuine determinant-one diagonal element separates every unwanted
positive entry while equating the two selected diagonal positions. -/
theorem torusKernel_separates [Fintype F] (hF : 4 < Fintype.card F)
    (r s : PositiveIndex n) (hrs : s ≠ r) :
    ∃ d ∈ torusKernel (F := F) r, d.val s.val.1 s.val.1 ≠ d.val s.val.2 s.val.2 := by
  classical
  let i := r.val.1
  let j := r.val.2
  let a := s.val.1
  let b := s.val.2
  have hij : i < j := r.property
  have hab : a < b := s.property
  by_cases ha : a = i ∨ a = j
  · by_cases hb : b = i ∨ b = j
    · exfalso
      apply hrs
      rcases ha with ha|ha <;> rcases hb with hb|hb
      · rw [ha,hb] at hab; exact (lt_irrefl _ hab).elim
      · exact Subtype.ext (Prod.ext ha hb)
      · rw [ha,hb] at hab; exact (lt_asymm hij hab).elim
      · rw [ha,hb] at hab; exact (lt_irrefl _ hab).elim
    · have hbi : b ≠ i := fun h => hb (Or.inl h)
      have hbj : b ≠ j := fun h => hb (Or.inr h)
      obtain ⟨x,hx⟩ := exists_unit_power_ne_one hF 3 (by decide) (by decide)
      let d := balancedDiagonal i j b hbi.symm hbj.symm x
      refine ⟨d, balancedDiagonal_mem r b hbi hbj x, ?_⟩
      have he : ∀ t, d.val t t =
          (if t=i then (x:F) else if t=b then (x:F)⁻¹ else 1) *
          (if t=j then (x:F) else if t=b then (x:F)⁻¹ else 1) := by
        intro t
        exact balancedDiagonal_entry _ _ _ _ _ x t
      change d.val a a ≠ d.val b b
      rw [he a, he b]
      rcases ha with ha|ha
      · simpa [ha, hbi, hbj, hbi.symm, hbj.symm, ne_of_lt hij, (ne_of_lt hij).symm] using cube_difference x hx
      · simpa [ha, hbi, hbj, hbi.symm, hbj.symm, ne_of_lt hij, (ne_of_lt hij).symm] using cube_difference x hx
  · have hai : a ≠ i := fun h => ha (Or.inl h)
    have haj : a ≠ j := fun h => ha (Or.inr h)
    by_cases hb : b = i ∨ b = j
    · obtain ⟨x,hx⟩ := exists_unit_power_ne_one hF 3 (by decide) (by decide)
      let d := balancedDiagonal i j a hai.symm haj.symm x
      refine ⟨d, balancedDiagonal_mem r a hai haj x, ?_⟩
      have he : ∀ t, d.val t t =
          (if t=i then (x:F) else if t=a then (x:F)⁻¹ else 1) *
          (if t=j then (x:F) else if t=a then (x:F)⁻¹ else 1) := by
        intro t
        exact balancedDiagonal_entry _ _ _ _ _ x t
      change d.val a a ≠ d.val b b
      rw [he a, he b]
      rcases hb with hb|hb
      · simpa [hb, hai, haj, hai.symm, haj.symm, ne_of_lt hij, (ne_of_lt hij).symm] using (cube_difference x hx).symm
      · simpa [hb, hai, haj, hai.symm, haj.symm, ne_of_lt hij, (ne_of_lt hij).symm] using (cube_difference x hx).symm
    · have hbi : b ≠ i := fun h => hb (Or.inl h)
      have hbj : b ≠ j := fun h => hb (Or.inr h)
      obtain ⟨x,hx⟩ := exists_unit_power_ne_one hF 2 (by decide) (by decide)
      let d := SpecialLinearGroup.diag2n (ne_of_lt hab) (x:F) x.ne_zero
      have ht : d ∈ T := diagonal_of_eq _ _ rfl
      refine ⟨d, (mem_torusKernel_iff r d).mpr ⟨ht, ?_⟩, ?_⟩
      · change d.val i i = d.val j j
        simp [d, SpecialLinearGroup.diag2n_coe, hai.symm, haj.symm, hbi.symm, hbj.symm]
      · change d.val a a ≠ d.val b b
        simpa [d, SpecialLinearGroup.diag2n_coe, ne_of_lt hab, (ne_of_lt hab).symm] using square_difference x hx

/-- Literal diagonal commutation, at every actual matrix entry. -/
theorem diagonal_commutes_iff (d g : G) (hd : d ∈ T) :
    d*g = g*d ↔ ∀ i j : Fin n, (d.val i i - d.val j j)*g.val i j = 0 := by
  have he := diagonal_eq d hd
  constructor
  · intro h i j
    have hc := congrArg (fun x : G => x.val i j) h
    change (d.val*g.val) i j = (g.val*d.val) i j at hc
    rw [he, Matrix.diagonal_mul, Matrix.mul_diagonal] at hc
    rw [sub_mul]
    exact sub_eq_zero.mpr (by simpa [mul_comm] using hc)
  · intro h
    apply Subtype.ext
    change d.val*g.val = g.val*d.val
    rw [he]
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hc := h i j
    rw [sub_mul, sub_eq_zero] at hc
    simpa [mul_comm] using hc

/-- The whole fixed subgroup of the actual character kernel inside U is
exactly the literal positive root, in EVERY rank, for field size>4. -/
theorem fixed_torusKernel_iff [Fintype F] (hF : 4 < Fintype.card F)
    (r : PositiveIndex n) (g : G) (hg : g ∈ Uplus n F) :
    (∀ d ∈ torusKernel r, d*g = g*d) ↔ g ∈ rootSubgroup (F := F) r := by
  classical
  constructor
  · intro h
    have hz : ∀ i j : Fin n, i < j → (i,j) ≠ r.val → g.val i j = 0 := by
      intro i j hij hne
      let s : PositiveIndex n := ⟨(i,j), hij⟩
      have hsr : s ≠ r := fun he => hne (congrArg Subtype.val he)
      obtain ⟨d,hd,hsep⟩ := torusKernel_separates hF r s hsr
      have hc := (diagonal_commutes_iff d g ((mem_torusKernel_iff r d).mp hd).1).mp (h d hd) i j
      exact (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr hsep)
    refine ⟨g.val r.val.1 r.val.2, ?_⟩
    apply Subtype.ext
    ext i j
    change (1 + Matrix.single r.val.1 r.val.2 (g.val r.val.1 r.val.2) : Matrix (Fin n) (Fin n) F) i j = g.val i j
    by_cases he : i = j
    · subst j
      have hs : ¬(r.val.1=i ∧ r.val.2=i) := by
        rintro ⟨ha,hb⟩
        exact (ne_of_lt r.property) (ha.trans hb.symm)
      simp [Matrix.single_apply, hs, hg.2 i]
    · by_cases hij : i < j
      · by_cases hr : (i,j) = r.val
        · have hi : i = r.val.1 := congrArg Prod.fst hr
          have hj : j = r.val.2 := congrArg Prod.snd hr
          simp [Matrix.single_apply, Matrix.one_apply, hi, hj, ne_of_lt r.property]
        · rw [hz i j hij hr]
          have hs : ¬(r.val.1=i ∧ r.val.2=j) := by
            rintro ⟨ha,hb⟩
            exact hr (Prod.ext ha.symm hb.symm)
          simp [Matrix.single_apply, Matrix.one_apply, he, hs]
      · have hji : j.val < i.val := by
          have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
          omega
        rw [hg.1 i j hji]
        have hr : ¬ (i = r.val.1 ∧ j = r.val.2) := by rintro ⟨rfl,rfl⟩; exact hij r.property
        have hs : ¬(r.val.1=i ∧ r.val.2=j) := by
          rintro ⟨ha,hb⟩
          exact hr ⟨ha.symm,hb.symm⟩
        simp [Matrix.single_apply, Matrix.one_apply, he, hs]
  · rintro ⟨t,rfl⟩ d hd
    apply (diagonal_commutes_iff d _ ((mem_torusKernel_iff r d).mp hd).1).mpr
    intro i j
    have hdiag := ((mem_torusKernel_iff r d).mp hd).2
    change (d.val i i-d.val j j)*(1 + Matrix.single r.val.1 r.val.2 t : Matrix (Fin n) (Fin n) F) i j = 0
    by_cases he : i = j
    · subst j; simp
    · by_cases hr : i = r.val.1 ∧ j = r.val.2
      · rcases hr with ⟨rfl,rfl⟩; simp [hdiag]
      · have hs : ¬(r.val.1=i ∧ r.val.2=j) := by
          rintro ⟨ha,hb⟩
          exact hr ⟨ha.symm,hb.symm⟩
        simp [Matrix.single_apply, Matrix.one_apply, he, hs]

end NikolovSegal.SLnRootAction
