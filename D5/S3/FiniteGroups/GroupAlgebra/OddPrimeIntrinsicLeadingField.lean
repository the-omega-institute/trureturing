/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingField
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeIntrinsicLeadingField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Algebra.Subalgebra.Lattice, mathlib/module/Mathlib.LinearAlgebra.Dimension.Free, mathlib/module/Mathlib.RingTheory.SimpleModule.Rank]
   utility: none
   digest: Two evaluation injections force the intrinsic commuting leading algebra to be a field. -/

/-!
For an actual odd-prime representation satisfying cyclic projectivity and
independent ordered mixed vanishing, the intrinsic leading action acts on the
existing coinvariants. Evaluation on a common invariant subspace and its
quotient gives two rank bounds. Their minimum contradicts the strict threshold.
The resulting simple faithful action of the actual commutative adjoin makes
that algebra a degree-m field, with an evaluation equivalence to the coinvariants.
-/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeIntrinsicLeadingAction
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.SimpleModule.Rank

set_option autoImplicit false

noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeIntrinsicLeadingField

open scoped MonoidAlgebra IsMulCommutative
universe uK uV uU

private abbrev EAdd (p r : ℕ) := Fin r → ZMod p
private abbrev E (p r : ℕ) := Multiplicative (EAdd p r)

variable {p r m : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type uK} [Field K] [Finite K] [CharP K p]

local instance primeFieldAlgebra : Algebra (ZMod p) K := ZMod.algebra K p

/- The same restricted scalar structure as in the intrinsic output. -/
local instance primeEndModule (U : Type uU) [AddCommGroup U] [Module K U] :
    Module (ZMod p) (Module.End K U) :=
  Module.compHom _ (algebraMap (ZMod p) K)

/- Private and live-consumed by intrinsic_leading_field. Neither a coefficient
model nor irreducibility is an input to the final arbitrary-rho theorem. -/
private theorem invariant_subspace_eq_bot_or_top
    {U : Type uU} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (A : EAdd p r →ₗ[ZMod p] Module.End K U)
    (hunit : ∀ g, g ≠ 0 → IsUnit (A g))
    (hdim : Module.finrank K U = m)
    (hbound : Module.finrank (ZMod p) K * (m / 2) < r)
    (W : Submodule K U)
    (hW : ∀ g x, x ∈ W → A g x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra htriv
  have hWbot : W ≠ ⊥ := fun he => htriv (Or.inl he)
  have hWtop : W ≠ ⊤ := fun he => htriv (Or.inr he)
  obtain ⟨w, hwW, hw0⟩ := W.ne_bot_iff.mp hWbot
  obtain ⟨u, huW⟩ : ∃ u : U, u ∉ W := by
    by_contra hn
    push_neg at hn
    exact hWtop (top_unique (fun x _ => hn x))
  let w₀ : W := ⟨w, hwW⟩
  have hw₀ : w₀ ≠ 0 := fun he => hw0 (congrArg Subtype.val he)
  let q₀ : U ⧸ W := W.mkQ u
  have hq₀ : q₀ ≠ 0 := by
    intro he
    exact huW (Submodule.Quotient.mk_eq_zero.mp he)

  let B (g : EAdd p r) : Module.End K W := (A g).restrict (hW g)
  have hAinj (g : EAdd p r) (hg : g ≠ 0) : Function.Injective (A g) :=
    LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp (hunit g hg))
  have hBinj (g : EAdd p r) (hg : g ≠ 0) : Function.Injective (B g) := by
    intro x y he
    apply Subtype.ext
    exact hAinj g hg (congrArg Subtype.val he)
  /- Essential finite-dimensional step: forward invariance alone is insufficient
  for the quotient injection. Prove onto on W and actual equality A(g)W=W. -/
  have hBsurj (g : EAdd p r) (hg : g ≠ 0) : Function.Surjective (B g) :=
    LinearMap.injective_iff_surjective.mp (hBinj g hg)
  have hAW (g : EAdd p r) (hg : g ≠ 0) : W.map (A g) = W := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hW g y hy
    · intro x hx
      obtain ⟨y, hy⟩ := hBsurj g hg ⟨x, hx⟩
      exact ⟨y, y.property, congrArg Subtype.val hy⟩

  let Q (g : EAdd p r) : Module.End K (U ⧸ W) :=
    W.mapQ W (A g) (hW g)
  have hQzero (g : EAdd p r) (hg : g ≠ 0) (x : U ⧸ W)
      (hx : Q g x = 0) : x = 0 := by
    obtain ⟨v, rfl⟩ := W.mkQ_surjective x
    have hAv : A g v ∈ W := Submodule.Quotient.mk_eq_zero.mp hx
    /- Equality, hence a preimage in W, is used on the live proof path. -/
    have hAv' : A g v ∈ W.map (A g) := by rw [hAW g hg]; exact hAv
    obtain ⟨w', hw', he⟩ := hAv'
    have hwv : w' = v := hAinj g hg he
    exact Submodule.Quotient.mk_eq_zero.mpr (hwv ▸ hw')
  have hQinj (g : EAdd p r) (hg : g ≠ 0) : Function.Injective (Q g) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hQzero g hg
    rw [map_sub, hxy, sub_self]
  /- Explicitly record invertibility on U/W, derived after A(g)W=W. -/
  have hQunit (g : EAdd p r) (hg : g ≠ 0) : IsUnit (Q g) :=
    (LinearMap.isUnit_iff_ker_eq_bot _).mpr (LinearMap.ker_eq_bot.mpr (hQinj g hg))

  letI : Module (ZMod p) W := Module.compHom W (algebraMap (ZMod p) K)
  letI : Module (ZMod p) (U ⧸ W) := Module.compHom (U ⧸ W) (algebraMap (ZMod p) K)
  letI : FiniteDimensional (ZMod p) K := inferInstance
  letI : FiniteDimensional (ZMod p) W := FiniteDimensional.trans (ZMod p) K W
  letI : FiniteDimensional (ZMod p) (U ⧸ W) :=
    FiniteDimensional.trans (ZMod p) K (U ⧸ W)

  /- First Fp-linear injection: evaluate on a nonzero vector of W. -/
  let evalWAdd : EAdd p r →+ W :=
    { toFun := fun g => B g w₀
      map_zero' := by
        apply Subtype.ext
        change (A 0) w = 0
        simp only [map_zero, LinearMap.zero_apply]
      map_add' := by
        intro g k
        apply Subtype.ext
        change (A (g + k)) w = (A g) w + (A k) w
        simp only [map_add, LinearMap.add_apply] }
  let evalW : EAdd p r →ₗ[ZMod p] W := evalWAdd.toZModLinearMap p
  have hevalWzero (g : EAdd p r) (he : evalW g = 0) : g = 0 := by
    by_contra hg
    apply hw₀
    apply hBinj g hg
    exact he.trans (map_zero (B g)).symm
  have hevalWinj : Function.Injective evalW := by
    intro g k he
    apply sub_eq_zero.mp
    apply hevalWzero
    rw [map_sub, he, sub_self]
  have hrW : r ≤ Module.finrank (ZMod p) W := by
    simpa only [EAdd, Module.finrank_pi, Fintype.card_fin] using
      (LinearMap.finrank_le_finrank_of_injective hevalWinj)
  have hrW' : r ≤ Module.finrank (ZMod p) K * Module.finrank K W := by
    rw [Module.finrank_mul_finrank (ZMod p) K W]
    exact hrW

  /- Second Fp-linear injection: evaluation at a nonzero QUOTIENT class. -/
  let evalQAdd : EAdd p r →+ (U ⧸ W) :=
    { toFun := fun g => Q g q₀
      map_zero' := by
        change W.mkQ ((A 0) u) = 0
        simp only [map_zero, LinearMap.zero_apply]
      map_add' := by
        intro g k
        change W.mkQ ((A (g + k)) u) = W.mkQ ((A g) u) + W.mkQ ((A k) u)
        simp only [map_add, LinearMap.add_apply] }
  let evalQ : EAdd p r →ₗ[ZMod p] (U ⧸ W) := evalQAdd.toZModLinearMap p
  have hevalQzero (g : EAdd p r) (he : evalQ g = 0) : g = 0 := by
    by_contra hg
    have hi : Function.Injective (Q g) :=
      LinearMap.ker_eq_bot.mp ((LinearMap.isUnit_iff_ker_eq_bot _).mp (hQunit g hg))
    apply hq₀
    apply hi
    exact he.trans (map_zero (Q g)).symm
  have hevalQinj : Function.Injective evalQ := by
    intro g k he
    apply sub_eq_zero.mp
    apply hevalQzero
    rw [map_sub, he, sub_self]
  have hrQ : r ≤ Module.finrank (ZMod p) (U ⧸ W) := by
    simpa only [EAdd, Module.finrank_pi, Fintype.card_fin] using
      (LinearMap.finrank_le_finrank_of_injective hevalQinj)
  have hrQ' : r ≤ Module.finrank (ZMod p) K * Module.finrank K (U ⧸ W) := by
    rw [Module.finrank_mul_finrank (ZMod p) K (U ⧸ W)]
    exact hrQ

  let d := Module.finrank K W
  have hqd : Module.finrank K (U ⧸ W) + d = m := by
    simpa only [d, hdim] using W.finrank_quotient_add_finrank
  have hqdim : Module.finrank K (U ⧸ W) = m - d := by omega
  have hrmd : r ≤ Module.finrank (ZMod p) K * (m - d) := by
    simpa only [hqdim] using hrQ'
  have hmin : min d (m - d) ≤ m / 2 := by omega
  have hrmin : r ≤ Module.finrank (ZMod p) K * min d (m - d) := by
    rcases le_total d (m - d) with hd | hd
    · simpa only [min_eq_left hd, d] using hrW'
    · simpa only [min_eq_right hd] using hrmd
  exact (not_le_of_gt hbound)
    (hrmin.trans (Nat.mul_le_mul_left _ hmin))

variable {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- For every actual rho and every nonidentity anchor,
the strict rank bound forces its intrinsic first-layer adjoin to be a degree-m
field acting on the existing coinvariants by evaluation. -/
theorem intrinsic_leading_field
    (rho : Representation K (E p r) V)
    (hr : 0 < r) (hm : 0 < m) (hV : Module.finrank K V = p * m)
    (hproj : ∀ H : Subgroup (E p r), IsCyclic H →
      Module.Projective K[H] (rho.comp H.subtype).asModule)
    (hmixed : ∀ xs : List (EAdd p r), xs.length = p →
      (xs.map (fun g => rho (Multiplicative.ofAdd g) - 1)).prod = 0)
    (h : E p r) (hh : h ≠ 1)
    (hbound : Module.finrank (ZMod p) K * (m / 2) < r) :
    ∃ A : EAdd p r →ₗ[ZMod p] Module.End K (Representation.Coinvariants rho),
      Module.finrank K (Representation.Coinvariants rho) = m ∧
      A h.toAdd = 1 ∧
      (∀ g, g ≠ 0 → IsUnit (A g)) ∧
      (∀ g k, Commute (A g) (A k)) ∧
      (∀ g v w,
        A g (Representation.Coinvariants.mk rho v) = Representation.Coinvariants.mk rho w ↔
          (rho (Multiplicative.ofAdd g) - 1) v - (rho h - 1) w ∈
            LinearMap.range ((rho h - 1) ^ 2)) ∧
      (∀ W : Submodule K (Representation.Coinvariants rho),
        (∀ g x, x ∈ W → A g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      (let C := Algebra.adjoin K (Set.range A)
       IsField C ∧ Module.finrank K C = m ∧
         ∃ u : Representation.Coinvariants rho, u ≠ 0 ∧
           ∃ e : C ≃ₗ[K] Representation.Coinvariants rho,
             ∀ c : C, e c = (c : Module.End K (Representation.Coinvariants rho)) u) := by
  classical
  /- Intrinsic leading action on the existing coinvariants. -/
  obtain ⟨A, hdim, hAh, hunit, hcomm, hcert⟩ :=
    OddPrimeIntrinsicLeadingAction.intrinsic_leading_action rho hr hm hV hproj hmixed h hh
  let U := Representation.Coinvariants rho
  letI : Nontrivial U := Module.nontrivial_of_finrank_pos (hdim.symm ▸ hm)
  have hirr (W : Submodule K U) (hW : ∀ g x, x ∈ W → A g x ∈ W) :
      W = ⊥ ∨ W = ⊤ :=
    invariant_subspace_eq_bot_or_top A hunit hdim hbound W hW
  refine ⟨A, hdim, hAh, hunit, hcomm, hcert, hirr, ?_⟩
  let C := Algebra.adjoin K (Set.range A)
  change IsField C ∧ Module.finrank K C = m ∧ _
  letI : IsMulCommutative C := Algebra.isMulCommutative_adjoin K (by
    rintro _ ⟨g, rfl⟩ _ ⟨k, rfl⟩ _
    exact hcomm g k)
  /- Existing evaluation action, restricted through the actual inclusion of C. -/
  letI : Module C U := Module.compHom U C.val.toRingHom
  letI : IsScalarTower K C U := ⟨fun _ _ _ => rfl⟩
  letI : FaithfulSMul C U :=
    { eq_of_smul_eq_smul := by
        intro c d hcd
        apply Subtype.ext
        exact eq_of_smul_eq_smul (M := Module.End K U) hcd }
  letI : IsSimpleModule C U :=
    { eq_bot_or_eq_top := by
        intro S
        have hinv (g : EAdd p r) (x : U) (hx : x ∈ S.restrictScalars K) :
            A g x ∈ S.restrictScalars K := by
          let c : C := ⟨A g, Algebra.subset_adjoin (Set.mem_range_self g)⟩
          exact S.smul_mem c hx
        rcases hirr (S.restrictScalars K) hinv with hb | ht
        · exact Or.inl ((Submodule.restrictScalars_eq_bot_iff K).mp hb)
        · exact Or.inr ((Submodule.restrictScalars_eq_top_iff K).mp ht) }
  have hC : IsField C := Ring.isField_iff_maximal_bot.mpr (by
    have hmax := IsSimpleModule.annihilator_isMaximal (R := C) (M := U)
    have hann : Module.annihilator C U = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
    rwa [hann] at hmax)
  /- Local use of the existing IsField conversion; no custom field-data wrapper. -/
  letI : Field C := hC.toField
  have hline : Module.finrank C U = 1 := isSimpleModule_iff_finrank_eq_one.mp inferInstance
  have hdegree : Module.finrank K C = m := by
    have htower := Module.finrank_mul_finrank K C U
    simpa only [hline, mul_one, hdim] using htower
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  let ev : C →ₗ[K] U :=
    (LinearMap.applyₗ (R := K) (M := U) (M₂ := U) u).comp C.val.toLinearMap
  have hevinj : Function.Injective ev := by
    have hi := LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton C hu)
    exact hi
  have hevsurj : Function.Surjective ev := IsSimpleModule.toSpanSingleton_surjective C hu
  let e : C ≃ₗ[K] U := LinearEquiv.ofBijective ev ⟨hevinj, hevsurj⟩
  exact ⟨hC, hdegree, u, hu, e, fun _ => rfl⟩

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeIntrinsicLeadingField
