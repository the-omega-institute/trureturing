/- GID: D5/S3/Arith/CyclotomicFields/MercaQuarticField
   generality: G
   mirror-B: D5/B/S3/Arith/CyclotomicFields/MercaQuarticField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual cyclic quartic CM field fixed by the normalized Merca kernel. -/

import D5.S3.ArithUnits.MercaQuarticCharacter
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.NumberField.Norm

/-!
The field is the actual intermediate field fixed by the normalized unit kernel
inside the prime cyclotomic number field. Class numbers are not parameters of
this construction. The historical Ma--Zhang note and classical cyclotomic theory
supply its mathematical provenance.
-/

set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative Cyclotomic

namespace D5.S3.Arith.CyclotomicFields.MercaQuarticField

open NumberField NumberField.InfinitePlace IntermediateField IsCyclotomicExtension
open D5.S3.ArithUnits.MercaQuarticCharacter

/-- The ambient prime cyclotomic number field. -/
abbrev Ambient (r : ℕ) := CyclotomicField r ℚ

variable (r : ℕ) [Fact r.Prime]

instance ambient_cyclotomic : IsCyclotomicExtension {r} ℚ (Ambient r) := by
  letI : NeZero (r : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension r ℚ

instance ambient_abelian : IsAbelianGalois ℚ (Ambient r) :=
  IsCyclotomicExtension.isAbelianGalois {r} ℚ (Ambient r)

/-- The actual unit kernel transported by the cyclotomic Galois equivalence. -/
def galoisKernel (hr : r % 8 = 5) : Subgroup Gal(Ambient r/ℚ) :=
  (kernel r hr).comap (Rat.galEquivZMod r (Ambient r)).toMonoidHom

/-- The actual fixed field, viewed inside the cyclotomic extension. -/
def fixedField (hr : r % 8 = 5) : IntermediateField ℚ (Ambient r) :=
  IntermediateField.fixedField (galoisKernel r hr)

/-- The same actual intermediate field as a number-field type. -/
abbrev Field (hr : r % 8 = 5) := fixedField r hr

instance field_numberField (hr : r % 8 = 5) : NumberField (Field r hr) :=
  NumberField.of_intermediateField (fixedField r hr)

instance ambient_cyclic : IsCyclic Gal(Ambient r/ℚ) :=
  isCyclic_of_injective (Rat.galEquivZMod r (Ambient r)).toMonoidHom
    (Rat.galEquivZMod r (Ambient r)).injective

instance field_galois (hr : r % 8 = 5) : IsGalois ℚ (Field r hr) := by
  exact (IsAbelianGalois.of_algHom (fixedField r hr).val).toIsGalois

instance field_cyclic (hr : r % 8 = 5) : IsCyclic Gal(Field r hr/ℚ) :=
  isCyclic_of_surjective (AlgEquiv.restrictNormalHom (Field r hr))
    (AlgEquiv.restrictNormalHom_surjective (K₁ := Field r hr) (E := Ambient r))

private lemma degree (hr : r % 8 = 5) : Module.finrank ℚ (Field r hr) = 4 := by
  rw [finrank_eq_fixingSubgroup_index]
  change (IntermediateField.fixedField (galoisKernel r hr)).fixingSubgroup.index = 4
  rw [fixingSubgroup_fixedField, galoisKernel]
  exact ((kernel r hr).index_comap_of_surjective
    (Rat.galEquivZMod r (Ambient r)).surjective).trans
      (kernel_structure r hr).2.2.2.2.2.2.1

private theorem ambientCM (hr : r % 8 = 5) : IsCMField (Ambient r) :=
  Rat.isCMField (Ambient r) (S := {r}) ⟨r, Set.mem_singleton r, by omega⟩

private def ambientConj (hr : r % 8 = 5) : Gal(Ambient r/ℚ) := by
  letI := ambientCM r hr
  exact (IsCMField.complexConj (Ambient r)).restrictScalars ℚ

private lemma ambientConj_image (hr : r % 8 = 5) :
    Rat.galEquivZMod r (Ambient r) (ambientConj r hr) = -1 := by
  letI := ambientCM r hr
  have hs : ambientConj r hr ^ 2 = 1 := by
    ext x
    simp [ambientConj, pow_two]
  have hn : ambientConj r hr ≠ 1 := by
    intro h
    apply IsCMField.complexConj_ne_one (Ambient r)
    ext x
    exact DFunLike.congr_fun h x
  let u := Rat.galEquivZMod r (Ambient r) (ambientConj r hr)
  have hu : u ^ 2 = 1 := by
    change (Rat.galEquivZMod r (Ambient r) (ambientConj r hr)) ^ 2 = 1
    rw [← map_pow, hs, map_one]
  have hune : u ≠ 1 := by
    intro h
    exact hn ((Rat.galEquivZMod r (Ambient r)).injective (by simpa [u] using h))
  apply Units.ext
  rcases sq_eq_one_iff.mp (congrArg (fun z : (ZMod r)ˣ => (z : ZMod r)) hu) with h | h
  · exact (hune (Units.ext h)).elim
  · exact h

private lemma ambientConj_not_mem (hr : r % 8 = 5) :
    ambientConj r hr ∉ galoisKernel r hr := by
  change Rat.galEquivZMod r (Ambient r) (ambientConj r hr) ∉ kernel r hr
  rw [ambientConj_image]
  exact (kernel_structure r hr).2.2.2.2.2.2.2

instance field_totallyComplex (hr : r % 8 = 5) : IsTotallyComplex (Field r hr) where
  isComplex w := by
    letI := ambientCM r hr
    rw [← not_isReal_iff_isComplex]
    intro hw
    obtain ⟨ψ, hψ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := Field r hr) (E := Ambient r) (M := ℂ) w.embedding.toRatAlgHom
    apply ambientConj_not_mem r hr
    rw [← fixingSubgroup_fixedField (galoisKernel r hr)]
    change ambientConj r hr ∈ (fixedField r hr).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : Field r hr := ⟨x, hx⟩
    have hy : ψ x = w.embedding y := DFunLike.congr_fun hψ y
    apply ψ.injective
    change ψ (IsCMField.complexConj (Ambient r) x) = ψ x
    calc
      _ = star (ψ x) :=
        IsCMField.complexEmbedding_complexConj (Ambient r) ψ.toRingHom x
      _ = ψ x := by
        rw [hy]
        exact DFunLike.congr_fun (conjugate_embedding_eq_of_isReal hw) y

instance field_abelian (hr : r % 8 = 5) : IsAbelianGalois ℚ (Field r hr) :=
  IsAbelianGalois.of_isCyclic ℚ (Field r hr)

instance field_CM (hr : r % 8 = 5) : IsCMField (Field r hr) :=
  IsCMField.of_isAbelianGalois _

/-- Actual fixed-field semantics, cyclic quartic degree and CM real-subfield degree.
Identification of the real field with Q(sqrt(r)) is a further theorem. -/
theorem field_structure (hr : r % 8 = 5) :
    Module.finrank ℚ (Field r hr) = 4 ∧ IsCyclic Gal(Field r hr/ℚ) ∧
    IsCMField (Field r hr) ∧
    Module.finrank ℚ (NumberField.maximalRealSubfield (Field r hr)) = 2 := by
  refine ⟨degree r hr, inferInstance, inferInstance, ?_⟩
  have h := Module.finrank_mul_finrank ℚ
    (NumberField.maximalRealSubfield (Field r hr)) (Field r hr)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two
    (NumberField.maximalRealSubfield (Field r hr)) (Field r hr), degree r hr] at h
  omega

private lemma primitive_torsion (hr : r % 8 = 5) :
    ∃ ζ : Field r hr, IsPrimitiveRoot ζ (NumberField.Units.torsionOrder (Field r hr)) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : NumberField.Units.torsion (Field r hr),
      orderOf μ = NumberField.Units.torsionOrder (Field r hr) :=
    IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  exact ⟨_, hμ.map_of_injective (FaithfulSMul.algebraMap_injective
    (𝓞 (Field r hr)) (Field r hr))⟩

/-- The actual quartic field has exactly two roots of unity on the r>5 domain.
The excluded conductor five is precisely where this argument would allow r-1=4. -/
theorem torsion_order (hr : r % 8 = 5) (hr5 : 5 < r) :
    NumberField.Units.torsionOrder (Field r hr) = 2 := by
  let w := NumberField.Units.torsionOrder (Field r hr)
  obtain ⟨ζ, hζ⟩ := primitive_torsion r hr
  have hpos : 0 < w := NumberField.Units.torsionOrder_pos _
  have hwdiv : w ∣ 2 * r := by
    have h := NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
      (hζ.map_of_injective (FaithfulSMul.algebraMap_injective
        (Field r hr) (Ambient r)))
    rw [Rat.torsionOrder_eq (n := r) (K := Ambient r),
      if_neg (by rw [Nat.even_iff]; omega)] at h
    exact h
  have hrnot : ¬ r ∣ w := by
    intro hd
    have hz : IsPrimitiveRoot (ζ ^ (w / r)) r := hζ.pow hpos
      (show w = w / r * r by exact (Nat.div_mul_cancel hd).symm)
    have hle := hz.lcm_totient_le_finrank hz
      (Polynomial.cyclotomic.irreducible_rat
        (by simpa only [Nat.lcm_self] using (Fact.out : r.Prime).pos))
    rw [Nat.lcm_self, Nat.totient_prime (Fact.out : r.Prime), degree r hr] at hle
    omega
  have hw2 : w ∣ 2 :=
    ((Fact.out : r.Prime).coprime_iff_not_dvd.mpr hrnot).symm.dvd_of_dvd_mul_right hwdiv
  have h2w : 2 ∣ w :=
    NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
      (IsPrimitiveRoot.neg_one (R := Field r hr) 0 (by decide))
  exact Nat.dvd_antisymm hw2 h2w

private def fourEquiv (hr : r % 8 = 5) :
    Multiplicative (ZMod 4) ≃* Gal(Field r hr/ℚ) :=
  mulEquivOfCyclicCardEq (by
    change Nat.card (ZMod 4) = _
    rw [Nat.card_zmod, IsGalois.card_aut_eq_finrank, degree])

private lemma fourEquiv_two (hr : r % 8 = 5) :
    fourEquiv r hr (Multiplicative.ofAdd 2) =
      (IsCMField.complexConj (Field r hr)).restrictScalars ℚ := by
  let c := (IsCMField.complexConj (Field r hr)).restrictScalars ℚ
  have hc2 : c ^ 2 = 1 := by
    ext x
    simp [c, pow_two]
  have hcne : c ≠ 1 := by
    intro h
    apply IsCMField.complexConj_ne_one (Field r hr)
    ext x
    exact congrArg Subtype.val (DFunLike.congr_fun h x)
  have hz : ∀ z : Multiplicative (ZMod 4), z ^ 2 = 1 → z ≠ 1 →
      z = Multiplicative.ofAdd 2 := by decide
  have h := hz ((fourEquiv r hr).symm c)
    (by rw [← map_pow, hc2, map_one])
    (by intro h; apply hcne; exact (fourEquiv r hr).symm.injective (by simpa using h))
  exact ((fourEquiv r hr).symm_apply_eq.mp h).symm

private lemma no_antireal_unit (hr : r % 8 = 5) (hr5 : 5 < r)
    (u : (𝓞 (Field r hr))ˣ) :
    IsCMField.complexConj (Field r hr) (u : Field r hr) ≠ -(u : Field r hr) := by
  classical
  let e := fourEquiv r hr
  let σ := e (Multiplicative.ofAdd 1)
  let a : Field r hr := u
  have hsquare : σ * σ =
      (IsCMField.complexConj (Field r hr)).restrictScalars ℚ := by
    rw [← map_mul]
    exact fourEquiv_two r hr
  have hσ2 (x : Field r hr) :
      σ (σ x) = IsCMField.complexConj (Field r hr) x :=
    DFunLike.congr_fun hsquare x
  intro hanti
  have hanti' : IsCMField.complexConj (Field r hr) a = -a := hanti
  have hvalues : (∏ z : Multiplicative (ZMod 4), e z a) = (a * σ a) ^ 2 := by
    have h3 : e (Multiplicative.ofAdd 3) a = -(σ a) := by
      have heq : e (Multiplicative.ofAdd 3) = σ * (σ * σ) := by
        dsimp [σ]
        rw [← map_mul, ← map_mul]
        congr 1
      rw [heq, AlgEquiv.mul_apply, hsquare, AlgEquiv.restrictScalars_apply, hanti', map_neg]
    change (∏ j : ZMod 4, e (Multiplicative.ofAdd j) a) = _
    rw [show (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} by decide]
    simp only [Finset.prod_insert, Finset.prod_singleton,
      show (0 : ZMod 4) ∉ ({1, 2, 3} : Finset (ZMod 4)) by decide,
      show (1 : ZMod 4) ∉ ({2, 3} : Finset (ZMod 4)) by decide,
      show (2 : ZMod 4) ∉ ({3} : Finset (ZMod 4)) by decide,
      not_false_eq_true]
    rw [show Multiplicative.ofAdd (0 : ZMod 4) = 1 from rfl, map_one,
      AlgEquiv.one_apply]
    rw [fourEquiv_two, AlgEquiv.restrictScalars_apply, hanti', h3]
    change a * (σ a * (-a * -(σ a))) = _
    ring
  have hnorm : algebraMap ℚ (Field r hr) (Algebra.norm ℚ a) = (a * σ a) ^ 2 := by
    rw [Algebra.norm_eq_prod_automorphisms, ← e.toEquiv.prod_comp (fun τ => τ a)]
    exact hvalues
  have hn : (Algebra.norm ℚ a) ^ 2 = 1 := by
    have h := NumberField.isUnit_iff_norm.mp u.isUnit
    rw [abs_eq (by norm_num : (0 : ℚ) ≤ 1)] at h
    change Algebra.norm ℚ a = 1 ∨ Algebra.norm ℚ a = -1 at h
    rcases h with h | h <;> simp only [h, one_pow, neg_one_sq]
  have hx4 : (a * σ a) ^ 4 = 1 := by
    have h := congrArg (algebraMap ℚ (Field r hr)) hn
    rw [map_pow, map_one, hnorm] at h
    simpa only [← pow_mul] using h
  letI : NeZero (orderOf (a * σ a)) :=
    ⟨(isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by decide, hx4⟩).orderOf_pos.ne'⟩
  have ho := NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
    (IsPrimitiveRoot.orderOf (a * σ a))
  rw [torsion_order r hr hr5] at ho
  have hx2 : (a * σ a) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp ho
  have hx : a * σ a = 1 ∨ a * σ a = -1 := sq_eq_one_iff.mp hx2
  have hσx : σ (a * σ a) = -(a * σ a) := by
    rw [map_mul, hσ2, hanti']
    ring
  rcases hx with hx | hx <;> rw [hx] at hσx <;> norm_num at hσx

/-- The genuine Hasse unit index of the actual cyclic quartic field is one.
The proof excludes an anti-real maximal-order unit using its four conjugates. -/
theorem unit_index (hr : r % 8 = 5) (hr5 : 5 < r) :
    IsCMField.indexRealUnits (Field r hr) = 1 := by
  rcases IsCMField.indexRealUnits_eq_one_or_two (Field r hr) with h | h
  · exact h
  exfalso
  obtain ⟨u, hu⟩ := (IsCMField.indexRealUnits_eq_two_iff (Field r hr)).mp h
  let ζ := IsCMField.unitsMulComplexConjInv (Field r hr) u
  have horder : orderOf ζ = 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ((Subgroup.eq_top_iff' _).mp hu)]
    exact torsion_order r hr hr5
  have hζne : ζ ≠ 1 := by
    intro hζ
    rw [hζ, orderOf_one] at horder
    omega
  have hζ2 := NumberField.Units.pow_torsionOrder_eq_one (Field r hr) ζ.property
  rw [torsion_order r hr hr5] at hζ2
  have hfield : ((ζ : (𝓞 (Field r hr))ˣ) : Field r hr) = -1 := by
    rcases sq_eq_one_iff.mp (congrArg (fun v : (𝓞 (Field r hr))ˣ =>
      (v : Field r hr)) hζ2) with h | h
    · exact (hζne (Subtype.ext (Units.ext (RingOfIntegers.ext h)))).elim
    · exact h
  have hquot : (u : Field r hr) *
      (IsCMField.complexConj (Field r hr) (u : Field r hr))⁻¹ = -1 := by
    change ((u * (IsCMField.unitsComplexConj (Field r hr) u)⁻¹ :
      (𝓞 (Field r hr))ˣ) : Field r hr) = -1 at hfield
    rw [NumberField.Units.coe_mul] at hfield
    change (u : Field r hr) * algebraMap (𝓞 (Field r hr)) (Field r hr)
      (↑((IsCMField.unitsComplexConj (Field r hr) u)⁻¹)) = -1 at hfield
    rw [map_units_inv] at hfield
    exact hfield
  have hanti : IsCMField.complexConj (Field r hr) (u : Field r hr) =
      -(u : Field r hr) := by
    have hc : IsCMField.complexConj (Field r hr) (u : Field r hr) ≠ 0 :=
      (map_ne_zero _).mpr (NumberField.Units.coe_ne_zero u)
    have := (div_eq_iff hc).mp hquot
    linear_combination this
  exact no_antireal_unit r hr hr5 u hanti

end D5.S3.Arith.CyclotomicFields.MercaQuarticField
