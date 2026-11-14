/- GID: D5/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/NormalQuotientClassCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quotient conjugacy classes characterize perfect coding of normal subgroups. -/
import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Ma--Nikandish--Zhang antecedent Theorem 2.9, perfect-code second part,
original scientific05 C16. This criterion concerns actual conjugacy classes
in the actual quotient group. It is independent of the missing total-code
branch, and does not assert quotient total-code inheritance. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.CayleySumCodes.NormalQuotientClassCriterion
open TotalPerfectCriterion PerfectCodeTransversal NormalTransversal
variable {G Q : Type*} [Group G] [Group Q]

private def classMap (f : G →* Q) (x : G) : conjugatesOf x → conjugatesOf (f x) :=
  fun y => ⟨f y.1, f.map_isConj y.2⟩

private theorem classMap_surjective (f : G →* Q) (hf : Function.Surjective f) (x : G) :
    Function.Surjective (classMap f x) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, ha⟩ := isConj_iff.mp hy
  obtain ⟨b, hb⟩ := hf a
  refine ⟨⟨b*x*b⁻¹, isConj_iff.mpr ⟨b, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change f (b*x*b⁻¹) = y
  simpa only [map_mul, map_inv, hb] using ha

private theorem classMap_bijective [Finite G] (f : G →* Q)
    (hf : Function.Surjective f) (x : G)
    (hc : Nat.card (conjugatesOf x) = Nat.card (conjugatesOf (f x))) :
    Function.Bijective (classMap f x) :=
  (Nat.bijective_iff_surjective_and_card (classMap f x)).mpr
    ⟨classMap_surjective f hf x, hc⟩

private theorem quotient_eq (H : Subgroup G) [H.Normal] (x y : G) :
    QuotientGroup.mk' H x = QuotientGroup.mk' H y ↔ x⁻¹*y ∈ H := by
  change (x : G ⧸ H) = (y : G ⧸ H) ↔ x⁻¹*y ∈ H
  exact QuotientGroup.eq

private theorem transversal_unique (H : Subgroup G) [H.Normal] (T : Set G)
    (ht : Subgroup.IsComplement T (H : Set G)) (x y : G) (hx : x ∈ T) (hy : y ∈ T)
    (he : QuotientGroup.mk' H x = QuotientGroup.mk' H y) : x = y := by
  obtain ⟨t, _, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht x
  have h1 := hu ⟨x, hx⟩ (by simp)
  have h2 := hu ⟨y, hy⟩ ((quotient_eq H y x).mp he.symm)
  exact congrArg Subtype.val (h1.trans h2.symm)

/-- A full normal transversal is equivalent to equal-cardinality conjugacy
lifts of every quotient element. Both directions use actual full classes. -/
theorem nlt_iff [Finite G] (H : Subgroup G) [H.Normal] :
    NLT H ↔ ∀ q : G ⧸ H, ∃ t : G, QuotientGroup.mk' H t = q ∧
      Nat.card (conjugatesOf t) = Nat.card (conjugatesOf q) := by
  classical
  let f := QuotientGroup.mk' H
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective H
  constructor
  · rintro ⟨T, hn, ht⟩ q
    obtain ⟨x, rfl⟩ := hf q
    obtain ⟨t, hh, _⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht x
    have he : f t.1 = f x := (quotient_eq H t.1 x).mpr hh
    refine ⟨t.1, he, ?_⟩
    have inj : Function.Injective (classMap f t.1) := by
      intro y z hyz
      apply Subtype.ext
      apply transversal_unique H T ht y.1 z.1
      · obtain ⟨a, ha⟩ := isConj_iff.mp y.2
        exact ha ▸ hn a t.1 t.2
      · obtain ⟨a, ha⟩ := isConj_iff.mp z.2
        exact ha ▸ hn a t.1 t.2
      · exact congrArg Subtype.val hyz
    have hc := Nat.card_congr (Equiv.ofBijective (classMap f t.1)
      ⟨inj, classMap_surjective f hf t.1⟩)
    simpa only [he] using hc
  · intro hlift
    let rep : ConjClasses (G ⧸ H) → G ⧸ H := fun c => Classical.choose c.exists_rep
    have hrep (c : ConjClasses (G ⧸ H)) : ConjClasses.mk (rep c) = c :=
      Classical.choose_spec c.exists_rep
    choose lift hfl hcard using (fun c : ConjClasses (G ⧸ H) => hlift (rep c))
    have hclass (c : ConjClasses (G ⧸ H)) : ConjClasses.mk (f (lift c)) = c := by
      rw [hfl c]
      exact hrep c
    let T : Set G := {g | ∃ c : ConjClasses (G ⧸ H), IsConj (lift c) g}
    have hn : NormalSubset T := by
      rintro a x ⟨c, hc⟩
      exact ⟨c, hc.trans (isConj_iff.mpr ⟨a, rfl⟩)⟩
    have himage (g : G) (c : ConjClasses (G ⧸ H)) (hg : IsConj (lift c) g) :
        ConjClasses.mk (f g) = c :=
      (ConjClasses.mk_eq_mk_iff_isConj.mpr (f.map_isConj hg)).symm.trans (hclass c)
    have hbij (c : ConjClasses (G ⧸ H)) : Function.Bijective (classMap f (lift c)) := by
      apply classMap_bijective f hf
      rw [show f (lift c) = rep c from hfl c]
      exact hcard c
    refine ⟨T, hn, Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr ?_⟩
    intro x
    let c := ConjClasses.mk (f x)
    have hx : IsConj (f (lift c)) (f x) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hclass c)
    obtain ⟨y, hy⟩ := (hbij c).2 ⟨f x, hx⟩
    have hfy : f y.1 = f x := congrArg Subtype.val hy
    refine ⟨⟨y.1, c, y.2⟩, (quotient_eq H y.1 x).mp hfy, ?_⟩
    rintro ⟨z, d, hz⟩ hzx
    have hfz : f z = f x := (quotient_eq H z x).mpr hzx
    have hdc : d = c := by
      rw [← himage z d hz, hfz]
    subst d
    apply Subtype.ext
    have heq : classMap f (lift c) ⟨z, hz⟩ = classMap f (lift c) y :=
      Subtype.ext (hfz.trans hfy.symm)
    exact congrArg (fun v : conjugatesOf (lift c) => (v : G)) ((hbij c).1 heq)

/-- The normal-subgroup perfect-code criterion from the unaffected second
part of antecedent Theorem 2.9. Each outside coset has a representative whose
full conjugacy class has exactly the cardinality of that quotient class. -/
theorem result [Finite G] (H : Subgroup G) [H.Normal] :
    (∃ (Y : Set G) (hY : NormalSubset Y), IsPerfectCode (sumGraph Y hY) H) ↔
      ∀ x : G, x ∉ H → ∃ h : G, h ∈ H ∧
        Nat.card (conjugatesOf (QuotientGroup.mk' H x)) =
          Nat.card (conjugatesOf (x*h)) := by
  classical
  rw [normal_exists_iff H, nlt_iff H]
  constructor
  · intro hl x _
    obtain ⟨t, ht, hc⟩ := hl (QuotientGroup.mk' H x)
    obtain ⟨h, hh, he⟩ := (QuotientGroup.mk'_eq_mk' H).mp ht.symm
    refine ⟨h, hh, ?_⟩
    simpa only [he] using hc.symm
  · intro hl q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H q
    by_cases hx : x ∈ H
    · have he : QuotientGroup.mk' H x = 1 := by
        change x ∈ (QuotientGroup.mk' H).ker
        simpa only [QuotientGroup.ker_mk'] using hx
      refine ⟨1, by simpa using he.symm, ?_⟩
      rw [he]
      have hG : conjugatesOf (1 : G) = {1} := by ext z; simp [conjugatesOf]
      have hQ : conjugatesOf (1 : G ⧸ H) = {1} := by ext z; simp [conjugatesOf]
      rw [hG, hQ]
      simp
    · obtain ⟨h, hh, hc⟩ := hl x hx
      have he : QuotientGroup.mk' H (x*h) = QuotientGroup.mk' H x := by
        exact (QuotientGroup.mk'_eq_mk' H).mpr ⟨h, hh, rfl⟩ |>.symm
      exact ⟨x*h, he, hc.symm⟩

#print axioms nlt_iff
#print axioms result
end D5.S3.Combinatorics.CayleySumCodes.NormalQuotientClassCriterion
