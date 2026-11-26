import GRH.Lib.General.Geometry.ConstantFunctions
import GRH.Lib.Cohomology.ProperBaseChange.ProperBaseChange
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: A proper scheme has closed diagonal and valuative lifting from one affine atlas. -/

open CategoryTheory Limits AlgebraicGeometry CommRingCat Scheme Spec terminal Ideal TopologicalSpace
  PrimeSpectrum Set Cofan.IsColimit IsOpenImmersion Fintype prod
variable {X R} (s : X ⟶ Spec R)

/-- For X proper over Spec R there is a morphism a: Spec T → X, locally of finite type, through
which every morphism Spec O → X factors, for all rings O satisfying `IsComparableRing`. -/
lemma exists_finiteType_atlas [IsProper s] : ∃ T a, @LocallyOfFiniteType _ X a ∧ ∀ O,
    IsComparableRing (@id (carrier O)) → ∀ z, ∃ u, @map T O u ≫ a = z :=
  let U := X.affineCover.finiteSubcover (H := QuasiCompact.compactSpace_of_compactSpace s)
  ⟨_, inv (toSpecΓ _) ≫ Sigma.desc U.f, locallyOfFiniteType_comp (hg :=
    HasRingHomProperty.instIsZariskiLocalAtSource.sigmaDesc inferInstance) .., fun O h z ↦ by
  choose m M l using fun x : Spec O ↦ exists_le_maximal _ x.2.1
  choose g n k using (exists_range_iff.1 <| isTopologicalBasis_basic_opens.isOpen_iff.1
    (z ⁻¹ᵁ Hom.opensRange _).2 ⟨_, M · |>.isPrime⟩ (U.covers _))
  choose e n h d using (exists_idempotent_dvd_of_notMem h (M _) <| n ·)
  let C x : Clopens (Spec O) := isIdempotentElemEquivClopens ⟨_, h x⟩
  have ⟨t, _⟩ := finite_cover_nhds (C · |>.isOpen.mem_nhds (by tauto))
  choose g l _ D using exists_disjointed_le (t.restrict C)
  have ⟨c⟩ := nonempty_isColimit_cofanMk_of (Opens.ι <| g · |>.toOpens)
    (by simp_all [Clopens.ext_iff, iUnion_subtype]) (D.mono (by simp [← Opens.coe_disjoint]))
  use preimage (desc c (fun x ↦ lift _ (Opens.ι _ ≫ z) (range_subset_iff.2 (k _ <| l x ·.2 ∘
    mem_of_dvd _ (d x))) ≫ Sigma.ι ..) ≫ toSpecΓ _), hom_ext c _ _ (by simp [-cofan_mk_inj]; simp)⟩

/-- If s: X → Spec R is a proper morphism of schemes, then the functor of points of X over R is
proper in the sense of `IsProperOver`. -/
lemma isProperOver_pointsToBase [IsProper s] :
  IsProperOver (pointsToBase s) := have := X.isSeparated_iff.2 (comp_from s ▸ {})
  ⟨fun C ⟨x⟩ ⟨y⟩ ↦ (exists_ideal_le_ker_iff_factors (diag X) (lift ..)).imp (by
    intros; simp_all [prod.hom_ext_iff, lift_fst, lift_snd]; exact ULift.up_inj),
                                    (exists_finiteType_atlas s).imp fun _ ⟨a, _, H⟩ ↦
    ⟨⟨a⟩, fun O z h ↦ ((IsProper.eq_valuativeCriterion.le _ _ s ‹_›).1.1.1 ⟨O, _, z.1,
    map (ofHom (.codRestrict _ _ h)), ⟨homEquiv.injective (by aesop)⟩⟩).elim fun ⟨⟨l⟩, _⟩ ↦
    (H _ isTest_of_preValuationRing.2 l.1).imp (by intros; simp_all; congrm ⟨$(l.2)⟩)⟩⟩
