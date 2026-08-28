/- GID: D5/S3/Arith/Representation/IcosahedralExteriorSquareDecomposition
   generality: I
   mirror-B: D5/B/S3/Arith/Representation/IcosahedralExteriorSquareDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The real A5 exterior square splits into two icosahedral summands. -/

import D5.S0.Carrier.Conj
import D5.S1.Scale.Embedding
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke

-- Library-search audit trail (2026-08-28):
-- * Repository searches found no existing real `A5` exterior-square decomposition.
-- * Pinned Mathlib supplies the alternating group, exterior power, character/Hom formula,
--   Schur injectivity, and Maschke splitting used below.
-- * Pinned Mathlib has no `A5` character table, explicit real icosahedral representations,
--   or converse from character equality to representation equivalence.
-- * Loogle, LeanSearch, Reservoir, and GitHub supplied no third-party exact theorem.

namespace D5.S3.Arith.Representation.IcosahedralExteriorSquareDecomposition

open scoped BigOperators MonoidAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The source's concrete group `A5`.
abbrev AlternatingFive := alternatingGroup (Fin 5)

-- The zero-coordinate-sum hyperplane in the real permutation space on five roots.
def centeredRootSubspace : Submodule ℝ (Fin 5 → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, x i = 0 at hx
    change ∑ i, y i = 0 at hy
    simp [Finset.sum_add_distrib, hx, hy]
  smul_mem' := by
    intro c x hx
    change ∑ i, x i = 0 at hx
    calc
      ∑ i, c * x i = c * ∑ i, x i := (Finset.mul_sum ..).symm
      _ = 0 := by rw [hx, mul_zero]

-- The four-dimensional standard real `A5` state space `V4`.
abbrev CenteredRootState := centeredRootSubspace

-- Even permutations act on `V4` by permuting its five coordinates.
noncomputable def centeredRootRepresentation :
    Representation ℝ AlternatingFive CenteredRootState where
  toFun g :=
    { toFun := fun x =>
        ⟨fun i => x.1 ((g⁻¹).1 i), by
          change ∑ i, x.1 ((g⁻¹).1 i) = 0
          rw [Equiv.sum_comp (g⁻¹).1 x.1]
          exact x.2⟩
      map_add' := by
        intro x y
        ext i
        rfl
      map_smul' := by
        intro c x
        ext i
        rfl }
  map_one' := by
    ext x i
    rfl
  map_mul' := by
    intro g h
    ext x i
    rfl

-- The complete second-order observation space `Lambda^2 V4`.
abbrev SecondOrderObservationSpace := ⋀[ℝ]^2 CenteredRootState

-- The induced `A5` action on the genuine second exterior power.
noncomputable def secondOrderRepresentation :
    Representation ℝ AlternatingFive SecondOrderObservationSpace where
  toFun g := exteriorPower.map 2 (centeredRootRepresentation g)
  map_one' := by
    change exteriorPower.map 2 (LinearMap.id : CenteredRootState →ₗ[ℝ] CenteredRootState) =
      LinearMap.id
    exact exteriorPower.map_id
  map_mul' := by
    intro g h
    change exteriorPower.map 2
        ((centeredRootRepresentation g).comp (centeredRootRepresentation h)) =
      (exteriorPower.map 2 (centeredRootRepresentation g)).comp
        (exteriorPower.map 2 (centeredRootRepresentation h))
    rw [exteriorPower.map_comp]

-- The six-dimensional carrier of the two named three-dimensional icosahedral summands.
abbrev IcosahedralCompletionSpace := (Fin 3 → ℝ) × (Fin 3 → ℝ)

-- A source-specific certificate that two real characters are the two golden Galois embeddings
-- of one `Z[phi]`-valued character, and are genuinely distinct.
structure GoldenGaloisCharacterPair
    (rho3 rho3Prime : Representation ℝ AlternatingFive (Fin 3 → ℝ)) where
  goldenCharacter : AlternatingFive → D5.S0.Carrier.GoldenInt
  first_embedding : ∀ g,
    D5.S1.Scale.embedding (goldenCharacter g) = rho3.character g
  conjugate_embedding : ∀ g,
    D5.S1.Scale.embedding (D5.S0.Carrier.conj (goldenCharacter g)) = rho3Prime.character g
  separated : ∃ g,
    D5.S1.Scale.embedding (goldenCharacter g) ≠
      D5.S1.Scale.embedding (D5.S0.Carrier.conj (goldenCharacter g))

private theorem GoldenGaloisCharacterPair.character_ne
    {rho3 rho3Prime : Representation ℝ AlternatingFive (Fin 3 → ℝ)}
    (h : GoldenGaloisCharacterPair rho3 rho3Prime) :
    rho3.character ≠ rho3Prime.character := by
  intro heq
  obtain ⟨g, hg⟩ := h.separated
  apply hg
  rw [h.first_embedding, h.conjugate_embedding, heq]

private theorem character_sum_equiv
    {G V W U : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (rho : Representation ℝ G V) (sigma : Representation ℝ G W)
    (tau : Representation ℝ G U)
    (hirrRho : rho.IsIrreducible) (hirrSigma : sigma.IsIrreducible)
    (hdistinct : rho.character ≠ sigma.character)
    (hcharacter : tau.character = rho.character + sigma.character) :
    Nonempty (Representation.Equiv (rho.prod sigma) tau) := by
  letI := Fintype.ofFinite G
  letI : NeZero (Nat.card G : ℝ) := by
    rw [← @Fintype.card_eq_nat_card G (by assumption)]
    exact NeZero.charZero
  letI : Invertible (Nat.card G : ℝ) :=
    invertibleOfNonzero (NeZero.ne (Nat.card G : ℝ))
  letI : rho.IsIrreducible := hirrRho
  letI : sigma.IsIrreducible := hirrSigma
  letI : Nontrivial V := by
    change Nontrivial rho.asModule
    exact IsSimpleModule.nontrivial ℝ[G] rho.asModule
  letI : Nontrivial W := by
    change Nontrivial sigma.asModule
    exact IsSimpleModule.nontrivial ℝ[G] sigma.asModule
  letI : IsEmpty (Representation.Equiv rho sigma) :=
    ⟨fun e => hdistinct (Representation.char_iso e)⟩
  letI : IsEmpty (Representation.Equiv sigma rho) :=
    ⟨fun e => hdistinct (Representation.char_iso e.symm)⟩
  have hcrossRS : Module.finrank ℝ (Representation.IntertwiningMap rho sigma) = 0 :=
    Module.finrank_zero_iff.mpr inferInstance
  have hcrossSR : Module.finrank ℝ (Representation.IntertwiningMap sigma rho) = 0 :=
    Module.finrank_zero_iff.mpr inferInstance
  have hhomRReal :
      (Module.finrank ℝ (Representation.IntertwiningMap rho tau) : ℝ) =
        Module.finrank ℝ (Representation.IntertwiningMap rho rho) := by
    calc
      Module.finrank ℝ (Representation.IntertwiningMap rho tau) =
          (Nat.card G : ℝ)⁻¹ * ∑ g : G, tau.character g * rho.character g⁻¹ :=
        (Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho tau).symm
      _ = (Nat.card G : ℝ)⁻¹ *
            ∑ g : G, (rho.character g + sigma.character g) * rho.character g⁻¹ := by
        rw [hcharacter]
        rfl
      _ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, rho.character g * rho.character g⁻¹ +
            (Nat.card G : ℝ)⁻¹ * ∑ g : G, sigma.character g * rho.character g⁻¹ := by
        simp_rw [add_mul, Finset.sum_add_distrib]
        ring
      _ = Module.finrank ℝ (Representation.IntertwiningMap rho rho) +
            Module.finrank ℝ (Representation.IntertwiningMap rho sigma) := by
        rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
          Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
      _ = Module.finrank ℝ (Representation.IntertwiningMap rho rho) := by
        norm_num [hcrossRS]
  have hhomR :
      Module.finrank ℝ (Representation.IntertwiningMap rho tau) =
        Module.finrank ℝ (Representation.IntertwiningMap rho rho) := by
    exact_mod_cast hhomRReal
  have hhomSReal :
      (Module.finrank ℝ (Representation.IntertwiningMap sigma tau) : ℝ) =
        Module.finrank ℝ (Representation.IntertwiningMap sigma sigma) := by
    calc
      Module.finrank ℝ (Representation.IntertwiningMap sigma tau) =
          (Nat.card G : ℝ)⁻¹ * ∑ g : G, tau.character g * sigma.character g⁻¹ :=
        (Representation.card_inv_mul_sum_char_mul_char_eq_finrank sigma tau).symm
      _ = (Nat.card G : ℝ)⁻¹ *
            ∑ g : G, (rho.character g + sigma.character g) * sigma.character g⁻¹ := by
        rw [hcharacter]
        rfl
      _ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, rho.character g * sigma.character g⁻¹ +
            (Nat.card G : ℝ)⁻¹ * ∑ g : G, sigma.character g * sigma.character g⁻¹ := by
        simp_rw [add_mul, Finset.sum_add_distrib]
        ring
      _ = Module.finrank ℝ (Representation.IntertwiningMap sigma rho) +
            Module.finrank ℝ (Representation.IntertwiningMap sigma sigma) := by
        rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
          Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
      _ = Module.finrank ℝ (Representation.IntertwiningMap sigma sigma) := by
        norm_num [hcrossSR]
  have hhomS :
      Module.finrank ℝ (Representation.IntertwiningMap sigma tau) =
        Module.finrank ℝ (Representation.IntertwiningMap sigma sigma) := by
    exact_mod_cast hhomSReal
  have hselfR : 0 < Module.finrank ℝ (Representation.IntertwiningMap rho rho) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨Representation.IntertwiningMap.id rho, ?_⟩
    intro hid
    apply not_subsingleton V
    constructor
    intro x y
    have hx := DFunLike.congr_fun hid x
    have hy := DFunLike.congr_fun hid y
    simpa using hx.trans hy.symm
  have hselfS : 0 < Module.finrank ℝ (Representation.IntertwiningMap sigma sigma) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨Representation.IntertwiningMap.id sigma, ?_⟩
    intro hid
    apply not_subsingleton W
    constructor
    intro x y
    have hx := DFunLike.congr_fun hid x
    have hy := DFunLike.congr_fun hid y
    simpa using hx.trans hy.symm
  have hnonzeroR : ∃ f : Representation.IntertwiningMap rho tau, f ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (hhomR.symm ▸ hselfR)
  have hnonzeroS : ∃ f : Representation.IntertwiningMap sigma tau, f ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (hhomS.symm ▸ hselfS)
  obtain ⟨f, hf⟩ := hnonzeroR
  obtain ⟨g, hg⟩ := hnonzeroS
  have hfInjective : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hgInjective : Function.Injective g :=
    (Representation.IsIrreducible.injective_or_eq_zero g).resolve_right hg
  obtain ⟨rModule, hrModule⟩ := MonoidAlgebra.exists_leftInverse_of_injective
    (Representation.IntertwiningMap.equivLinearMapAsModule rho tau f)
    (LinearMap.ker_eq_bot.mpr hfInjective)
  let r : Representation.IntertwiningMap tau rho :=
    (Representation.IntertwiningMap.equivLinearMapAsModule tau rho).symm rModule
  have hrf (v : V) : r (f v) = v := by
    have h := LinearMap.congr_fun hrModule v
    exact h
  have hrg : r.comp g = 0 := Subsingleton.elim _ _
  let inclusion : Representation.IntertwiningMap (rho.prod sigma) tau :=
    { toLinearMap := LinearMap.coprod f.toLinearMap g.toLinearMap
      isIntertwining' a := by
        apply LinearMap.ext
        rintro ⟨v, w⟩
        change f (rho a v) + g (sigma a w) = tau a (f v + g w)
        rw [map_add, f.isIntertwining, g.isIntertwining] }
  have inclusionInjective : Function.Injective inclusion := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ heq
    have hrgApply (x : W) : r (g x) = 0 := by
      have h := DFunLike.congr_fun hrg x
      simpa [Representation.IntertwiningMap.comp_apply] using h
    have hv : v = v' := by
      have h := congrArg r heq
      simpa [inclusion, hrf, hrgApply] using h
    have hw : w = w' := by
      apply hgInjective
      simpa [inclusion, hv] using heq
    exact Prod.ext hv hw
  have hfinrank : Module.finrank ℝ (V × W) = Module.finrank ℝ U := by
    have hAtOne := congrFun hcharacter (1 : G)
    simp only [Pi.add_apply, Representation.char_one] at hAtOne
    rw [Module.finrank_prod]
    exact_mod_cast hAtOne.symm
  exact ⟨Representation.IntertwiningMap.ofBijective inclusion
    ⟨inclusionInjective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp inclusionInjective⟩⟩

-- Fivefold second-order observation decomposition. For the two source-named,
-- Galois-conjugate irreducible three-dimensional real icosahedral representations, the source
-- character sum determines a genuine `A5`-equivariant decomposition of `Lambda^2 V4` and its
-- underlying six-dimensional completion equivalence.
theorem exterior_square_decomposes_into_icosahedral_pair
    (rho3 rho3Prime : Representation ℝ AlternatingFive (Fin 3 → ℝ))
    (hirreducible3 : rho3.IsIrreducible)
    (hirreducible3Prime : rho3Prime.IsIrreducible)
    (hGalois : GoldenGaloisCharacterPair rho3 rho3Prime)
    (hcharacter : secondOrderRepresentation.character =
      rho3.character + rho3Prime.character) :
    Nonempty (Representation.Equiv secondOrderRepresentation (rho3.prod rho3Prime)) ∧
      Nonempty (IcosahedralCompletionSpace ≃ₗ[ℝ] SecondOrderObservationSpace) := by
  have hdistinct := hGalois.character_ne
  obtain ⟨decomposition⟩ := character_sum_equiv rho3 rho3Prime secondOrderRepresentation
    hirreducible3 hirreducible3Prime hdistinct hcharacter
  exact ⟨⟨decomposition.symm⟩, ⟨decomposition.toLinearEquiv⟩⟩

-- Reverse probe for CAS-A1: the first public leaf projects the actual representation equivalence.
example
    (rho3 rho3Prime : Representation ℝ AlternatingFive (Fin 3 → ℝ))
    (hirreducible3 : rho3.IsIrreducible)
    (hirreducible3Prime : rho3Prime.IsIrreducible)
    (hGalois : GoldenGaloisCharacterPair rho3 rho3Prime)
    (hcharacter : secondOrderRepresentation.character =
      rho3.character + rho3Prime.character) :
    Nonempty (Representation.Equiv secondOrderRepresentation (rho3.prod rho3Prime)) :=
  (exterior_square_decomposes_into_icosahedral_pair rho3 rho3Prime
    hirreducible3 hirreducible3Prime hGalois hcharacter).1

-- Reverse probe for CAS-A2: the second leaf forces the observation carrier to have dimension six.
example
    (rho3 rho3Prime : Representation ℝ AlternatingFive (Fin 3 → ℝ))
    (hirreducible3 : rho3.IsIrreducible)
    (hirreducible3Prime : rho3Prime.IsIrreducible)
    (hGalois : GoldenGaloisCharacterPair rho3 rho3Prime)
    (hcharacter : secondOrderRepresentation.character =
      rho3.character + rho3Prime.character) :
    Module.finrank ℝ SecondOrderObservationSpace = 6 := by
  obtain ⟨e⟩ := (exterior_square_decomposes_into_icosahedral_pair rho3 rho3Prime
    hirreducible3 hirreducible3Prime hGalois hcharacter).2
  rw [← e.finrank_eq, Module.finrank_prod]
  norm_num

-- Trivialization probe for CAS-A1: the Galois certificate rules out identifying the two summands.
example
    (rho3 rho3Prime : Representation ℝ AlternatingFive (Fin 3 → ℝ))
    (hGalois : GoldenGaloisCharacterPair rho3 rho3Prime) :
    rho3.character ≠ rho3Prime.character :=
  hGalois.character_ne

#print axioms exterior_square_decomposes_into_icosahedral_pair

end D5.S3.Arith.Representation.IcosahedralExteriorSquareDecomposition
