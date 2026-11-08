/- GID: D5/S3/FiniteGroups/FrobeniusCharacterDegrees
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FrobeniusCharacterDegrees
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed-point-free conjugation gives the character-degree divisibility dichotomy. -/

/-
Escape audit unfinished for the five arbitrary-characteristic additions: https://github.com/the-omega-institute/trureturing/issues/27899
admission_basis: escape-witness
Frozen baseline inputs (module statement identities):
D5/S3/FiniteGroups/FiniteCharacterAlgebra @ sha256:5ea5be4246f85df1a6a5a34be414eaa3174509f06a0bb1c923f3d8e8cfff6a55
D5/S3/FiniteGroups/CliffordConstituents @ sha256:f6e6d286b818f1665d1a59844c6a457c3907fdb4bfcaca1018640dabe80920d7
D5/S3/FiniteGroups/CliffordDecomposition @ sha256:942e8a07e15758d3a11fe9c6234cbc9507dec0773748704252c247840de4f647
D5/S3/FiniteGroups/InducedCharacterFormula @ sha256:1c3aec1e0516377c8748f40cb426d2126c6743facaedfe9089323543a1b2e4e2
D5/S3/FiniteGroups/CharacterDegreeDivisibility @ sha256:ff98a4e5b1afad07cc0f8e78fc943f0c30d1141d02e1e4ebacbf7ee2fa074c68
D5/S3/FiniteGroups/ComplexCharacterAbelianProducts @ sha256:0f5341f17c27bceb2085721564486b26af2042f25ae947bd7e5d60c092c79fcf
Module escape_witness: degree_dvd_or_index_dvd_of_fixedPointFree
Fixed-point-free conjugation forces a nontrivial constituent inertia group to equal the normal kernel; Clifford decomposition yields the dichotomy.
trivial_of_invariant_fixedPointFree | proof_shape: bind-only | escape_witness: none | consumer: inertia_eq_of_fixedPointFree
abelian_character_eq_iff | proof_shape: bind-only | escape_witness: none | consumer: inertia_eq_of_fixedPointFree
degree_square_le_card | proof_shape: content | escape_witness: D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible | consumer: D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.B_degree_dvd
degree_dvd_quotient_card | proof_shape: content | escape_witness: D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card | consumer: degree_dvd_or_index_dvd_of_fixedPointFree
inertia_eq_of_fixedPointFree | proof_shape: bind-only | escape_witness: none | consumer: degree_dvd_or_index_dvd_of_fixedPointFree
restriction_trivial_of_clifford_constituent_trivial | proof_shape: bind-only | escape_witness: none | consumer: degree_dvd_or_index_dvd_of_fixedPointFree
degree_dvd_or_index_dvd_of_fixedPointFree | proof_shape: content | escape_witness: degree_dvd_or_index_dvd_of_fixedPointFree | consumer: D5.S3.FiniteGroups.BahturinCentronePereiraPeakGroups.BCP31.B_degree_dvd
trivial_of_equiv_fixedPointFree_of_isAlgClosed | proof_shape: content | escape_witness: trivial_of_equiv_fixedPointFree_of_isAlgClosed | consumer: inertia_eq_of_fixedPointFree_of_isAlgClosed, trivial_of_character_invariant_fixedPointFree_of_isAlgClosed
trivial_of_character_invariant_fixedPointFree_of_isAlgClosed | proof_shape: content | escape_witness: D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.exists_trace_one_zero_of_not_nonempty_linearEquiv | consumer: none
inertia_eq_of_fixedPointFree_of_isAlgClosed | proof_shape: content | escape_witness: trivial_of_equiv_fixedPointFree_of_isAlgClosed | consumer: trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed
restriction_trivial_of_clifford_constituent_trivial_generic | proof_shape: bind-only | escape_witness: none | consumer: trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed
trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed | proof_shape: content | escape_witness: trivial_of_equiv_fixedPointFree_of_isAlgClosed | consumer: none
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import D5.S3.FiniteGroups.ComplexCharacterAbelianProducts
import D5.S3.FiniteGroups.InducedCharacterFormula
import D5.S3.FiniteGroups.CharacterDegreeDivisibility
import D5.S3.FiniteGroups.CliffordConstituents
import D5.S3.FiniteGroups.CliffordDecomposition
import D5.S3.FiniteGroups.FiniteCharacterAlgebra

section ScratchSource_FixedPointFreeDual

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory

variable {A : Type*} [CommGroup A]

private theorem trivial_of_invariant_fixedPointFree [Finite A]
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k A V) (f : MulAut A)
    (hf : ∀ a : A, f a = a → a = 1)
    (hρ : ∀ a : A, ρ (f a) = ρ a) : Representation.IsTrivial ρ := by
  constructor
  intro a
  obtain ⟨b, rfl⟩ := MonoidHom.FixedPointFree.commutatorMap_surjective
    (φ := f) hf a
  simp only [MonoidHom.commutatorMap_apply, div_eq_mul_inv]
  rw [map_mul, ← hρ b, ← map_mul, mul_inv_cancel, map_one]
  rfl

private theorem abelian_character_eq_iff {k : Type*} [Field k] [IsAlgClosed k]
    (X : FDRep k A) [Simple X] (a b : A) :
    X.character a = X.character b ↔ X.ρ a = X.ρ b := by
  letI : Representation.IsIrreducible X.ρ := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
  have hdim : Module.finrank k X = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative X.ρ
  obtain ⟨c, hc⟩ := D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.central_action_scalar X.ρ a (fun g => mul_comm a g)
  obtain ⟨d, hd⟩ := D5.S3.FiniteGroups.ComplexCharacterAbelianProducts.central_action_scalar X.ρ b (fun g => mul_comm b g)
  constructor
  · intro h
    have hcd : c = d := by
      simpa [FDRep.character, Representation.character, hc, hd,
        map_smul, LinearMap.trace_id, hdim] using h
    rw [hc, hd, hcd]
  · intro h
    exact congrArg (LinearMap.trace k X) h

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_FixedPointFreeDual

section ScratchSource_CharacterFacts

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory
open scoped _root_.MonoidAlgebra

/-
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19389
- Dimension bound obtained directly from the upstream density theorem. -/
theorem degree_square_le_card (G : Type) [Group G] [Finite G]
    (X : FDRep ℂ G) [Simple X] :
    Module.finrank ℂ X ^ 2 ≤ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hρ : Representation.IsIrreducible X.ρ := _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
  have hs : Function.Surjective (Representation.asAlgebraHom X.ρ) :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible X.ρ hρ
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (Representation.asAlgebraHom X.ρ).toLinearMap) hs
  have hcard : Module.finrank ℂ (MonoidAlgebra ℂ G) = Nat.card G := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ), Fintype.card_eq_nat_card]
  simpa [Module.finrank_linearMap, hcard, pow_two] using h

/-- A simple representation trivial on a normal subgroup has degree dividing the quotient order. -/
private theorem degree_dvd_quotient_card (G : Type) [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (X : FDRep ℂ G) [Simple X]
    [Representation.IsTrivial (X.ρ.comp N.subtype)] :
    Module.finrank ℂ X ∣ Nat.card (G ⧸ N) := by
  have hcomp : (Representation.ofQuotient X.ρ N).comp (QuotientGroup.mk' N) = X.ρ := by
    ext g v
    rfl
  haveI : Representation.IsIrreducible ((Representation.ofQuotient X.ρ N).comp (QuotientGroup.mk' N)) := by
    rw [hcomp]
    exact _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple X
  haveI : Representation.IsIrreducible (Representation.ofQuotient X.ρ N) :=
    (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.isIrreducible_comp_surjective_iff (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N) (Representation.ofQuotient X.ρ N)).mp inferInstance
  exact _root_.D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti.Representation.finrank_dvd_card (Representation.ofQuotient X.ρ N)

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_CharacterFacts

section ScratchSource_CliffordPeak

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti D5.S3.FiniteGroups.CliffordConstituents.TauCeti D5.S3.FiniteGroups.CliffordDecomposition.TauCeti D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti
open scoped IsMulCommutative

variable {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
  [IsMulCommutative N]

private theorem inertia_eq_of_fixedPointFree
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (V : FDRep ℂ N) [Simple V] (hV : ¬ Representation.IsTrivial V.ρ) :
    (MulAction.stabilizer K (toSkeleton V)) = N := by
  apply le_antisymm
  · intro g hg
    by_contra hgN
    apply hV
    apply trivial_of_invariant_fixedPointFree V.ρ (MulAut.conjNormal g⁻¹)
    · exact hfix g⁻¹ (fun h => hgN (by simpa using N.inv_mem h))
    · intro n
      apply (abelian_character_eq_iff V _ _).mp
      convert char_conj_eq_of_mem_inertia hg n using 1
      congr 1
      apply Subtype.ext
      simp
  · exact le_inertia V

private theorem restriction_trivial_of_clifford_constituent_trivial
    (W : FDRep ℂ K) (V : FDRep ℂ N) [Finite (K ⧸ (MulAction.stabilizer K (toSkeleton V)))]
    (e : ℕ) (iso : ((Action.res (FGModuleCat ℂ) (N).subtype).obj W) ≅ (D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V e))
    (hdim : Module.finrank ℂ W = e * ((MulAction.stabilizer K (toSkeleton V))).index * Module.finrank ℂ V)
    [Representation.IsTrivial V.ρ] :
    Representation.IsTrivial (W.ρ.comp N.subtype) := by
  classical
  letI : Fintype (K ⧸ (MulAction.stabilizer K (toSkeleton V))) := Fintype.ofFinite _
  constructor
  intro n
  apply (_root_.D5.S3.FiniteGroups.InducedCharacterFormula.Representation.char_eq_finrank_iff (W.ρ.comp N.subtype)
    (isOfFinOrder_of_finite n)).mp
  have hc := congrFun (FDRep.char_iso iso) n
  rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.character_actionRes, _root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum,
    finsum_eq_sum_of_fintype] at hc
  have hv (q : K ⧸ (MulAction.stabilizer K (toSkeleton V))) :
      ((conjNormalFDRepFunctor (Quotient.out q)).obj V).character n = (Module.finrank ℂ V : ℂ) := by
    rw [char_conjNormalFDRep]
    change LinearMap.trace ℂ V (V.ρ _) = _
    rw [Representation.isTrivial_def, LinearMap.trace_id]
  simp_rw [hv] at hc
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hc
  change W.character (N.subtype n) = (Module.finrank ℂ W : ℂ)
  rw [hc, hdim]
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  push_cast
  ring

/-- The degree dichotomy supplied by fixed-point-free conjugation on an abelian kernel. -/
theorem degree_dvd_or_index_dvd_of_fixedPointFree
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (W : FDRep ℂ K) [Simple W] :
    Module.finrank ℂ W ∣ N.index ∨ N.index ∣ Module.finrank ℂ W := by
  obtain ⟨V, hV, hf, e, he, ⟨iso⟩, hdim⟩ := (D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank (N := N) W)
  letI := hV
  letI := hf
  by_cases ht : Representation.IsTrivial V.ρ
  · letI := ht
    letI := restriction_trivial_of_clifford_constituent_trivial N W V e iso hdim
    left
    simpa [Subgroup.index_eq_card] using degree_dvd_quotient_card K N W
  · right
    rw [inertia_eq_of_fixedPointFree N hfix V ht] at hdim
    exact ⟨e * Module.finrank ℂ V, by rw [hdim]; ring⟩

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_CliffordPeak

section ScratchSource_NonabelianInvariant

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory

theorem trivial_of_character_invariant_fixedPointFree
    {A : Type*} [Group A] [Finite A] (α : MulAut A)
    (hα : ∀ a : A, α a = a → a = 1)
    (V : FDRep ℂ A) [Simple V]
    (hχ : ∀ a : A, V.character (α a) = V.character a) :
    Representation.IsTrivial V.ρ := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  let ρ' : Representation ℂ A V := V.ρ.comp α.toMonoidHom
  have hρ : Representation.IsIrreducible V.ρ :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple V
  have hρ' : Representation.IsIrreducible ρ' := by
    exact (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.isIrreducible_comp_surjective_iff
      α.toMonoidHom α.surjective V.ρ).2 hρ
  have hchar : Representation.character ρ' = Representation.character V.ρ := by
    funext a
    exact hχ a
  have horth : (Nat.card A : ℂ)⁻¹ * ∑ a : A, (Representation.character ρ') a *
      (Representation.character V.ρ) a⁻¹ =
      if Nonempty (Representation.Equiv V.ρ ρ') then (1 : ℂ) else 0 := by
    exact Representation.char_orthonormal ρ' V.ρ
  have hself : (Nat.card A : ℂ)⁻¹ * ∑ a : A, (Representation.character V.ρ) a *
      (Representation.character V.ρ) a⁻¹ =
      (1 : ℂ) := by
    simpa [if_pos (Nonempty.intro (Representation.Equiv.refl V.ρ))] using
      (Representation.char_orthonormal V.ρ V.ρ)
  rw [hchar] at horth
  have hnon : Nonempty (Representation.Equiv V.ρ ρ') := by
    by_contra hne
    have hzero : (Nat.card A : ℂ)⁻¹ * ∑ a : A, (Representation.character V.ρ) a *
        (Representation.character V.ρ) a⁻¹ =
        (0 : ℂ) := by simpa [hne] using horth
    exact one_ne_zero (hself.symm.trans hzero)
  let e : Representation.Equiv V.ρ ρ' := Classical.choice hnon
  let T : Representation.IntertwiningMap V.ρ ρ' := e.toIntertwiningMap
  have hT : Function.Bijective T := e.toLinearEquiv.bijective
  have hTcomp (a : A) : T.toLinearMap ∘ₗ V.ρ a = V.ρ (α a) ∘ₗ T.toLinearMap := by
    exact T.isIntertwining' a
  have htrace (a : A) : LinearMap.trace ℂ V (T.toLinearMap ∘ₗ V.ρ a) =
      LinearMap.trace ℂ V T.toLinearMap := by
    obtain ⟨b, rfl⟩ := MonoidHom.FixedPointFree.commutatorMap_surjective
      (φ := α) hα a
    simp only [MonoidHom.commutatorMap_apply, div_eq_mul_inv, map_mul]
    change LinearMap.trace ℂ V (T.toLinearMap ∘ₗ V.ρ b ∘ₗ V.ρ ((α b)⁻¹)) =
      LinearMap.trace ℂ V T.toLinearMap
    rw [← LinearMap.comp_assoc]
    rw [hTcomp b]
    change LinearMap.trace ℂ V ((V.ρ (α b) * T.toLinearMap) * V.ρ ((α b)⁻¹)) =
      LinearMap.trace ℂ V T.toLinearMap
    rw [LinearMap.trace_mul_cycle]
    simp only [← map_mul, inv_mul_cancel, map_one, one_mul]
  have htrace_mul (m n : A) :
      LinearMap.trace ℂ V ((V.ρ n * T.toLinearMap) * V.ρ m) =
        LinearMap.trace ℂ V (V.ρ n * T.toLinearMap) := by
    calc
      _ = LinearMap.trace ℂ V ((V.ρ m * V.ρ n) * T.toLinearMap) := by
        rw [LinearMap.trace_mul_cycle]
      _ = LinearMap.trace ℂ V ((T.toLinearMap * V.ρ m) * V.ρ n) := by
        rw [LinearMap.trace_mul_cycle]
      _ = LinearMap.trace ℂ V (T.toLinearMap * (V.ρ m * V.ρ n)) := by
        rw [mul_assoc]
      _ = LinearMap.trace ℂ V (T.toLinearMap * V.ρ (m * n)) := by
        rw [← map_mul]
      _ = LinearMap.trace ℂ V T.toLinearMap := htrace (m * n)
      _ = LinearMap.trace ℂ V (T.toLinearMap * V.ρ n) := (htrace n).symm
      _ = LinearMap.trace ℂ V (V.ρ n * T.toLinearMap) := by
        rw [LinearMap.trace_mul_comm]
  have hgroup (m : A) (a : MonoidAlgebra ℂ A) :
      LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ a *
        (T.toLinearMap * V.ρ m - T.toLinearMap)) = 0 := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
        simp only [map_add, add_mul, ha, hb, add_zero]
    | single g c =>
        have hz : LinearMap.trace ℂ V (V.ρ g *
            (T.toLinearMap * V.ρ m - T.toLinearMap)) = 0 := by
          rw [mul_sub, map_sub, ← mul_assoc, htrace_mul m g]
          exact sub_self _
        simp [Representation.asAlgebraHom_single, smul_mul_assoc, hz]
  have has : Function.Surjective (Representation.asAlgebraHom V.ρ) :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible
      V.ρ hρ
  have htrace_all (m : A) (U : Module.End ℂ V) :
      LinearMap.trace ℂ V (U * (T.toLinearMap * V.ρ m - T.toLinearMap)) = 0 := by
    obtain ⟨a, rfl⟩ := has U
    exact hgroup m a
  have hzero (m : A) : T.toLinearMap * V.ρ m - T.toLinearMap = 0 := by
    apply LinearMap.ext
    intro v
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro f
    have h := htrace_all m (f.smulRight v)
    change LinearMap.trace ℂ V ((f.comp
      (T.toLinearMap * V.ρ m - T.toLinearMap)).smulRight v) = 0 at h
    rw [LinearMap.trace_smulRight] at h
    exact h
  have hconst (m : A) : T.toLinearMap ∘ₗ V.ρ m = T.toLinearMap := by
    simpa only [Module.End.mul_eq_comp] using sub_eq_zero.mp (hzero m)
  have hαfix (m : A) : V.ρ (α m) = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hT.2 v
    have hi := congrArg (fun f => f w) (hTcomp m)
    have hc := congrArg (fun f => f w) (hconst m)
    calc
      V.ρ (α m) v = V.ρ (α m) (T w) := by rw [hw]
      _ = T (V.ρ m w) := hi.symm
      _ = T w := hc
      _ = v := hw
  constructor
  intro a
  obtain ⟨m, rfl⟩ := α.surjective a
  exact hαfix m

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_NonabelianInvariant

section ScratchSource_NonabelianDichotomy

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory
open D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti
open D5.S3.FiniteGroups.CharacterDegreeDivisibility.TauCeti
open D5.S3.FiniteGroups.CliffordConstituents.TauCeti
open D5.S3.FiniteGroups.CliffordDecomposition.TauCeti
open D5.S3.FiniteGroups.InducedCharacterFormula.TauCeti

variable {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]

private theorem inertia_eq_of_fixedPointFree_nonabelian
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (V : FDRep ℂ N) [Simple V] (hV : ¬ Representation.IsTrivial V.ρ) :
    (MulAction.stabilizer K (toSkeleton V)) = N := by
  apply le_antisymm
  · intro g hg
    by_contra hgN
    apply hV
    apply trivial_of_character_invariant_fixedPointFree (MulAut.conjNormal g⁻¹)
      (hfix g⁻¹ (fun h => hgN (by simpa using N.inv_mem h))) V
    · intro n
      convert char_conj_eq_of_mem_inertia hg n using 1
      congr 1
      apply Subtype.ext
      simp
  · exact le_inertia V

private theorem restriction_trivial_of_clifford_constituent_trivial_nonabelian
    (W : FDRep ℂ K) (V : FDRep ℂ N) [Finite (K ⧸ (MulAction.stabilizer K (toSkeleton V)))]
    (e : ℕ) (iso : ((Action.res (FGModuleCat ℂ) (N).subtype).obj W) ≅
      (D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V e))
    (hdim : Module.finrank ℂ W = e *
      ((MulAction.stabilizer K (toSkeleton V))).index * Module.finrank ℂ V)
    [Representation.IsTrivial V.ρ] :
    Representation.IsTrivial (W.ρ.comp N.subtype) := by
  classical
  letI : Fintype (K ⧸ (MulAction.stabilizer K (toSkeleton V))) := Fintype.ofFinite _
  constructor
  intro n
  apply (_root_.D5.S3.FiniteGroups.InducedCharacterFormula.Representation.char_eq_finrank_iff
    (W.ρ.comp N.subtype) (isOfFinOrder_of_finite n)).mp
  have hc := congrFun (FDRep.char_iso iso) n
  rw [_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.character_actionRes,
    _root_.D5.S3.FiniteGroups.CliffordDecomposition.FDRep.character_cliffordSum,
    finsum_eq_sum_of_fintype] at hc
  have hv (q : K ⧸ (MulAction.stabilizer K (toSkeleton V))) :
      ((conjNormalFDRepFunctor (Quotient.out q)).obj V).character n =
        (Module.finrank ℂ V : ℂ) := by
    rw [char_conjNormalFDRep]
    change LinearMap.trace ℂ V (V.ρ _) = _
    rw [Representation.isTrivial_def, LinearMap.trace_id]
  simp_rw [hv] at hc
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hc
  change W.character (N.subtype n) = (Module.finrank ℂ W : ℂ)
  rw [hc, hdim]
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  push_cast
  ring

/-
Escape audit unfinished under https://github.com/the-omega-institute/trureturing/issues/27844.
The single same-delivery source-level Reg attempt is retained in
`.scratch/delivery-repair/nonabelian-reg-attempt.lean`; no `declared_validated`
registration is claimed.
-/

/- Fixed-point-free conjugation on a normal subgroup gives the nonabelian degree dichotomy. -/
theorem degree_dvd_or_index_dvd_of_fixedPointFree_nonabelian
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (W : FDRep ℂ K) [Simple W] :
    Module.finrank ℂ W ∣ N.index ∨ N.index ∣ Module.finrank ℂ W := by
  obtain ⟨V, hV, hf, e, he, ⟨iso⟩, hdim⟩ :=
    (D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank (N := N) W)
  letI := hV
  letI := hf
  by_cases ht : Representation.IsTrivial V.ρ
  · letI := ht
    letI := restriction_trivial_of_clifford_constituent_trivial_nonabelian N W V e iso hdim
    left
    simpa [Subgroup.index_eq_card] using degree_dvd_quotient_card K N W
  · right
    rw [inertia_eq_of_fixedPointFree_nonabelian N hfix V ht] at hdim
    exact ⟨e * Module.finrank ℂ V, by rw [hdim]; ring⟩

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ScratchSource_NonabelianDichotomy

section ModularFrobeniusAction

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees
open CategoryTheory

/-- A simple representation equivalent to its twist by a fixed-point-free
 automorphism is trivial, in arbitrary characteristic. -/
theorem trivial_of_equiv_fixedPointFree_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k]
    {A : Type*} [Group A] [Finite A] (α : MulAut A)
    (hα : ∀ a : A, α a = a → a = 1)
    (V : FDRep k A) [Simple V]
    (e : Representation.Equiv V.ρ (V.ρ.comp α.toMonoidHom)) :
    Representation.IsTrivial V.ρ := by
  classical
  let ρ' : Representation k A V := V.ρ.comp α.toMonoidHom
  have hρ : Representation.IsIrreducible V.ρ :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple V
  let T : Representation.IntertwiningMap V.ρ ρ' := e.toIntertwiningMap
  have hT : Function.Bijective T := e.toLinearEquiv.bijective
  have hTcomp (a : A) : T.toLinearMap ∘ₗ V.ρ a = V.ρ (α a) ∘ₗ T.toLinearMap := by
    exact T.isIntertwining' a
  have htrace (a : A) : LinearMap.trace k V (T.toLinearMap ∘ₗ V.ρ a) =
      LinearMap.trace k V T.toLinearMap := by
    obtain ⟨b, rfl⟩ := MonoidHom.FixedPointFree.commutatorMap_surjective
      (φ := α) hα a
    simp only [MonoidHom.commutatorMap_apply, div_eq_mul_inv, map_mul]
    change LinearMap.trace k V (T.toLinearMap ∘ₗ V.ρ b ∘ₗ V.ρ ((α b)⁻¹)) =
      LinearMap.trace k V T.toLinearMap
    rw [← LinearMap.comp_assoc]
    rw [hTcomp b]
    change LinearMap.trace k V ((V.ρ (α b) * T.toLinearMap) * V.ρ ((α b)⁻¹)) =
      LinearMap.trace k V T.toLinearMap
    rw [LinearMap.trace_mul_cycle]
    simp only [← map_mul, inv_mul_cancel, map_one, one_mul]
  have htrace_mul (m n : A) :
      LinearMap.trace k V ((V.ρ n * T.toLinearMap) * V.ρ m) =
        LinearMap.trace k V (V.ρ n * T.toLinearMap) := by
    calc
      _ = LinearMap.trace k V ((V.ρ m * V.ρ n) * T.toLinearMap) := by
        rw [LinearMap.trace_mul_cycle]
      _ = LinearMap.trace k V ((T.toLinearMap * V.ρ m) * V.ρ n) := by
        rw [LinearMap.trace_mul_cycle]
      _ = LinearMap.trace k V (T.toLinearMap * (V.ρ m * V.ρ n)) := by
        rw [mul_assoc]
      _ = LinearMap.trace k V (T.toLinearMap * V.ρ (m * n)) := by
        rw [← map_mul]
      _ = LinearMap.trace k V T.toLinearMap := htrace (m * n)
      _ = LinearMap.trace k V (T.toLinearMap * V.ρ n) := (htrace n).symm
      _ = LinearMap.trace k V (V.ρ n * T.toLinearMap) := by
        rw [LinearMap.trace_mul_comm]
  have hgroup (m : A) (a : MonoidAlgebra k A) :
      LinearMap.trace k V (Representation.asAlgebraHom V.ρ a *
        (T.toLinearMap * V.ρ m - T.toLinearMap)) = 0 := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
        simp only [map_add, add_mul, ha, hb, add_zero]
    | single g c =>
        have hz : LinearMap.trace k V (V.ρ g *
            (T.toLinearMap * V.ρ m - T.toLinearMap)) = 0 := by
          rw [mul_sub, map_sub, ← mul_assoc, htrace_mul m g]
          exact sub_self _
        simp [Representation.asAlgebraHom_single, hz]
  have has : Function.Surjective (Representation.asAlgebraHom V.ρ) :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.asAlgebraHom_surjective_of_isIrreducible
      V.ρ hρ
  have htrace_all (m : A) (U : Module.End k V) :
      LinearMap.trace k V (U * (T.toLinearMap * V.ρ m - T.toLinearMap)) = 0 := by
    obtain ⟨a, rfl⟩ := has U
    exact hgroup m a
  have hzero (m : A) : T.toLinearMap * V.ρ m - T.toLinearMap = 0 := by
    apply LinearMap.ext
    intro v
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro f
    have h := htrace_all m (f.smulRight v)
    change LinearMap.trace k V ((f.comp
      (T.toLinearMap * V.ρ m - T.toLinearMap)).smulRight v) = 0 at h
    rw [LinearMap.trace_smulRight] at h
    exact h
  have hconst (m : A) : T.toLinearMap ∘ₗ V.ρ m = T.toLinearMap := by
    simpa only [Module.End.mul_eq_comp] using sub_eq_zero.mp (hzero m)
  constructor
  intro a
  apply LinearMap.ext
  intro v
  apply hT.1
  exact congrArg (fun f => f v) (hconst a)

/-- Character invariance under a fixed-point-free automorphism forces a simple
 representation to be trivial over an algebraically closed field. -/
theorem trivial_of_character_invariant_fixedPointFree_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k]
    {A : Type*} [Group A] [Finite A] (α : MulAut A)
    (hα : ∀ a : A, α a = a → a = 1)
    (V : FDRep k A) [Simple V]
    (hχ : ∀ a : A, V.character (α a) = V.character a) :
    Representation.IsTrivial V.ρ := by
  let ρ' : Representation k A V := V.ρ.comp α.toMonoidHom
  have hρ : Representation.IsIrreducible V.ρ :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple V
  have hρ' : Representation.IsIrreducible ρ' :=
    (_root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.isIrreducible_comp_surjective_iff
      α.toMonoidHom α.surjective V.ρ).2 hρ
  have hchar : _root_.Representation.character V.ρ = ρ'.character := by
    funext a
    exact (hχ a).symm
  obtain ⟨e⟩ :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.Representation.nonempty_equiv_of_character_eq_of_isIrreducible
      V.ρ ρ' hρ hρ' hchar
  exact trivial_of_equiv_fixedPointFree_of_isAlgClosed α hα V e

open D5.S3.FiniteGroups.CliffordConstituents.TauCeti

section CliffordAction
variable {k : Type*} [Field k]
variable {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]

private theorem inertia_eq_of_fixedPointFree_of_isAlgClosed [IsAlgClosed k]
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (V : FDRep k N) [Simple V] (hV : ¬ Representation.IsTrivial V.ρ) :
    MulAction.stabilizer K (toSkeleton V) = N := by
  apply le_antisymm
  · intro g hg
    by_contra hgN
    apply hV
    obtain ⟨i⟩ := mem_inertia_iff.mp hg
    obtain ⟨e⟩ := nonempty_fdRepIso_iff.mp ⟨i.symm⟩
    have he : Representation.Equiv V.ρ
        (V.ρ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) := e
    exact trivial_of_equiv_fixedPointFree_of_isAlgClosed (MulAut.conjNormal g⁻¹)
      (hfix g⁻¹ (fun h => hgN (by simpa using N.inv_mem h))) V he
  · exact le_inertia V

private theorem restriction_trivial_of_clifford_constituent_trivial_generic
    (W : FDRep k K) (V : FDRep k N)
    [Finite (K ⧸ MulAction.stabilizer K (toSkeleton V))]
    (e : ℕ)
    (iso : ((Action.res (FGModuleCat k) N.subtype).obj W) ≅
      D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V e)
    [Representation.IsTrivial V.ρ] :
    Representation.IsTrivial (W.ρ.comp N.subtype) := by
  classical
  let M := (q : K ⧸ MulAction.stabilizer K (toSkeleton V)) → Fin e →
    Representation.asModule ((conjNormalFDRepFunctor (Quotient.out q)).obj V).ρ
  let ρM : Representation k N M := Representation.ofModule' (k := k) (G := N) M
  have hM (n : N) (x : M) : ρM n x = x := by
    funext q j
    let U : FDRep k N := (conjNormalFDRepFunctor (Quotient.out q)).obj V
    apply (_root_.Representation.asModuleEquiv U.ρ).injective
    change (_root_.Representation.asModuleEquiv U.ρ) (MonoidAlgebra.single n (1 : k) • x q j) =
      (_root_.Representation.asModuleEquiv U.ρ) (x q j)
    rw [Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, one_smul]
    change V.ρ (MulAut.conjNormal (Quotient.out q)⁻¹ n)
      ((_root_.Representation.asModuleEquiv U.ρ) (x q j)) = (_root_.Representation.asModuleEquiv U.ρ) (x q j)
    exact Representation.isTrivial_apply V.ρ _ _
  have eSum : Representation.Equiv
      (D5.S3.FiniteGroups.CliffordDecomposition.FDRep.cliffordSum V e).ρ ρM :=
    _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.ofShrinkEquiv ρM
  obtain ⟨eRes⟩ := nonempty_fdRepIso_iff.mp ⟨iso⟩
  let E : Representation.Equiv (W.ρ.comp N.subtype) ρM := eRes.trans eSum
  constructor
  intro n
  apply LinearMap.ext
  intro w
  apply E.toLinearEquiv.injective
  change E ((W.ρ.comp N.subtype) n w) = E w
  calc
    _ = ρM n (E w) :=
      LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' n) w
    _ = E w := hM n (E w)

end CliffordAction

/-- Fixed-point-free outside conjugation forces trivial normal action or index
 divisibility of a simple representation's dimension, in arbitrary characteristic. -/
theorem trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k]
    {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (W : FDRep k K) [Simple W] :
    Representation.IsTrivial (W.ρ.comp N.subtype) ∨
      N.index ∣ Module.finrank k W := by
  obtain ⟨V, hV, hf, e, -, ⟨iso⟩, hdim⟩ :=
    D5.S3.FiniteGroups.InducedCharacterFormula.FDRep.clifford_restrict_finrank (N := N) W
  letI := hV
  letI := hf
  by_cases ht : Representation.IsTrivial V.ρ
  · letI := ht
    exact Or.inl (restriction_trivial_of_clifford_constituent_trivial_generic N W V e iso)
  · right
    rw [inertia_eq_of_fixedPointFree_of_isAlgClosed N hfix V ht] at hdim
    exact ⟨e * Module.finrank k V, by rw [hdim]; ring⟩

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
end ModularFrobeniusAction



namespace ArbitraryFieldDescent

open scoped TensorProduct

variable {k E G V : Type*} [Field k] [Field E] [Algebra k E]
  [Group G] [AddCommGroup V] [Module k V]

/-- Scalar extension of a representation, with the group acting on the second tensor factor. -/
noncomputable def extRep (ρ : Representation k G V) :
    Representation E G (E ⊗[k] V) where
  toFun g := (ρ g).baseChange E
  map_one' := by simp
  map_mul' g h := by simp [← LinearMap.baseChange_mul]

@[simp] theorem extRep_apply_tmul (ρ : Representation k G V) (g : G) (e : E) (v : V) :
    extRep ρ g (e ⊗ₜ[k] v) = e ⊗ₜ[k] ρ g v := by
  rfl

@[simp] theorem extRep_finrank [Module.Finite k V] (ρ : Representation k G V) :
    Module.finrank E (E ⊗[k] V) = Module.finrank k V := by
  exact Module.finrank_baseChange
section GenericDescent
universe u
variable {R E M : Type u} [Ring R] [Field E] [Algebra E R]
  [AddCommGroup M] [Module R M] [Module E M] [IsScalarTower E R M]
  [Module.Finite E M]

/-- Finite-dimensional module dimensions are divisible by `d` when every simple
submodule has dimension divisible by `d`. -/
theorem finrank_dvd_of_simple_submodules (d : ℕ)
    (hbase : ∀ {X : Type u} [AddCommGroup X] [Module R X] [Module E X]
      [IsScalarTower E R X] [Module.Finite E X]
      (S : Submodule R X), IsSimpleModule R S →
        d ∣ Module.finrank E (S.restrictScalars E)) :
    d ∣ Module.finrank E M := by
  classical
  by_cases hzero : Module.finrank E M = 0
  · simp [hzero]
  induction hdim : Module.finrank E M using Nat.strong_induction_on generalizing M with
  | h n ih =>
    let p : Set ℕ := {m | ∃ S : Submodule R M, S ≠ ⊥ ∧
      m = Module.finrank E (S.restrictScalars E)}
    have hp : p.Nonempty := by
      refine ⟨Module.finrank E M, ⊤, ?_, ?_⟩
      · intro htop
        apply hzero
        apply (Module.finrank_zero_iff).2
        refine ⟨fun x y => ?_⟩
        have hxR : x ∈ (⊥ : Submodule R M) := htop ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule R M))
        have hyR : y ∈ (⊥ : Submodule R M) := htop ▸ (Submodule.mem_top : y ∈ (⊤ : Submodule R M))
        have hx0 : x = 0 := by simpa using hxR
        have hy0 : y = 0 := by simpa using hyR
        exact hx0.trans hy0.symm
      · rw [Submodule.restrictScalars_top, finrank_top]

    obtain ⟨S, hSne, hSdim⟩ := Nat.sInf_mem hp
    have hSsimple : IsSimpleModule R S := by
      rw [isSimpleModule_iff_isAtom, isAtom_iff_le_of_ge]
      refine ⟨hSne, ?_⟩
      intro T hTne hTS
      by_contra hne
      have hlt : T.restrictScalars E < S.restrictScalars E := by
        refine lt_of_le_of_ne (Submodule.restrictScalars_mono E hTS) ?_
        intro heq
        have heq' : T = S := Submodule.restrictScalars_injective E _ _ heq
        exact hne (heq'.symm ▸ le_rfl)
      have hdimlt : Module.finrank E (T.restrictScalars E) <
          Module.finrank E (S.restrictScalars E) := by
        exact lt_of_le_of_ne (Submodule.finrank_mono
          (Submodule.restrictScalars_mono E hTS)) (by
            intro heq
            have heq' : T = S := Submodule.restrictScalars_injective E _ _
              (Submodule.eq_of_le_of_finrank_eq
                (Submodule.restrictScalars_mono E hTS) heq)
            exact hne (heq'.symm ▸ le_rfl))
      have hmem : Module.finrank E (T.restrictScalars E) ∈ p := ⟨T, hTne, rfl⟩
      exact (Nat.not_lt_of_ge (Nat.sInf_le hmem)) (by simpa [← hSdim] using hdimlt)
    have hdS : d ∣ Module.finrank E (S.restrictScalars E) := hbase (X := M) S hSsimple
    have hquotlt : Module.finrank E (M ⧸ S) < Module.finrank E M := by
      have hadd := (S.restrictScalars E).finrank_quotient_add_finrank
      have hpos : 0 < Module.finrank E (S.restrictScalars E) := by
        apply Nat.pos_of_ne_zero
        intro hz
        have hbot : S.restrictScalars E = (⊥ : Submodule E M) :=
          (Submodule.finrank_eq_zero).mp hz
        exact hSne (Submodule.restrictScalars_injective E _ _ hbot)
      have hle : Module.finrank E (M ⧸ S.restrictScalars E) +
          Module.finrank E (S.restrictScalars E) ≤ Module.finrank E M := le_of_eq hadd
      have hlt' : Module.finrank E (M ⧸ S.restrictScalars E) < Module.finrank E M := by
        omega
      rw [← LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv E S)]
      exact hlt'
    obtain ⟨c, hc⟩ := hdS
    have hdQ : d ∣ Module.finrank E (M ⧸ S) := by
      by_cases hqzero : Module.finrank E (M ⧸ S) = 0
      · simp [hqzero]
      · apply ih (M := M ⧸ S) (Module.finrank E (M ⧸ S))
        · exact hdim ▸ hquotlt
        · exact hqzero
        · rfl
    obtain ⟨q, hq⟩ := hdQ
    have hadd := (S.restrictScalars E).finrank_quotient_add_finrank
    have heq : Module.finrank E (M ⧸ S) + Module.finrank E (S.restrictScalars E) =
        Module.finrank E M := by
      rw [← LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv E S)]
      exact hadd
    refine ⟨q + c, ?_⟩
    calc
      n = Module.finrank E M := hdim.symm
      _ = Module.finrank E (M ⧸ S) +
          Module.finrank E (S.restrictScalars E) := heq.symm
      _ = d * q + d * c := by rw [hq, hc]
      _ = d * (q + c) := by ring
end GenericDescent

end ArbitraryFieldDescent

namespace D5.S3.FiniteGroups.FrobeniusCharacterDegrees

open CategoryTheory
open scoped TensorProduct
open scoped _root_.MonoidAlgebra

variable {k E G V : Type*} [Field k] [Field E] [Algebra k E]
  [Group G] [AddCommGroup V] [Module k V]

private noncomputable def originalModule (ρ : Representation k G V) :
    Module (MonoidAlgebra k G) (E ⊗[k] V) := by
  let ρE : Representation E G (E ⊗[k] V) :=
    _root_.ArbitraryFieldDescent.extRep ρ
  let M := ρE.asModule
  exact Module.compHom M (MonoidAlgebra.mapRingHom G (algebraMap k E))

private theorem pure_image_linear
    (ρ : Representation k G V) (c : E) :
    letI : Module (MonoidAlgebra k G) (E ⊗[k] V) := originalModule ρ
    ∃ f : ρ.asModule →ₗ[MonoidAlgebra k G] (E ⊗[k] V),
      ∀ v, f v = c ⊗ₜ[k] (ρ.asModuleEquiv v : V) := by
  let ρE : Representation E G (E ⊗[k] V) :=
    _root_.ArbitraryFieldDescent.extRep ρ
  let M := ρE.asModule
  letI : Module k M := Module.compHom M (algebraMap k E)
  letI : IsScalarTower k E M := IsScalarTower.of_compHom k E M
  letI : Module (MonoidAlgebra k G) M :=
    Module.compHom M (MonoidAlgebra.mapRingHom G (algebraMap k E))
  let f₀ : V →ₗ[k] M :=
    (ρE.asModuleEquiv.symm.restrictScalars k).comp (TensorProduct.mk k E V c)
  let f : ρ.asModule →ₗ[MonoidAlgebra k G] M :=
    { toFun := fun v => f₀ (ρ.asModuleEquiv v)
      map_add' := by
        intro x y
        change f₀ (ρ.asModuleEquiv x + ρ.asModuleEquiv y) = _
        rw [f₀.map_add]
      map_smul' := by
        intro a v
        induction a using MonoidAlgebra.induction_linear with
        | zero => simp [f₀]
        | add a b ha hb =>
            rw [add_smul, ρ.asModuleEquiv.map_add, f₀.map_add, ha, hb]
            change _ = (a + b) • (f₀ (ρ.asModuleEquiv v) : M)
            simpa only [RingHom.id_apply] using
              (add_smul a b (f₀ (ρ.asModuleEquiv v))).symm
        | single g r =>
            apply ρE.asModuleEquiv.injective
            change c ⊗ₜ[k] (ρ.asModuleEquiv (MonoidAlgebra.single g r • v)) =
              ρE.asModuleEquiv ((MonoidAlgebra.mapRingHom G (algebraMap k E)
                (MonoidAlgebra.single g r)) • f₀ (ρ.asModuleEquiv v))
            rw [Representation.asModuleEquiv_map_smul,
              MonoidAlgebra.mapRingHom_single,
              Representation.asModuleEquiv_map_smul]
            have hf₀ (x : V) : ρE.asModuleEquiv (f₀ x) = c ⊗ₜ[k] x := by
              rfl
            have hact (x : V) : ρE g (c ⊗ₜ[k] x) = c ⊗ₜ[k] ρ g x := by
              exact _root_.ArbitraryFieldDescent.extRep_apply_tmul ρ g c x
            simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply]
            rw [hf₀, hact]
            rw [TensorProduct.tmul_smul]
            simp [Algebra.smul_def] }
  refine ⟨f, ?_⟩
  intro v
  rfl

private theorem ext_isotypic
    (ρ : Representation k G V)
    (hρ : IsSimpleModule (MonoidAlgebra k G) ρ.asModule) :
    letI : Module (MonoidAlgebra k G) (E ⊗[k] V) := originalModule ρ
    IsSemisimpleModule (MonoidAlgebra k G) (E ⊗[k] V) ∧
      IsIsotypicOfType (MonoidAlgebra k G) (E ⊗[k] V)
        ρ.asModule := by
  let S0 : Submodule (MonoidAlgebra k G) ρ.asModule := ⊤
  letI : IsSimpleModule (MonoidAlgebra k G) S0 :=
    IsSimpleModule.congr (Submodule.topEquiv : S0 ≃ₗ[MonoidAlgebra k G] ρ.asModule)
  letI : Module (MonoidAlgebra k G) (E ⊗[k] V) := originalModule ρ
  have htop : isotypicComponent (MonoidAlgebra k G) (E ⊗[k] V) S0 = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    induction x using TensorProduct.induction_on with
    | zero => exact (isotypicComponent (MonoidAlgebra k G) (E ⊗[k] V) S0).zero_mem
    | tmul c v =>
        obtain ⟨f, hf⟩ := pure_image_linear (ρ := ρ) c
        have hle := Submodule.map_le_isotypicComponent S0 f
        let y : ρ.asModule := ρ.asModuleEquiv.symm v
        have hy : y ∈ S0 := by simp [S0]
        have hmem : f y ∈ S0.map f := Submodule.mem_map.mpr ⟨y, hy, rfl⟩
        apply hle
        simpa [hf, y] using hmem
    | add x y hx hy =>
        exact (isotypicComponent (MonoidAlgebra k G) (E ⊗[k] V) S0).add_mem hx hy
  constructor
  · let C := isotypicComponent (MonoidAlgebra k G) (E ⊗[k] V) S0
    letI : IsSemisimpleModule (MonoidAlgebra k G) C := by
      dsimp [C]
      infer_instance
    apply IsSemisimpleModule.of_surjective (Submodule.subtype C)
    intro x
    have hx : x ∈ C := by
      change x ∈ isotypicComponent (MonoidAlgebra k G) (E ⊗[k] V) S0
      rw [htop]
      trivial
    exact ⟨⟨x, hx⟩, rfl⟩
  · exact (IsIsotypicOfType.of_isotypicComponent_eq_top htop).of_linearEquiv_type
      (Submodule.topEquiv : S0 ≃ₗ[MonoidAlgebra k G] ρ.asModule)

private def supported
    (A B S0 X : Type*) [Ring A] [Ring B]
    [AddCommGroup X] [Module B X]
    [AddCommGroup S0] [Module A S0] (φ : A →+* B) : Prop :=
  letI : Module A X := Module.compHom X φ
  IsSemisimpleModule A X ∧ IsIsotypicOfType A X S0

private theorem supported_submodule
    {A B S0 X : Type*} [Ring A] [Ring B]
    [AddCommGroup X] [Module B X]
    [AddCommGroup S0] [Module A S0]
    (φ : A →+* B) (hX : supported A B S0 X φ) (N : Submodule B X) :
    supported A B S0 N φ := by
  letI : Module A X := Module.compHom X φ
  letI : Module A N := Module.compHom N φ
  dsimp [supported] at hX ⊢
  let f : N →ₗ[A] X :=
    { toFun := fun x => x.1
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  letI : IsSemisimpleModule A X := hX.1
  constructor
  · exact IsSemisimpleModule.of_injective f N.subtype_injective
  · exact hX.2.of_injective f N.subtype_injective

private theorem supported_quotient
    {A B S0 X : Type*} [Ring A] [Ring B]
    [AddCommGroup X] [Module B X]
    [AddCommGroup S0] [Module A S0]
    (φ : A →+* B) (hX : supported A B S0 X φ) (N : Submodule B X) :
    supported A B S0 (X ⧸ N) φ := by
  letI : Module A X := Module.compHom X φ
  letI : Module A (X ⧸ N) := Module.compHom (X ⧸ N) φ
  dsimp [supported] at hX ⊢
  let q : X →ₗ[A] X ⧸ N :=
    { toFun := Submodule.mkQ N
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  letI : IsSemisimpleModule A X := hX.1
  have hsem : IsSemisimpleModule A (X ⧸ N) :=
    IsSemisimpleModule.of_surjective q (Submodule.mkQ_surjective N)
  have hiso : IsIsotypicOfType A (X ⧸ N) S0 := by
    intro S hS
    letI : IsSimpleModule A S := hS
    obtain ⟨g, hg⟩ := IsSemisimpleModule.lifting_property q
      (Submodule.mkQ_surjective N) S.subtype
    have hgi : Function.Injective g := by
      intro x y hxy
      apply S.subtype_injective
      exact (LinearMap.congr_fun hg x).symm.trans
        ((congrArg q hxy).trans (LinearMap.congr_fun hg y))
    have hSiso : IsIsotypicOfType A S S0 := hX.2.of_injective g hgi
    let T : Submodule A S := ⊤
    letI : IsSimpleModule A T := IsSimpleModule.congr
      (Submodule.topEquiv : T ≃ₗ[A] S)
    obtain ⟨e⟩ := hSiso T
    exact ⟨(Submodule.topEquiv : T ≃ₗ[A] S).symm.trans e⟩
  exact ⟨hsem, hiso⟩

universe uA uB uE uS uX

private theorem finite_length_dvd_of_supported
    {A : Type uA} {B : Type uB} {E : Type uE} {S0 : Type uS} {X : Type uX}
    [Ring A] [Ring B] [Field E]
    [AddCommGroup X] [Module B X] [instE : Module E X] [Module E B]
    [AddCommGroup S0] [Module A S0] (φ : A →+* B) (d : ℕ)
    (hfactor : ∀ {Y : Type uX} [AddCommGroup Y] [Module B Y] [Module E Y]
      [IsScalarTower E B Y] [Module.Finite E Y] [IsSimpleModule B Y],
      supported A B S0 Y φ → d ∣ Module.finrank E Y)
    (hlen : IsFiniteLength B X)
    [instTower : IsScalarTower E B X] [instFinite : Module.Finite E X]
    (hX : supported A B S0 X φ) : d ∣ Module.finrank E X := by
  revert hX instFinite instTower instE
  induction hlen with
  | of_subsingleton =>
      intro instE instTower instFinite hX
      rw [Module.finrank_zero_of_subsingleton]
      exact dvd_zero d
  | @of_simple_quotient X _ _ N _ _ ih =>
      intro instE instTower instFinite hX
      letI : SMul E N :=
        ⟨fun e x => ⟨e • (x : X), (N.restrictScalars E).smul_mem e x.property⟩⟩
      letI : Module E N := Module.ofMinimalAxioms
        (fun e x y => by
          apply Subtype.ext
          exact smul_add e (x : X) (y : X))
        (fun e f x => by
          apply Subtype.ext
          exact add_smul e f (x : X))
        (fun e f x => by
          apply Subtype.ext
          exact mul_smul e f (x : X))
        (fun x => by
          apply Subtype.ext
          exact one_smul E (x : X))
      letI : IsScalarTower E B N :=
        { smul_assoc := by
            intro e b x
            apply Subtype.ext
            exact smul_assoc e b (x : X) }
      let f : N →ₗ[E] X :=
        { toFun := fun x => x.1
          map_add' := by intro x y; rfl
          map_smul' := by intro e x; rfl }
      letI : Module.Finite E N := Module.Finite.of_injective f N.subtype_injective
      have hN : d ∣ Module.finrank E N :=
        ih (supported_submodule φ hX N)
      have hQ : d ∣ Module.finrank E (X ⧸ N) :=
        hfactor (Y := X ⧸ N) (supported_quotient φ hX N)
      obtain ⟨q, hq⟩ := hN
      obtain ⟨c, hc⟩ := hQ
      have hadd := (N.restrictScalars E).finrank_quotient_add_finrank
      have heq : Module.finrank E (X ⧸ N) + Module.finrank E N =
          Module.finrank E X := by
        rw [← LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv E N)]
        exact hadd
      refine ⟨q + c, ?_⟩
      calc
        Module.finrank E X = Module.finrank E (X ⧸ N) + Module.finrank E N := heq.symm
        _ = d * c + d * q := by rw [hc, hq]
        _ = d * (q + c) := by ring

theorem trivial_restriction_or_index_dvd_of_fixedPointFree
    {k : Type*} [Field k]
    {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hfix : ∀ g : K, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1)
    (W : FDRep k K) [Simple W] :
    Representation.IsTrivial (W.ρ.comp N.subtype) ∨
      N.index ∣ Module.finrank k W := by
  classical
  by_cases htriv : Representation.IsTrivial (W.ρ.comp N.subtype)
  · exact Or.inl htriv
  · right
    let E := AlgebraicClosure k
    let A := MonoidAlgebra k K
    let B := MonoidAlgebra E K
    let φ : A →+* B := MonoidAlgebra.mapRingHom K (algebraMap k E)
    let ρE : Representation E K (E ⊗[k] W) :=
      _root_.ArbitraryFieldDescent.extRep W.ρ
    let S0 : Submodule A (Representation.asModule W.ρ) := ⊤
    letI : IsSimpleModule A (Representation.asModule W.ρ) := by
      rw [← Representation.irreducible_iff_isSimpleModule_asModule]
      exact _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.isIrreducible_of_simple W
    letI : IsSimpleModule A S0 :=
      IsSimpleModule.congr
        (Submodule.topEquiv : S0 ≃ₗ[A] Representation.asModule W.ρ)
    letI : Module E (Representation.asModule ρE) := inferInstance
    letI : Module B (E ⊗[k] W) := ρE.instModuleMonoidAlgebraAsModule
    letI : IsScalarTower E B (E ⊗[k] W) := by
      exact (inferInstance : IsScalarTower E (MonoidAlgebra E K)
        (Representation.asModule ρE))
    letI : Module A (E ⊗[k] W) := originalModule W.ρ
    have hsupport : supported A B S0 (E ⊗[k] W) φ := by
      change IsSemisimpleModule A (E ⊗[k] W) ∧
        IsIsotypicOfType A (E ⊗[k] W) S0
      have h := ext_isotypic (E := E) W.ρ inferInstance
      exact ⟨h.1, h.2.of_linearEquiv_type
        (Submodule.topEquiv : S0 ≃ₗ[A] Representation.asModule W.ρ).symm⟩
    letI : Module.Finite k W := inferInstance
    letI : Module.Finite E (E ⊗[k] W) := inferInstance
    letI : Module.Finite E B := inferInstance
    letI : Module.Finite B (E ⊗[k] W) :=
      Module.Finite.of_restrictScalars_finite E B (E ⊗[k] W)
    letI : IsArtinianRing B := IsArtinianRing.of_finite E B
    have hlen : IsFiniteLength B (E ⊗[k] W) :=
      isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
    have hd : N.index ∣ Module.finrank E (E ⊗[k] W) := by
      refine finite_length_dvd_of_supported φ N.index ?_ hlen hsupport
      intro Y _ _ _ _ _ _ hY
      letI : Module A Y := Module.compHom Y φ
      change IsSemisimpleModule A Y ∧ IsIsotypicOfType A Y S0 at hY
      letI : IsSemisimpleModule A Y := hY.1
      letI : Nontrivial Y := IsSimpleModule.nontrivial B Y
      letI : Module (MonoidAlgebra E K) Y := inferInstance
      let ρY : Representation E K Y :=
        Representation.ofModule' (k := E) (G := K) Y
      let Xrep : FDRep E K := FDRep.of ρY
      letI : IsSimpleModule (MonoidAlgebra E K) Y := by
        change IsSimpleModule B Y
        infer_instance
      have hρY_smul (r : MonoidAlgebra E K) (x : Y) :
          ρY.asAlgebraHom r x = r • x := by
        induction r using MonoidAlgebra.induction_on with
        | of g =>
            simp [ρY, Representation.ofModule', Representation.asAlgebraHom_of]
        | add r s hr hs =>
            simp only [map_add, LinearMap.add_apply, add_smul, hr, hs]
        | smul c r hr =>
            rw [map_smul, LinearMap.smul_apply, hr]
            rw [← smul_assoc]
      let eY : ρY.asModule ≃ₗ[MonoidAlgebra E K] Y :=
        { toFun := fun x => x
          invFun := fun x => x
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl
          map_add' := by intro x y; rfl
          map_smul' := by intro r x; exact hρY_smul r x }
      have hirrY : Representation.IsIrreducible ρY := by
        letI : IsSimpleModule (MonoidAlgebra E K) ρY.asModule :=
          IsSimpleModule.congr eY
        exact (Representation.irreducible_iff_isSimpleModule_asModule ρY).mpr inferInstance
      letI : Representation.IsIrreducible Xrep.ρ := by
        change Representation.IsIrreducible ρY
        exact hirrY
      letI : Simple Xrep :=
        _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.FDRep.simple_of_isIrreducible Xrep
      obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A Y
      letI : IsSimpleModule A S := hS
      obtain ⟨e⟩ := hY.2 S
      let f : Representation.asModule W.ρ →ₗ[A] Y :=
        S.subtype.comp (e.symm.toLinearMap.comp
          (Submodule.topEquiv : S0 ≃ₗ[A] Representation.asModule W.ρ).symm.toLinearMap)
      have hf : Function.Injective f := by
        intro x y hxy
        apply (Submodule.topEquiv : S0 ≃ₗ[A] Representation.asModule W.ρ).symm.injective
        apply e.symm.injective
        apply S.subtype_injective
        exact hxy
      have hsplit :=
        trivial_restriction_or_index_dvd_of_fixedPointFree_of_isAlgClosed
          N hfix Xrep
      obtain htrivY | hdY := hsplit
      · exfalso
        apply htriv
        constructor
        intro n
        apply LinearMap.ext
        intro w
        apply (Representation.asModuleEquiv W.ρ).symm.injective
        apply hf
        change f ((Representation.asModuleEquiv W.ρ).symm
            (W.ρ (N.subtype n) w)) =
          f ((Representation.asModuleEquiv W.ρ).symm w)
        rw [Representation.asModuleEquiv_symm_map_rho]
        rw [map_smul]
        change φ (MonoidAlgebra.of k K (N.subtype n)) •
            f ((Representation.asModuleEquiv W.ρ).symm w) =
              f ((Representation.asModuleEquiv W.ρ).symm w)
        have hmap : φ (MonoidAlgebra.of k K (N.subtype n)) =
            MonoidAlgebra.of E K (N.subtype n) := by
          change MonoidAlgebra.mapRingHom K (algebraMap k E)
              (MonoidAlgebra.single (N.subtype n) 1) =
            MonoidAlgebra.single (N.subtype n) 1
          rw [MonoidAlgebra.mapRingHom_single]
          rfl
        rw [hmap]
        change ρY (N.subtype n) (f ((Representation.asModuleEquiv W.ρ).symm w)) =
          f ((Representation.asModuleEquiv W.ρ).symm w)
        letI : Representation.IsTrivial (ρY.comp N.subtype) := by
          simpa [Xrep] using htrivY
        simpa using
          (Representation.isTrivial_apply (ρY.comp N.subtype) n
            (f ((Representation.asModuleEquiv W.ρ).symm w)))
      · simpa [Xrep] using hdY
    have hdim : Module.finrank E (E ⊗[k] W) = Module.finrank k W := by
      exact _root_.ArbitraryFieldDescent.extRep_finrank W.ρ
    rw [hdim] at hd
    exact hd

end D5.S3.FiniteGroups.FrobeniusCharacterDegrees
