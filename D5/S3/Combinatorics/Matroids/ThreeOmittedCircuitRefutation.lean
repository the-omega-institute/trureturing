/- GID: D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.claim; result=D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.result; claim=D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.claim
   digest: Three separated omissions can jointly leave two independent elements killed by two, although independent replacement predicts a single cyclic group of order six. -/

import D5.S3.Combinatorics.Matroids.SparsePavingCircuitCoordinates
import D5.S3.Combinatorics.Matroids.RankTwoCircuitInvariantFactors
import Mathlib.Data.Fintype.Powerset

open Finset
open scoped Matroid
open D5.S3.Combinatorics.Matroids
open JointCircuitLiftingObstruction
open ParallelCircuitObstruction
open RationalJointCircuitImage (RationalResidue)
open RankTwoCircuitInvariantFactors (ResidueTorsion residueTorsion_equiv_zmod)

namespace D5.S3.Combinatorics.Matroids.ThreeOmittedCircuitRefutation

private abbrev V := Fin 6

private def firstPair : Finset V := {0, 1}
private def secondPair : Finset V := {2, 3}
private def thirdPair : Finset V := {4, 5}

private def holes : Set (Finset V) :=
  {firstPair ∪ secondPair, firstPair ∪ thirdPair, secondPair ∪ thirdPair}

private def allowed (F : Finset V) : Prop :=
  F.card = 4 ∧ F ∉ holes

private instance : DecidablePred allowed := by
  intro F
  unfold allowed holes
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  infer_instance

private def chosenBases (X : Set V) : Prop :=
  ∃ F : Finset V, (F : Set V) = X ∧ allowed F

private def exchangeTest : Prop :=
  ∀ X Y : Finset V, allowed X → allowed Y → ∀ a ∈ X \ Y,
    ∃ b ∈ Y \ X, allowed (insert b (X.erase a))

private def exchangeDecidable : Decidable exchangeTest :=
  Fintype.decidableForallFintype (p := fun X : Finset V => ∀ Y : Finset V,
    allowed X → allowed Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, allowed (insert b (X.erase a)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- The kernel checks every exchange for the concrete six-element core.
private theorem exchange : exchangeTest :=
  of_decide_eq_true (inst := exchangeDecidable) (by rfl)

private theorem allowed_nonempty : ∃ X : Set V, chosenBases X ∧ X.Finite := by
  let F : Finset V := {0, 1, 2, 4}
  exact ⟨F, ⟨F, rfl, by decide⟩, F.finite_toSet⟩

private def core : Matroid V := Matroid.ofExistsFiniteIsBase Set.univ chosenBases
  allowed_nonempty (by
    intro X Y hX hY a ha
    obtain ⟨F, rfl, hF⟩ := hX
    obtain ⟨G, rfl, hG⟩ := hY
    obtain ⟨b, hb, h⟩ := exchange F G hF hG a (by simpa using ha)
    exact ⟨b, by simpa using hb, insert b (F.erase a), by simp, h⟩)
  (fun _ _ => Set.subset_univ _)

private theorem core_ground : core.E = Set.univ := rfl

private theorem core_base (F : Finset V) :
    core.IsBase (F : Set V) ↔ F.card = 4 ∧ F ∉ holes := by
  change chosenBases (F : Set V) ↔ allowed F
  simp [chosenBases]

private theorem hole_size : ∀ H ∈ holes, (H : Finset V).card = 4 := by
  intro H hH
  simp only [holes, Set.mem_insert_iff, Set.mem_singleton_iff] at hH
  rcases hH with rfl | rfl | rfl <;> decide

private theorem sparse : holes.Pairwise (fun H J : Finset V => (H ∩ J).card + 2 ≤ 4) := by
  intro H hH J hJ hne
  simp only [holes, Set.mem_insert_iff, Set.mem_singleton_iff] at hH hJ
  rcases hH with rfl | rfl | rfl <;> rcases hJ with rfl | rfl | rfl
  all_goals first | exact (hne rfl).elim | decide

private def coefficients (u v : ZMod 2) (F : Finset V) : ZMod 2 :=
  if allowed F then
    if firstPair ⊆ F then u else if secondPair ⊆ F then v else u + v
  else 0

private abbrev parityRows : Prop :=
  ∀ (u v : ZMod 2) (F : Finset V),
    (∑ i ∈ univ \ F, D5.S3.HomologicalAlgebra.OrderedFaceSign.insertionSign F i • coefficients u v (insert i F)) = 0 ∧
    (F.card = 5 →
      (∑ i ∈ F, CircuitCycleDecomposition.restrictionSign F i ∅ •
        coefficients u v (F.erase i)) = 0)

private def parityDecidable : Decidable parityRows :=
  Fintype.decidableForallFintype (p := fun u : ZMod 2 => ∀ (v : ZMod 2) (F : Finset V),
    (∑ i ∈ univ \ F, D5.S3.HomologicalAlgebra.OrderedFaceSign.insertionSign F i • coefficients u v (insert i F)) = 0 ∧
    (F.card = 5 →
      (∑ i ∈ F, CircuitCycleDecomposition.restrictionSign F i ∅ •
        coefficients u v (F.erase i)) = 0))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- The kernel checks the finite boundary and circuit rows for all binary parameters.
private theorem parity : parityRows :=
  of_decide_eq_true (inst := parityDecidable) (by rfl)

private def embed (e : ResidueTorsion 2 ≃ₗ[ℤ] ZMod 2) : ZMod 2 →ₗ[ℤ] RationalResidue :=
  (ResidueTorsion 2).subtype.comp e.symm.toLinearMap

private theorem embed_injective (e : ResidueTorsion 2 ≃ₗ[ℤ] ZMod 2) :
    Function.Injective (embed e) :=
  Subtype.val_injective.comp e.symm.injective

private theorem embed_two (e : ResidueTorsion 2 ≃ₗ[ℤ] ZMod 2) (t : ZMod 2) :
    (2 : ℤ) • embed e t = 0 :=
  (Submodule.mem_torsionBy_iff _ _).mp (e.symm t).prop

private theorem id_weight (i : V) : (univ.filter (fun x : V => id x = i)).card = 1 := by
  rw [show univ.filter (fun x : V => id x = i) = {i} by ext x; simp]
  exact card_singleton i

private theorem isResidue (e : ResidueTorsion 2 ≃ₗ[ℤ] ZMod 2) (u v : ZMod 2) :
    (fun F => embed e (coefficients u v F)) ∈ weightedCircuitResidues core (id : V → V) := by
  rw [SparsePavingCircuitCoordinates.mem_weightedCircuitResidues_iff _
    (by decide : 4 < Fintype.card V) hole_size sparse core_ground core_base]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F bad
    simp [coefficients, allowed, bad]
  · intro F omitted
    simp [coefficients, allowed, omitted]
  · intro F
    unfold weightedBoundary
    simp only [id_weight, one_nsmul, ← map_zsmul, ← map_sum, (parity u v F).1, map_zero]
  · intro F hF
    unfold circuitReadout
    simp only [empty_union, ← map_zsmul, ← map_sum, (parity u v F).2 hF, map_zero]

private theorem coefficient_first (u v : ZMod 2) : coefficients u v {0, 1, 2, 4} = u := by
  have hallowed : allowed {0, 1, 2, 4} := by decide
  have hpair : firstPair ⊆ {0, 1, 2, 4} := by decide
  simp only [coefficients, ite_eq_left hallowed, ite_eq_left hpair]

private theorem coefficient_second (u v : ZMod 2) : coefficients u v {0, 2, 3, 4} = v := by
  have hallowed : allowed {0, 2, 3, 4} := by decide
  have hfirst : ¬ firstPair ⊆ {0, 2, 3, 4} := by decide
  have hsecond : secondPair ⊆ {0, 2, 3, 4} := by decide
  simp only [coefficients, ite_eq_left hallowed, ite_eq_right hfirst, ite_eq_left hsecond]

private abbrev twoTorsion : Type := {t : ZMod 6 // (2 : ℤ) • t = 0}

private theorem targetCard : Fintype.card twoTorsion = 2 := by decide

private theorem residue_not_cyclic :
    ¬ Nonempty (weightedCircuitResidues core (id : V → V) ≃ₗ[ℤ] ZMod 6) := by
  rintro ⟨comparison⟩
  obtain ⟨e⟩ := residueTorsion_equiv_zmod 2 (by decide)
  let f (x : ZMod 2 × ZMod 2) : weightedCircuitResidues core (id : V → V) :=
    ⟨fun F => embed e (coefficients x.1 x.2 F), isResidue e x.1 x.2⟩
  have hf (x : ZMod 2 × ZMod 2) : (2 : ℤ) • f x = 0 := by
    apply Subtype.ext
    funext F
    exact embed_two e _
  have hinj : Function.Injective f := by
    intro x y h
    have atFace (F : Finset V) : coefficients x.1 x.2 F = coefficients y.1 y.2 F :=
      embed_injective e (congrArg (fun Q : weightedCircuitResidues core (id : V → V) => Q.val F) h)
    exact Prod.ext (by simpa only [coefficient_first] using atFace {0,1,2,4})
      (by simpa only [coefficient_second] using atFace {0,2,3,4})
  let lift (x : ZMod 2 × ZMod 2) : twoTorsion :=
    ⟨comparison (f x), by rw [← map_smul, hf, map_zero]⟩
  have hle := Fintype.card_le_of_injective lift (fun _ _ h =>
    hinj (comparison.injective (congrArg Subtype.val h)))
  rw [targetCard] at hle
  norm_num at hle

private theorem no_lifting_equiv :
    ¬ Nonempty ((JointSaturatedImage (core.comap (id : V → V)) ⧸
      JointImageInSaturation (core.comap (id : V → V))) ≃ₗ[ℤ] ZMod 6) := by
  rintro ⟨e⟩
  have hn (i : V) : core.IsNonloop i := by
    rw [← Matroid.indep_singleton, ← Finset.coe_singleton,
      SparsePavingCircuitCoordinates.indep_iff_card_and_allowed (by decide) hole_size sparse core_base]
    refine ⟨by simp, ?_⟩
    intro h
    have hsize := hole_size {i} h
    simp at hsize
  obtain ⟨comparison, _⟩ := parallel_lifting_obstruction Function.surjective_id (fun {_ _} h => h) hn
  exact residue_not_cyclic ⟨comparison.symm.trans e⟩

/-- The independent replacement formula for three pairwise separated omitted bases. -/
def claim : Prop :=
  ∀ (k d : ℕ) (U : Type) [Fintype U] [LinearOrder U]
    (M : Matroid (Fin (k + 2))) (p : U → Fin (k + 2)),
    1 ≤ d → d + 2 ≤ k → Function.Surjective p →
    (∀ ⦃a b⦄, p a < p b → a < b) →
    ∀ (H J K : Finset (Fin (k + 2))),
      (∀ T ∈ ({H, J, K} : Set (Finset (Fin (k + 2)))), T.card = d + 2) →
      (H ∩ J).card ≤ d → (H ∩ K).card ≤ d → (J ∩ K).card ≤ d →
      M.E = Set.univ →
      (∀ F : Finset (Fin (k + 2)),
        M.IsBase (F : Set (Fin (k + 2))) ↔ F.card = d + 2 ∧ F ∉ ({H, J, K} : Set _)) →
      let n := Fintype.card U
      let weight := fun i => (univ.filter fun a => p a = i).card
      let g := univ.gcd weight
      let q := fun T => n.gcd ((univ \ T).gcd weight)
      Nonempty ((JointSaturatedImage (M.comap p) ⧸ JointImageInSaturation (M.comap p)) ≃ₗ[ℤ]
        ((Fin ((k.choose d) - 3) → ZMod g) ×
          (Fin ((k.choose (d + 1)) - 3) → ZMod n) × (ZMod (q H) × ZMod (q J) × ZMod (q K))))

theorem result : ¬ claim := by
  intro proposed
  obtain ⟨e⟩ := proposed 4 2 V core id (by decide) (by decide) Function.surjective_id
    (fun {_ _} h => h) (firstPair ∪ secondPair) (firstPair ∪ thirdPair)
    (secondPair ∪ thirdPair) hole_size (by decide) (by decide) (by decide) core_ground core_base
  have He :
      ((JointSaturatedImage (core.comap (id : V → V)) ⧸
        JointImageInSaturation (core.comap (id : V → V))) ≃ₗ[ℤ]
        ((Fin 3 → ZMod 1) × (Fin 1 → ZMod 6) × (ZMod 1 × ZMod 1 × ZMod 1))) := e
  let _ : Unique (ZMod 1 × ZMod 1 × ZMod 1) := Unique.mk' _
  let peel := (LinearEquiv.uniqueProd (R := ℤ) (M := (Fin 1 → ZMod 6) × (ZMod 1 × ZMod 1 × ZMod 1))
    (M₂ := Fin 3 → ZMod 1)).trans (LinearEquiv.prodUnique (R := ℤ))
  exact no_lifting_equiv ⟨He.trans (peel.trans (LinearEquiv.funUnique (Fin 1) ℤ (ZMod 6)))⟩

end D5.S3.Combinatorics.Matroids.ThreeOmittedCircuitRefutation
