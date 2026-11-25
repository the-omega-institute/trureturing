/- GID: D5/S3/Geometry/SimplicialPersistence/OrderedChains
   generality: G
   mirror-B: D5/B/S3/Geometry/SimplicialPersistence/OrderedChains
   mirror-E: none(waiver:ordered-integer-chains)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: The full ordered integer face complex with its original coproduct coordinates. -/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import D5.S3.Topology.TauCeti.Algebra.Homology.OrderedCechCover
public import Mathlib.Data.Fintype.Powerset

/-! The ordinary ordered integer face differential in every natural degree. -/

@[expose] public section
noncomputable section
open CategoryTheory Limits Finset
open scoped BigOperators

namespace D5.S3.Geometry.FiniteSimplicialSingularHomology
variable {V : Type} [Fintype V] [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

abbrev Z : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- Actual increasing faces: no truncation or dimension bound is imposed on `K`. -/
abbrev Face (p : ℕ) := {s : Finset V // s ∈ K ∧ s.card = p + 1}

instance (p : ℕ) : Fintype (Face K p) := by
  classical
  unfold Face
  infer_instance

/-- The free integer module on the actual ordered `p`-faces. -/
abbrev orderedGroup (p : ℕ) : ModuleCat ℤ := ∐ fun _ : Face K p => Z

def faceι {p : ℕ} (s : Face K p) : Z ⟶ orderedGroup K p :=
  Sigma.ι (fun _ : Face K p => Z) s

def eraseFace {p : ℕ} (s : Face K (p + 1)) (v : s.val) : Face K p := by
  have hc : (s.val.erase v.val).card = p + 1 := by
    rw [card_erase_of_mem v.property, s.property.2]
    omega
  exact ⟨s.val.erase v.val,
    (K.isRelLowerSet_faces s.property.1).2 (s.val.erase_subset v.val)
      (Finset.card_pos.mp (by omega)), hc⟩

/-- Increasing-face deletion, with the ordinary rank sign. -/
def orderedBoundary (p : ℕ) : orderedGroup K (p + 1) ⟶ orderedGroup K p :=
  Sigma.desc fun s => ∑ v : s.val,
    ((-1 : ℤ) ^ (s.val.filter (fun w => w < v.val)).card) • faceι K (eraseFace K s v)

/-- The ordinary signed face boundary squares to zero in every natural degree. -/
theorem orderedBoundary_squared (p : ℕ) :
    orderedBoundary K (p + 1) ≫ orderedBoundary K p = 0 := by
  classical
  apply Sigma.hom_ext
  intro s
  simp only [orderedBoundary, Sigma.ι_comp_desc_assoc, Preadditive.sum_comp,
    Preadditive.zsmul_comp, faceι, Sigma.ι_comp_desc]
  have reindex {r : ℕ} (t : Face K r) (f : t.val → (Z ⟶ orderedGroup K p)) :
      (∑ v : t.val, ((-1 : ℤ) ^ (t.val.filter (fun w => w < v.val)).card) • f v) =
        ∑ i : Fin (r + 1), (-1 : ℤ) ^ (i : ℕ) •
          f ⟨t.val.orderEmbOfFin t.property.2 i,
            Finset.orderEmbOfFin_mem _ _ i⟩ := by
    symm
    apply Fintype.sum_equiv (t.val.orderIsoOfFin t.property.2).toEquiv
    intro i
    congr 1
    exact congrArg (fun n : ℕ => (-1 : ℤ) ^ n)
      (TauCeti.OrderedCover.rank_enumeration t.property.2 i).symm
  rw [reindex s]
  simp_rw [reindex]
  change (∑ i : Fin (p + 3), (-1 : ℤ) ^ (i : ℕ) •
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • _) = 0
  apply TauCeti.sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
  intro i j hij
  congr 1
  apply Subtype.ext
  exact TauCeti.OrderedCover.double_deletion s.property.2 i j hij

/-- The full ordered integer chain complex; all face degrees are retained. -/
def orderedChainComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (orderedGroup K) (orderedBoundary K) (orderedBoundary_squared K)

end D5.S3.Geometry.FiniteSimplicialSingularHomology

namespace D5.S3.Geometry.PersistentLaplacianHeatStability
open D5.S3.Geometry.FiniteSimplicialSingularHomology
variable {V : Type} [Fintype V] [LinearOrder V]

def coordinates (L : PreAbstractSimplicialComplex V) (p : ℕ) :
    orderedGroup L p →ₗ[ℤ] (Face L p → ℤ) := by
  classical
  exact (DirectSum.linearEquivFunOnFintype ℤ (Face L p) (fun _ => ℤ)).toLinearMap.comp
    (ModuleCat.coprodIsoDirectSum (fun _ : Face L p => Z)).hom.hom


end D5.S3.Geometry.PersistentLaplacianHeatStability
