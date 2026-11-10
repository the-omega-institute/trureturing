/- GID: D5/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualZhuSourceProjectors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite source current projectors and all-alpha elimination. -/
import D5.S3.VertexAlgebra.Lattice.ActualZhuSourceSupport
import D5.S3.VertexAlgebra.Lattice.ActualZhuMinimum
import Mathlib.LinearAlgebra.Lagrange

/-! Lagrange interpolation is from pinned Mathlib (Apache-2.0).
The source relations are those of Dong--Li--Mason, DOI 10.1006/jabr.1997.7112,
Theorem 3.4 and Remark 2.11. All equalities remain in the literal quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.Lattice.ActualZhuSourceProjectors
open LatticeGeneratingFieldLocality LatticePositiveEnergy
open ActualZhuFinite ActualZhuAlgebra ActualZhuCurrentNormalForm
open ActualZhuCurrentRelations ActualZhuSourceSupport ActualZhuMinimum
open scoped BigOperators IsMulCommutative
noncomputable section
variable (D : LatticeData) [hD : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]
local instance : Ring (Q D) := quotientRing D hD.out
local instance : Algebra ℂ (Q D) := quotientAlgebra D hD.out
local instance : IsMulCommutative (currentAlgebra D) :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    exact currents_commute D i j)

def cutoff (i : Fin D.rank) : ℕ := (chargeEnergy D (unitCharge D i)).toNat
abbrev Node (i : Fin D.rank) := Fin (2 * cutoff D i + 1)
abbrev Grid := ∀ i : Fin D.rank, Node D i
def node (i : Fin D.rank) (j : Node D i) : ℤ := (j.val : ℤ) - cutoff D i
def gridWeight (r : Grid D) : Charge D := fun i => node D i (r i)

omit hD in
private theorem node_injective (i : Fin D.rank) :
    Function.Injective (fun j : Node D i => (node D i j : ℂ)) := by
  intro a b h
  have hz : node D i a = node D i b := Int.cast_injective h
  apply Fin.ext
  dsimp [node] at hz
  omega

def chargedCurrent (α : Charge D) : currentAlgebra D :=
  ∑ i, (α i : ℂ) • currentGenerator D i

theorem chargedCurrent_coe (α : Charge D) :
    (chargedCurrent D α : Q D) = Hcharge D α := by
  simp [chargedCurrent, Hcharge, currentGenerator]

private theorem chargedCurrent_unit (i : Fin D.rank) :
    chargedCurrent D (unitCharge D i) = currentGenerator D i := by
  classical
  simp [chargedCurrent, unitCharge]

private theorem current_nodal (α : Charge D) :
    let k := (chargeEnergy D α).toNat
    ∏ j : Fin (2*k+1),
      (chargedCurrent D α + (k : currentAlgebra D) - (j.val : currentAlgebra D)) = 0 := by
  classical
  let k := (chargeEnergy D α).toNat
  have he : ((List.range (2*k+1)).map fun j : ℕ =>
      chargedCurrent D α + (k : currentAlgebra D) - (j : currentAlgebra D)).prod = 0 := by
    apply Subtype.val_injective
    change (currentAlgebra D).val _ = (currentAlgebra D).val 0
    rw [map_list_prod, List.map_map, map_zero]
    simpa only [Function.comp_def, map_sub, map_add, map_natCast,
      show (currentAlgebra D).val (chargedCurrent D α) = Hcharge D α from
        chargedCurrent_coe D α] using all_alpha_current_relation D α
  rw [← List.prod_toFinset _ List.nodup_range, List.toFinset_range,
    Finset.prod_range] at he
  exact he

def coordinateProjector (i : Fin D.rank) (j : Node D i) : currentAlgebra D :=
  Polynomial.aeval (currentGenerator D i)
    (Lagrange.basis Finset.univ (fun j : Node D i => (node D i j : ℂ)) j)

theorem coordinate_sum (i : Fin D.rank) : ∑ j, coordinateProjector D i j = 1 := by
  classical
  have hi := (node_injective D i).injOn (s := (Finset.univ : Finset (Node D i)))
  have hs : (Finset.univ : Finset (Node D i)).Nonempty := ⟨⟨0, by omega⟩, by simp⟩
  have he := congrArg (Polynomial.aeval (currentGenerator D i)) (Lagrange.sum_basis hi hs)
  simpa only [map_sum, map_one, coordinateProjector] using he

theorem coordinate_eigen (i : Fin D.rank) (j : Node D i) :
    currentGenerator D i * coordinateProjector D i j =
      (node D i j : ℂ) • coordinateProjector D i j := by
  classical
  let s : Finset (Node D i) := Finset.univ
  let v : Node D i → ℂ := fun j => (node D i j : ℂ)
  have hj : j ∈ s := Finset.mem_univ _
  have hp : (Polynomial.X - Polynomial.C (v j)) * Lagrange.basis s v j =
      Polynomial.C (Lagrange.nodalWeight s v j) * Lagrange.nodal s v := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hj,
      ← Lagrange.nodal_erase_eq_nodal_div hj, Lagrange.nodal_eq_mul_nodal_erase hj]
    ring
  have hn : Polynomial.aeval (currentGenerator D i) (Lagrange.nodal s v) = 0 := by
    simp only [Lagrange.nodal, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    have he := current_nodal D (unitCharge D i)
    rw [chargedCurrent_unit] at he
    convert he using 1
    apply Finset.prod_congr rfl
    intro a _
    dsimp [v, node, cutoff]
    push_cast
    ring
  have he := congrArg (Polynomial.aeval (currentGenerator D i)) hp
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hn, mul_zero] at he
  change (currentGenerator D i - algebraMap ℂ (currentAlgebra D) (node D i j : ℂ)) *
    coordinateProjector D i j = 0 at he
  rw [sub_mul, sub_eq_zero, ← Algebra.smul_def] at he
  exact he

def projector (r : Grid D) : currentAlgebra D := ∏ i, coordinateProjector D i (r i)

theorem projector_sum : ∑ r : Grid D, projector D r = 1 := by
  classical
  change (∑ r : Grid D, ∏ i, coordinateProjector D i (r i)) = 1
  rw [← Fintype.prod_sum]
  simp [coordinate_sum]

theorem projector_eigen (r : Grid D) (i : Fin D.rank) :
    currentGenerator D i * projector D r = (gridWeight D r i : ℂ) • projector D r := by
  classical
  rw [projector, ← Finset.mul_prod_erase Finset.univ
    (fun j => coordinateProjector D j (r j)) (Finset.mem_univ i), ← mul_assoc,
    coordinate_eigen, smul_mul_assoc]
  rfl

theorem charged_eigen (r : Grid D) (α : Charge D) :
    chargedCurrent D α * projector D r =
      ((∑ i, α i * gridWeight D r i : ℤ) : ℂ) • projector D r := by
  classical
  simp only [chargedCurrent, Finset.sum_mul, smul_mul_assoc, projector_eigen,
    smul_smul, Int.cast_sum, Int.cast_mul, Finset.sum_smul]

private theorem product_eigen (r : Grid D) (α : Charge D) (k : ℕ) (l : List ℕ) :
    ((l.map fun j : ℕ => chargedCurrent D α + (k : currentAlgebra D) -
      (j : currentAlgebra D)).prod) * projector D r =
    ((l.map fun j : ℕ => ((∑ i, α i * gridWeight D r i : ℤ) : ℂ) +
      (k : ℂ) - (j : ℂ)).prod) • projector D r := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, ih, mul_smul_comm, sub_mul, add_mul, charged_eigen]
    have cast_mul (n : ℕ) : (n : currentAlgebra D) * projector D r =
        (n : ℂ) • projector D r := by
      rw [Algebra.smul_def, map_natCast]
    rw [cast_mul, cast_mul, ← add_smul, ← sub_smul, smul_smul]
    congr 1
    ring

/-- Every nonzero source projector satisfies all lattice inequalities, not just the box. -/
theorem projector_survives (r : Grid D) (hr : projector D r ≠ 0) :
    AllAlpha D (gridWeight D r) := by
  classical
  intro α
  let k := (chargeEnergy D α).toNat
  have hn := current_nodal D α
  have hp := product_eigen D r α k (List.range (2*k+1))
  have hz : ((List.range (2*k+1)).map fun j : ℕ => chargedCurrent D α +
      (k : currentAlgebra D) - (j : currentAlgebra D)).prod = 0 := by
    rw [← List.prod_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.prod_range]
    exact hn
  rw [hz, zero_mul] at hp
  have hc := (smul_eq_zero.mp hp.symm).resolve_right hr
  obtain ⟨j,hj,he⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hc)
  have hj' := List.mem_range.mp hj
  have he' : (∑ i, α i * gridWeight D r i : ℤ) + (k : ℤ) - (j : ℤ) = 0 := by
    exact_mod_cast he
  have hk : (k : ℤ) = chargeEnergy D α :=
    Int.toNat_of_nonneg (chargeEnergy_nonneg D hD.out α)
  constructor <;> omega

/-- Every current-algebra element acts by a scalar on each source projector. -/
theorem current_scalar (r : Grid D) (a : currentAlgebra D) :
    ∃ c : ℂ, (a : Q D) * (projector D r : Q D) = c • (projector D r : Q D) := by
  have hs (x : Q D) (hx : x ∈ currentAlgebra D) :
      ∃ c : ℂ, x * (projector D r : Q D) = c • (projector D r : Q D) := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact ⟨(gridWeight D r i : ℂ), congrArg Subtype.val (projector_eigen D r i)⟩
    | algebraMap c => exact ⟨c, Algebra.smul_def c _ |>.symm⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨c,hc⟩ := ihx
      obtain ⟨d,hd⟩ := ihy
      exact ⟨c+d, by rw [add_mul, hc, hd, add_smul]⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨c,hc⟩ := ihx
      obtain ⟨d,hd⟩ := ihy
      exact ⟨d*c, by rw [mul_assoc, hd, mul_smul_comm, hc, smul_smul]⟩
  exact hs a a.property

#print axioms projector_sum
#print axioms projector_eigen
#print axioms projector_survives
end
end D5.S3.VertexAlgebra.Lattice.ActualZhuSourceProjectors
