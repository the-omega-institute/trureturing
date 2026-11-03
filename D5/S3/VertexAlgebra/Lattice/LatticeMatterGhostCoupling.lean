/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling
   mirror-E: none(waiver:algebraic-matter-ghost-coupling)
   anchors: []
   utility: none
   digest: The actual locally finite lattice matter coupling and integer ghost Ward identities. -/

import D5.S3.VertexAlgebra.LatticeSugawaraVirasoro
import D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! The original matter and ghost modes define a statewise finite tensor charge. -/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

open D5.S3.Quantum.Fermionic

/-- Algebraic tensor product of the original all-charge lattice and occupation carriers. -/
abbrev State (D : LatticeData) := Carrier D ⊗[ℂ] Fock

def ghostB (D : LatticeData) (r : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (BcGhostFock.b r)

def ghostC (D : LatticeData) (r : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (BcGhostFock.c r)

def matterMode (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (r : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map (sugawaraMode D H r) LinearMap.id

def ghostVirasoro (D : LatticeData) (r : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (BcGhostVirasoro.L r)

def summand (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (m : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map (sugawaraMode D H m) (BcGhostFock.c (-m))

private theorem summand_product (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    summand D H m = matterMode D H m * ghostC D (-m) := by
  apply TensorProduct.ext'
  intro v w
  simp only [summand, matterMode, ghostC, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- The upper bound comes from the actual Sugawara vertex operator at index m+1. -/
def upper (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) : ℤ :=
  max 0 (-HahnSeries.order ((HahnModule.of ℂ).symm (sugawaraField D H v))-2)

private theorem above_upper (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D) (m : ℤ)
    (hm : upper D H v < m) : sugawaraMode D H m v = 0 := by
  apply VertexOperator.ncoeff_eq_zero_of_lt_order
  have h := le_max_right 0
    (-HahnSeries.order ((HahnModule.of ℂ).symm (sugawaraField D H v))-2)
  change max 0 _ < m at hm
  omega

private theorem tensor_tail (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D)
    (w : Fock) (A : ℕ) (hA : 2 ≤ A) (hw : BcGhostOccupationRadius.Radius A w) (m : ℤ)
    (hm : m < -(A : ℤ) ∨ upper D H v < m) :
    summand D H m (v ⊗ₜ[ℂ] w) = 0 := by
  simp only [summand, TensorProduct.map_tmul]
  rcases hm with hm | hm
  · rw [(BcGhostOccupationRadius.high_modes hA hw (-m) (by omega)).2, TensorProduct.tmul_zero]
  · rw [above_upper D H v m hm, TensorProduct.zero_tmul]

/-- The summation family is finite on every algebraic tensor state. -/
theorem summand_finite (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) :
    Function.HasFiniteSupport (fun m : ℤ => summand D H m x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨A, hA, hw⟩ := BcGhostOccupationRadius.exists_radius w
    apply (Set.finite_Icc (-(A : ℤ)) (upper D H v)).subset
    intro m hm
    by_contra hn
    have ht : m < -(A : ℤ) ∨ upper D H v < m := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hn
    exact hm (tensor_tail D H v w A hA hw m ht)
  | add x y hx hy =>
    apply (hx.union hy).subset
    intro m hm
    by_contra hn
    have hx0 : summand D H m x = 0 := by
      by_contra hz
      exact hn (Or.inl hz)
    have hy0 : summand D H m y = 0 := by
      by_contra hz
      exact hn (Or.inr hz)
    apply hm
    change summand D H m (x+y) = 0
    rw [map_add, hx0, hy0, add_zero]

/-- This is a sum of state actions, never a sum of an infinite endomorphism family. -/
def T (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) where
  toFun x := ∑ᶠ m : ℤ, summand D H m x
  map_add' x y := by
    simp only [map_add]
    exact finsum_add_distrib (summand_finite D H x) (summand_finite D H y)
  map_smul' a x := by
    simp only [map_smul]
    exact (smul_finsum' a (summand_finite D H x)).symm

/-- The native charge is the locally finite product of the actual matter and c modes. -/
theorem T_apply (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (x : State D) : T D H x = ∑ᶠ m : ℤ, (matterMode D H m * ghostC D (-m)) x := by
  simp only [T, LinearMap.coe_mk, AddHom.coe_mk, summand_product]

/-- Every finite capture computes the same action, independently of the chosen cutoff. -/
theorem finite_capture (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (x : State D) (s : Finset ℤ)
    (hs : Function.support (fun m : ℤ => summand D H m x) ⊆ (s : Set ℤ)) :
    T D H x = ∑ m ∈ s, summand D H m x := by
  rw [T_apply]
  simp_rw [← summand_product]
  exact finsum_eq_sum_of_support_subset _ hs

/-- One finite union captures any prescribed finite collection of intermediate states. -/
theorem common_capture (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (X : Finset (State D)) :
    ∃ s : Finset ℤ, ∀ x ∈ X,
      Function.support (fun m : ℤ => summand D H m x) ⊆ (s : Set ℤ) := by
  classical
  refine ⟨X.biUnion (fun x => (summand_finite D H x).toFinset), ?_⟩
  intro x hx m hm
  exact Finset.mem_biUnion.mpr ⟨x, hx, by simpa using hm⟩

/-- The actual simple-tensor interval formula has both a ghost and a matter endpoint. -/
theorem T_tmul (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) (w : Fock) (A : ℕ) (hA : 2 ≤ A) (hw : BcGhostOccupationRadius.Radius A w) :
    T D H (v ⊗ₜ[ℂ] w) = ∑ m ∈ Finset.Icc (-(A : ℤ)) (upper D H v),
      sugawaraMode D H m v ⊗ₜ[ℂ] BcGhostFock.c (-m) w := by
  classical
  rw [finite_capture D H _ (Finset.Icc (-(A : ℤ)) (upper D H v))]
  · simp only [summand, TensorProduct.map_tmul]
  · intro m hm
    by_contra hn
    exact hm (tensor_tail D H v w A hA hw m (by
      simpa only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] using hn))

private theorem summand_b (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m r : ℤ) :
    summand D H m * ghostB D r + ghostB D r * summand D H m =
      if m = r then matterMode D H m else 0 := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (BcGhostFock.ghost_mixed_car r (-m)) w
  simp only [LinearMap.add_apply, Module.End.mul_apply] at h
  simp only [summand, ghostB, LinearMap.add_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← TensorProduct.tmul_add, add_comm (BcGhostFock.c (-m) (BcGhostFock.b r w)), h]
  by_cases hm : m = r
  · subst m
    simp [matterMode]
  · have hz : r + -m ≠ 0 := by omega
    simp [hm, hz]

private theorem summand_c (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m r : ℤ) :
    summand D H m * ghostC D r + ghostC D r * summand D H m = 0 := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (BcGhostFock.ghost_c_car (-m) r) w
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  simp only [summand, ghostC, LinearMap.add_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
  rw [← TensorProduct.tmul_add, h, TensorProduct.tmul_zero]

/-- All-integer b Ward identity on the actual tensor carrier. -/
theorem ward_b (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (r : ℤ) : T D H * ghostB D r + ghostB D r * T D H = matterMode D H r := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨s₀, hs₀⟩ := common_capture D H {x, ghostB D r x}
  let s := insert r s₀
  have hsx : Function.support (fun m : ℤ => summand D H m x) ⊆ (s : Set ℤ) := by
    intro m hm
    exact Finset.mem_insert_of_mem (hs₀ x (by simp) hm)
  have hsb : Function.support (fun m : ℤ => summand D H m (ghostB D r x)) ⊆
      (s : Set ℤ) := by
    intro m hm
    exact Finset.mem_insert_of_mem (hs₀ (ghostB D r x) (by simp) hm)
  change T D H (ghostB D r x) + ghostB D r (T D H x) = _
  rw [finite_capture D H _ s hsb, finite_capture D H _ s hsx, map_sum,
    ← Finset.sum_add_distrib]
  calc
    _ = ∑ m ∈ s, if m = r then matterMode D H m x else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      have h := LinearMap.congr_fun (summand_b D H m r) x
      by_cases he : m = r <;>
        simpa only [LinearMap.add_apply, Module.End.mul_apply, he, if_true, if_false,
          LinearMap.zero_apply] using h
    _ = _ := by simp [s]

/-- All-integer c Ward identity on the actual tensor carrier. -/
theorem ward_c (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (r : ℤ) : T D H * ghostC D r + ghostC D r * T D H = 0 := by
  apply LinearMap.ext
  intro x
  have hx := summand_finite D H x
  have hy := summand_finite D H (ghostC D r x)
  change (∑ᶠ m : ℤ, summand D H m (ghostC D r x)) +
    ghostC D r (∑ᶠ m : ℤ, summand D H m x) = _
  rw [map_finsum (ghostC D r) hx,
    ← finsum_add_distrib hy (hx.fun_comp (map_zero (ghostC D r)))]
  calc
    _ = ∑ᶠ _m : ℤ, (0 : State D) := by
      apply finsum_congr
      intro m
      exact LinearMap.congr_fun (summand_c D H m r) x
    _ = _ := by simp

end D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
