/- GID: D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cyclic shifts give the second family in every dimension. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry

/-! Cyclic shifts give difference labels, while sum-indexed shield vectors supply the
partial-transpose certificate. -/

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions

open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite

noncomputable section

def multiplicity {d : ℕ} (a : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (m : Fin d) : ℕ :=
  Fintype.card {p : Fin d × Fin d // a p.1 p.2 ≠ 0 ∧ μ p.1 p.2 = m}

def tVec {d : ℕ} (a : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (m : Fin d) : Fin d × Fin d → ℂ := fun p =>
  if a p.1 p.2 ≠ 0 ∧ μ p.1 p.2 = m then
    (a p.1 p.2 : ℂ) / Real.sqrt d
  else 0

def IsSecondFamilyData (d : ℕ) (q : Fin d → Matrix (Fin d) (Fin d) ℝ)
    (qbar : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (a : Fin d → Fin d → ℝ) (s : Fin d → Fin d × Fin d → ℂ) : Prop :=
  (∀ j, (q j)ᵀ * q j = 1) ∧
  (∀ m n, ∑ k, qbar m k * qbar n k = if m = n then 1 else 0) ∧
  (∀ i j k, q k i j = a i j * qbar (μ i j) k) ∧
  (∀ i j, a i j ≠ 0 → a i j ^ 2 = (d : ℝ) / multiplicity a μ (μ i j)) ∧
  (∀ m n, ∑ x, star (s m x) * s n x = if m = n then 1 else 0) ∧
  D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
      (∑ m, Matrix.vecMulVec (s m) (star (s m))) =
    ∑ m, Matrix.vecMulVec (tVec a μ m) (star (tVec a μ m))

def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q qbar μ a s, IsSecondFamilyData d q qbar μ a s

private def cyclicQ (d : ℕ) (k : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  Equiv.Perm.permMatrix ℝ (finCycle k)

private def cyclicMu (d : ℕ) : Fin d → Fin d → Fin d := fun i j => j - i

private def cyclicS (d : ℕ) : Fin d → Fin d → ℝ := fun _ _ => 1

private def cyclicQbar (d : ℕ) : Fin d → Fin d → ℝ :=
  fun m k => if k = m then 1 else 0

private def cyclicShield (d : ℕ) : Fin d → Fin d × Fin d → ℂ :=
  fun m p => if p.1 + p.2 = m then (Real.sqrt d : ℂ)⁻¹ else 0

private theorem cyclic_shift_factor (d : ℕ) (i j k : Fin d) :
    i + k = j ↔ k = cyclicMu d i j := by
  have := i.neZero
  change i + k = j ↔ k = j - i
  simp only [eq_sub_iff_add_eq, add_comm]

private theorem cyclic_q_orthogonal (d : ℕ) (k : Fin d) :
    (cyclicQ d k)ᵀ * cyclicQ d k = 1 := by
  simpa only [cyclicQ, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.mem_unitaryGroup_iff'.mp ((finCycle k).permMatrix_mem_unitaryGroup (R := ℝ)))

private theorem cyclic_q_factorization (d : ℕ) :
    ∀ i j k, cyclicQ d k i j = cyclicS d i j * cyclicQbar d (cyclicMu d i j) k := by
  intro i j k
  delta cyclicQ cyclicS cyclicQbar
  simp [Equiv.Perm.permMatrix, cyclic_shift_factor d i j k]

private def cyclicFiberEquiv (d : ℕ) (m : Fin d) :
    {p : Fin d × Fin d // cyclicS d p.1 p.2 ≠ 0 ∧ cyclicMu d p.1 p.2 = m} ≃ Fin d :=
  { toFun := fun p => p.1.1
    invFun := fun i => ⟨(i, finCycle m i), by
      refine ⟨by change (1 : ℝ) ≠ 0; simp, ?_⟩
      have hm := (cyclic_shift_factor d i (finCycle m i) m).mp ?_
      · exact hm.symm
      · rfl⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have hm : m = cyclicMu d p.1.1 p.1.2 := p.2.2.symm
        have hs := (cyclic_shift_factor d p.1.1 p.1.2 m).mpr hm
        exact hs
    right_inv := by intro i; rfl }

private theorem cyclic_multiplicity (d : ℕ) (h : 2 ≤ d) (i j : Fin d) :
    (cyclicS d i j) ^ 2 = (d : ℝ) / multiplicity (cyclicS d) (cyclicMu d) (cyclicMu d i j) := by
  have hc : multiplicity (cyclicS d) (cyclicMu d) (cyclicMu d i j) = d := by
    delta multiplicity
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (cyclicFiberEquiv d (cyclicMu d i j))
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) h))
  change (1 : ℝ) ^ 2 =
    (d : ℝ) / multiplicity (cyclicS d) (cyclicMu d) (cyclicMu d i j)
  simp [hc, hd]

private theorem cyclic_qbar_orthonormal (d : ℕ) :
    ∀ m n, ∑ k, cyclicQbar d m k * cyclicQbar d n k = if m = n then 1 else 0 := by
  classical
  intro m n
  delta cyclicQbar
  by_cases hmn : m = n
  · subst n
    simp
  · have hnm : n ≠ m := Ne.symm hmn
    simp [hmn, hnm]

private def cyclicShieldIndexEquiv (d : ℕ) [NeZero d] :
    (Fin d × Fin d) ≃ (Fin 2 → ZMod d) :=
  (Equiv.prodCongr (ZMod.finEquiv d).toEquiv
    ((ZMod.finEquiv d).toEquiv.trans (Equiv.neg (ZMod d)))).trans
      (finTwoArrowEquiv (ZMod d)).symm

private def cyclicShieldSector (d : ℕ) [NeZero d] (m : Fin d) : Fin 2 → ZMod d :=
  ![0, -(ZMod.finEquiv d) m]

private theorem cyclic_shield_transport (d : ℕ) [NeZero d]
    (m : Fin d) (p : Fin d × Fin d) :
    fourierVector 0 (cyclicShieldSector d m) (cyclicShieldIndexEquiv d p) =
      cyclicShield d m p := by
  classical
  let z := ZMod.finEquiv d
  have hsector :
      cyclicShieldIndexEquiv d p =
        sectorPoint (cyclicShieldIndexEquiv d p 0) (cyclicShieldSector d m) ↔
      p.1 + p.2 = m := by
    constructor
    · intro hh
      have h1 := congrFun hh 1
      change -z p.2 = z p.1 + -z m at h1
      rw [← sub_eq_add_neg] at h1
      have h2 : -z p.2 + z m = z p.1 := (eq_sub_iff_add_eq).mp h1
      apply z.injective
      rw [map_add, ← h2]
      abel
    · intro hp
      have hz : z p.1 + z p.2 = z m := by rw [← map_add, hp]
      apply (finTwoArrowEquiv (ZMod d)).injective
      apply Prod.ext
      · change z p.1 = z p.1 + 0
        simp
      · change -z p.2 = z p.1 + -z m
        rw [← hz]
        abel
  delta fourierVector cyclicShield
  refine if_congr hsector ?_ rfl
  rw [zero_mul, AddChar.map_zero_eq_one, mul_one]

private theorem cyclic_shield_orthonormal (d : ℕ) (h : 2 ≤ d) :
    ∀ m n, ∑ x, star (cyclicShield d m x) * cyclicShield d n x = if m = n then 1 else 0 := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hlabels (m n : Fin d) : cyclicShieldSector d m = cyclicShieldSector d n ↔ m = n := by
    constructor
    · intro hh
      exact (ZMod.finEquiv d).injective (neg_injective (congrFun hh 1))
    · rintro rfl
      rfl
  intro m n
  have hb := sector_basis 2 d (by decide) h 0 0
    (cyclicShieldSector d m) (cyclicShieldSector d n) rfl rfl
  change (∑ i : Fin 2 → ZMod d,
    star (fourierVector 0 (cyclicShieldSector d m) i) *
      fourierVector 0 (cyclicShieldSector d n) i) = _ at hb
  calc
    _ = ∑ p, star (fourierVector 0 (cyclicShieldSector d m) (cyclicShieldIndexEquiv d p)) *
        fourierVector 0 (cyclicShieldSector d n) (cyclicShieldIndexEquiv d p) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [cyclic_shield_transport, cyclic_shield_transport]
    _ = ∑ i : Fin 2 → ZMod d, star (fourierVector 0 (cyclicShieldSector d m) i) *
        fourierVector 0 (cyclicShieldSector d n) i :=
      Equiv.sum_comp (cyclicShieldIndexEquiv d) (fun i =>
        star (fourierVector 0 (cyclicShieldSector d m) i) *
          fourierVector 0 (cyclicShieldSector d n) i)
    _ = _ := by
      exact hb.trans (if_congr
        ⟨fun hh => (hlabels m n).mp hh.2,
          fun hmn => ⟨rfl, (hlabels m n).mpr hmn⟩⟩ rfl rfl)

private theorem cyclic_partial_transpose (d : ℕ) :
    D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
        (∑ m, Matrix.vecMulVec (cyclicShield d m) (star (cyclicShield d m))) =
      ∑ m, Matrix.vecMulVec (tVec (cyclicS d) (cyclicMu d) m)
        (star (tVec (cyclicS d) (cyclicMu d) m)) := by
  classical
  apply Matrix.ext
  intro p q
  have := p.1.neZero
  have heq : q.1 + p.2 = p.1 + q.2 ↔ q.2 - q.1 = p.2 - p.1 := by
    rw [sub_eq_sub_iff_add_eq_add]
    constructor <;> intro hh <;> simpa only [add_comm] using hh.symm
  delta D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  delta cyclicShield tVec cyclicS cyclicMu
  simp [ite_mul, heq]

private theorem cyclic_data (d : ℕ) (h : 2 ≤ d) :
    IsSecondFamilyData d (cyclicQ d) (cyclicQbar d) (cyclicMu d) (cyclicS d)
      (cyclicShield d) := by
  refine ⟨?_, cyclic_qbar_orthonormal d, cyclic_q_factorization d, ?_,
    cyclic_shield_orthonormal d h, cyclic_partial_transpose d⟩
  · intro j
    exact cyclic_q_orthogonal d j
  · intro i j _
    exact cyclic_multiplicity d h i j

theorem result : claim := by
  intro d hd
  exact ⟨cyclicQ d, cyclicQbar d, cyclicMu d, cyclicS d, cyclicShield d,
    cyclic_data d hd⟩

end
end D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions
