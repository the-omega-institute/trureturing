/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostBPZ
   mirror-E: none(waiver:algebraic-original-orbifold-brst-ghost-bpz)
   anchors: []
   utility: none
   digest: Signed BPZ mode adjoints and the relative Ward identity on the native bc Fock space. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostBilinear
import D5.S3.Quantum.Fermionic.BcGhostBRSTDegree

/-! For inversion by `1/z`, the weights two and minus one give opposite
signs for the b and c modes. The diagonal ghost-number phase implements these
signs together with the parity of the left input in the bilinear pairing. -/

set_option autoImplicit false

noncomputable section
namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostBPZ

open D5.S3.Quantum.Fermionic
open CountableOccupationFock BcGhostFock BcGhostCharge BcGhostHermitian
open BcGhostBRST (Qg ghost_number_Qg)
open OriginalOrbifoldBRSTGhostBilinear

/-- The BPZ phase uses Euclidean residues, including at negative ghost number. -/
def bpzPhase (r : ℤ) : ℂ :=
  if r % 4 = 1 ∨ r % 4 = 2 then -1 else 1

private theorem residue_cases (r : ℤ) :
    r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by
  omega

private theorem parity_zpow (r : ℤ) : (-1 : ℂ) ^ r = (-1 : ℂ) ^ (r % 2) := by
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  have hsquare : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
  calc
    (-1 : ℂ) ^ r = (-1 : ℂ) ^ (r % 2 + 2 * (r / 2)) :=
      congrArg (fun n : ℤ => (-1 : ℂ) ^ n) (Int.emod_add_mul_ediv r 2).symm
    _ = (-1 : ℂ) ^ (r % 2) := by
      rw [zpow_add₀ hne, zpow_mul, hsquare, one_zpow, mul_one]

theorem bpzPhase_eq_zpow (r : ℤ) :
    bpzPhase r = (-1 : ℂ) ^ (r * (r + 1) / 2) := by
  have hnext : (r + 1) % 4 = (r % 4 + 1) % 4 := by omega
  have hprod := Int.mul_emod r (r + 1) 4
  rw [hnext] at hprod
  have hhalf : (r * (r + 1) / 2) % 2 = (r * (r + 1) % 4) / 2 := by omega
  rw [parity_zpow, hhalf, hprod]
  rcases residue_cases r with hr | hr | hr | hr <;> norm_num [bpzPhase, hr]

theorem bpzPhase_succ (r : ℤ) :
    bpzPhase (r + 1) = -((-1 : ℂ) ^ r) * bpzPhase r := by
  have hnext : (r + 1) % 4 = (r % 4 + 1) % 4 := by omega
  have hparity : r % 2 = (r % 4) % 2 := by omega
  unfold bpzPhase
  rw [hnext, parity_zpow, hparity]
  rcases residue_cases r with hr | hr | hr | hr <;> norm_num [hr]

theorem bpzPhase_pred (r : ℤ) :
    bpzPhase (r - 1) = (-1 : ℂ) ^ r * bpzPhase r := by
  have hprev : (r - 1) % 4 = (r % 4 + 3) % 4 := by omega
  have hparity : r % 2 = (r % 4) % 2 := by omega
  unfold bpzPhase
  rw [hprev, parity_zpow, hparity]
  rcases residue_cases r with hr | hr | hr | hr <;> norm_num [hr]

private theorem bpzPhase_square (r : ℤ) : bpzPhase r * bpzPhase r = 1 := by
  unfold bpzPhase
  split <;> norm_num

/-- The phase multiplies each finite occupation coefficient by its charge sign. -/
def P : Module.End ℂ Fock where
  toFun x := Finsupp.onFinset x.support (fun S => bpzPhase (charge S) * x S)
    (fun S h => Finsupp.mem_support_iff.mpr (fun hx => h (by simp [hx])))
  map_add' x y := by
    apply Finsupp.ext
    intro S
    simp only [Finsupp.onFinset_apply, Finsupp.add_apply, mul_add]
  map_smul' a x := by
    apply Finsupp.ext
    intro S
    simp only [Finsupp.onFinset_apply, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact mul_left_comm _ _ _

@[simp] theorem P_coefficient (x : Fock) (S : Finset ℕ) :
    P x S = bpzPhase (charge S) * x S := rfl

theorem P_ket (S : Finset ℕ) : P (ket S) = bpzPhase (charge S) • ket S := by
  apply Finsupp.ext
  intro T
  by_cases h : S = T
  · subst T
    simp
  · simp [ket, h]

theorem P_involutive : Function.Involutive P := by
  intro x
  apply Finsupp.ext
  intro S
  rw [P_coefficient, P_coefficient, ← mul_assoc, bpzPhase_square, one_mul]

theorem P_of_homogeneous {r : ℤ} {x : Fock} (hx : Homogeneous r x) :
    P x = bpzPhase r • x := by
  apply Finsupp.ext
  intro S
  by_cases hS : x S = 0
  · simp [hS]
  · simp [hx S hS]

private theorem P_homogeneous {r : ℤ} {x : Fock} (hx : Homogeneous r x) :
    Homogeneous r (P x) := by
  intro S hS
  apply hx S
  intro hzero
  exact hS (by simp [hzero])

private theorem homogeneous_of_commutator {T : Module.End ℂ Fock} {r s : ℤ}
    {x : Fock} (hx : Homogeneous r x)
    (hT : ghostNumber * T - T * ghostNumber = (s : ℂ) • T) :
    Homogeneous (r + s) (T x) := by
  apply (homogeneous_iff_number _ _).mpr
  have h := LinearMap.congr_fun hT x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    (homogeneous_iff_number r x).mp hx, map_smul] at h
  rw [Int.cast_add, add_smul]
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

private theorem homogeneous_b {r : ℤ} {x : Fock} (hx : Homogeneous r x) (n : ℤ) :
    Homogeneous (r - 1) (b n x) := by
  rw [sub_eq_add_neg]
  apply homogeneous_of_commutator hx
  simpa only [Int.cast_neg, Int.cast_one, neg_smul, one_smul] using
    ghost_number_relations.2.1 n

private theorem homogeneous_c {r : ℤ} {x : Fock} (hx : Homogeneous r x) (n : ℤ) :
    Homogeneous (r + 1) (c n x) :=
  homogeneous_of_commutator hx (by simpa using ghost_number_relations.2.2 n)

private theorem homogeneous_Qg {r : ℤ} {x : Fock} (hx : Homogeneous r x) :
    Homogeneous (r + 1) (Qg x) :=
  homogeneous_of_commutator hx (by simpa using ghost_number_Qg)

/-- The absolute BPZ pairing twists the first input of the native bilinear pairing. -/
def beta : Fock →ₗ[ℂ] Fock →ₗ[ℂ] ℂ := Bg.comp P

theorem beta_of_homogeneous {r : ℤ} {x : Fock} (hx : Homogeneous r x) (y : Fock) :
    beta x y = bpzPhase r * Bg x y := by
  change Bg (P x) y = _
  rw [P_of_homogeneous hx, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem beta_b (n : ℤ) {r : ℤ} {x : Fock} (hx : Homogeneous r x) (y : Fock) :
    beta (b n x) y = (-1 : ℂ) ^ r * beta x (b (-n) y) := by
  rw [beta_of_homogeneous (homogeneous_b hx n), beta_of_homogeneous hx,
    bpzPhase_pred, Bg_b, mul_assoc]

theorem beta_c (n : ℤ) {r : ℤ} {x : Fock} (hx : Homogeneous r x) (y : Fock) :
    beta (c n x) y = -((-1 : ℂ) ^ r) * beta x (c (-n) y) := by
  rw [beta_of_homogeneous (homogeneous_c hx n), beta_of_homogeneous hx,
    bpzPhase_succ, Bg_c, mul_assoc]

theorem beta_Qg {r : ℤ} {x : Fock} (hx : Homogeneous r x) (y : Fock) :
    beta (Qg x) y + (-1 : ℂ) ^ r * beta x (Qg y) = 0 := by
  rw [beta_of_homogeneous (homogeneous_Qg hx), beta_of_homogeneous hx,
    bpzPhase_succ, Bg_Qg]
  ring

theorem beta_left_radical (x : Fock) (hx : ∀ y, beta x y = 0) : x = 0 := by
  have h : P x = 0 := Bg_left_radical (P x) hx
  simpa only [P_involutive x, map_zero] using congrArg P h

theorem beta_right_radical (y : Fock) (hy : ∀ x, beta x y = 0) : y = 0 := by
  apply Bg_right_radical y
  intro x
  have h : Bg (P (P x)) y = 0 := hy (P x)
  rwa [P_involutive x] at h

theorem beta_charge_selection {r s : ℤ} {x y : Fock}
    (hx : Homogeneous r x) (hy : Homogeneous s y) (h : r + s ≠ 3) :
    beta x y = 0 := by
  change Hg (kappa (P x)) y = 0
  apply Hg_charge_selection r s _ _ _ hy h
  intro S hS
  apply P_homogeneous hx S
  simpa only [kappa_apply, ne_eq, star_eq_zero] using hS

/-- The occupation phase preserves the actual b-zero kernel. -/
def PRel : Relative →ₗ[ℂ] Relative :=
  P.restrict fun x hx => (mem_relative_iff _).mpr fun S hS => by
    simp [(mem_relative_iff _).mp hx S hS]

/-- The relative BPZ pairing keeps the c-zero insertion of the native relative pairing. -/
def betaRel : Relative →ₗ[ℂ] Relative →ₗ[ℂ] ℂ := Brel.comp PRel

theorem betaRel_apply (x y : Relative) :
    betaRel x y = beta (x : Fock) (c 0 (y : Fock)) := rfl

theorem betaRel_charge_selection {r s : ℤ} {x y : Relative}
    (hx : Homogeneous r (x : Fock)) (hy : Homogeneous s (y : Fock)) (h : r + s ≠ 2) :
    betaRel x y = 0 := by
  rw [betaRel_apply]
  exact beta_charge_selection hx (homogeneous_c hy 0) (by omega)

theorem betaRel_left_radical (x : Relative) (hx : ∀ y, betaRel x y = 0) : x = 0 := by
  have h : PRel x = 0 := Brel_left_radical (PRel x) hx
  have hp : P (x : Fock) = 0 := congrArg Subtype.val h
  apply Subtype.ext
  change (x : Fock) = 0
  simpa only [P_involutive (x : Fock), map_zero] using congrArg P hp

theorem betaRel_right_radical (y : Relative) (hy : ∀ x, betaRel x y = 0) : y = 0 := by
  apply Brel_right_radical y
  intro x
  have hx : PRel (PRel x) = x := Subtype.ext (P_involutive (x : Fock))
  have h : Brel (PRel (PRel x)) y = 0 := hy (PRel x)
  rwa [hx] at h

/-- The odd c-zero insertion gives the relative sign using the vanishing obstruction
on the b-zero kernel. The pairing expressions are evaluated in the ambient Fock space. -/
theorem beta_Qg_relative_ward {r : ℤ} {x y : Fock} (hr : Homogeneous r x)
    (hx : b 0 x = 0) (hy : b 0 y = 0) :
    beta (Qg x) (c 0 y) - (-1 : ℂ) ^ r * beta x (c 0 (Qg y)) = 0 := by
  rw [beta_of_homogeneous (homogeneous_Qg hr), beta_of_homogeneous hr, bpzPhase_succ]
  calc
    _ = (-((-1 : ℂ) ^ r) * bpzPhase r) *
          (Bg (Qg x) (c 0 y) + Bg x (c 0 (Qg y))) := by ring
    _ = 0 := by rw [Bg_Qg_relative_ward hx hy, mul_zero]

/-- The relative pairing can be used directly when both images under Qg lie in the kernel. -/
theorem betaRel_Qg_ward {r : ℤ} {x y : Relative} (hr : Homogeneous r (x : Fock))
    (hxQ : Qg (x : Fock) ∈ relativeSpace) (hyQ : Qg (y : Fock) ∈ relativeSpace) :
    betaRel ⟨Qg (x : Fock), hxQ⟩ y -
      (-1 : ℂ) ^ r * betaRel x ⟨Qg (y : Fock), hyQ⟩ = 0 := by
  simpa only [betaRel_apply] using beta_Qg_relative_ward hr x.property y.property

theorem beta_vacuum_top : beta vacuum (c (-1) (c 0 (c 1 vacuum))) = 1 := by
  have hthree : create 3 (ket {1}) = -ket {1, 3} := by
    have hcount : lowerCount 3 {1} = 1 := by decide
    have hS : insert 3 ({1} : Finset ℕ) = {1, 3} := by decide
    rw [create_ket, ite_eq_right (by decide : 3 ∉ ({1} : Finset ℕ)), hS]
    simp [phase, hcount]
  have hfive : create 5 (ket {1, 3}) = ket E := by
    have hcount : lowerCount 5 {1, 3} = 2 := by decide
    have hS : insert 5 ({1, 3} : Finset ℕ) = E := by decide
    rw [create_ket, ite_eq_right (by decide : 5 ∉ ({1, 3} : Finset ℕ)), hS]
    norm_num [phase, hcount]
  have hc : c (-1) = create 5 := by norm_num [c]
  have hP : P vacuum = vacuum := by
    have hcharge : charge ∅ = 0 := by decide
    rw [vacuum, P_ket, hcharge]
    norm_num [bpzPhase]
  change Bg (P vacuum) (c (-1) (c 0 (c 1 vacuum))) = _
  rw [hP, Bg_vacuum_left, ghost_vacuum.2.2.1, c_zero, hthree, hc, map_neg, hfive]
  simp [ket]

#print axioms bpzPhase
#print axioms bpzPhase_eq_zpow
#print axioms bpzPhase_succ
#print axioms bpzPhase_pred
#print axioms P
#print axioms P_coefficient
#print axioms P_ket
#print axioms P_involutive
#print axioms P_of_homogeneous
#print axioms beta
#print axioms beta_of_homogeneous
#print axioms beta_b
#print axioms beta_c
#print axioms beta_Qg
#print axioms beta_left_radical
#print axioms beta_right_radical
#print axioms beta_charge_selection
#print axioms PRel
#print axioms betaRel
#print axioms betaRel_apply
#print axioms betaRel_charge_selection
#print axioms betaRel_left_radical
#print axioms betaRel_right_radical
#print axioms beta_Qg_relative_ward
#print axioms betaRel_Qg_ward
#print axioms beta_vacuum_top

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostBPZ
