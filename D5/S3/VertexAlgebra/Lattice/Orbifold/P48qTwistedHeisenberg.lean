/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qTwistedHeisenberg
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed P48q creation and annihilation modes and their Heisenberg brackets. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedCurrentIterate
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingCurrentZero
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedDualBases
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Module
import Batteries.Tactic.OpenPrivate

/-!
Bakalov–Kac, arXiv:math/0402315v3, (4.23) and the current-algebra restriction
condition of Proposition 4.2. The signed index k denotes the physical mode k/3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg

open P48qThirdTwistedField (Cartan Fock Mode State frequency creator annihilatorDual
  fixedDualBases pair_modes modeRoot creator_action annihilatorDual_action)
open P48qMomentumEnergy (Fixed physicalMomentum)
open P48qTwistedChargeAction (Momentum)
open ThirdEigenspacePairing (p48qAction p48qForm p48qBasis p48qOppositeBasis)
open MvPolynomial
open scoped BigOperators Matrix

open private zetaPrimitive formSymmetric formInvariant from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private abbrev differentiate (j : Mode) : Module.End ℂ Fock := (pderiv j).toLinearMap
private abbrev multiplyX (j : Mode) : Module.End ℂ Fock := LinearMap.mulLeft ℂ (X j)

/-- The coordinate Weyl relation, including distinct rows and distinct frequencies. -/
theorem coordinate_commutator (i j : Mode) :
    ⁅(pderiv i : Derivation ℂ Fock Fock).toLinearMap, LinearMap.mulLeft ℂ (X j : Fock)⁆ =
      if i = j then (1 : Module.End ℂ Fock) else 0 := by
  apply LinearMap.ext
  intro P
  change pderiv i (X j * P) - X j * pderiv i P =
    (if i = j then (1 : Module.End ℂ Fock) else 0) P
  rw [pderiv_mul]
  by_cases h : i = j
  · subst j
    rw [pderiv_X_self]
    simp
  · rw [pderiv_X_of_ne (Ne.symm h)]
    simp [h]

private theorem derivatives_commute (i j : Mode) : ⁅differentiate i, differentiate j⁆ = 0 := by
  apply LinearMap.ext
  intro P
  change pderiv i (pderiv j P) - pderiv j (pderiv i P) = 0
  exact sub_eq_zero.mpr (pderiv_comm i j P)

private theorem multiplications_commute (i j : Mode) : ⁅multiplyX i, multiplyX j⁆ = 0 := by
  apply LinearMap.ext
  intro P
  change X i * (X j * P) - X j * (X i * P) = 0
  apply sub_eq_zero.mpr
  ac_rfl

/-- Physical frequency of the variable with second coordinate n. -/
def scale (n : ℕ) : ℂ := ((n + 1 : ℕ) : ℂ) / 3

/-- A creation direction in one frequency slice in the variable basis. -/
def create (n : ℕ) (b : Fin 16 → ℂ) : Module.End ℂ Fock :=
  ∑ i, b i • multiplyX (i, n)

/-- An annihilation direction in one frequency slice in dual coordinates. -/
def annihilate (n : ℕ) (a : Fin 16 → ℂ) : Module.End ℂ Fock :=
  ∑ i, (scale n * a i) • differentiate (i, n)

/-- The pairing is the contraction of dual coordinates at equal cover frequency. -/
theorem annihilate_create_commutator (n m : ℕ) (a b : Fin 16 → ℂ) :
    ⁅annihilate n a, create m b⁆ =
      if n = m then (scale n * ∑ i, a i * b i) • (1 : Module.End ℂ Fock) else 0 := by
  classical
  simp only [annihilate, create, sum_lie_sum, smul_lie, lie_smul, coordinate_commutator,
    Prod.mk.injEq]
  by_cases h : n = m
  · subst m
    simp only [and_true, ite_true, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, smul_smul]
    rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (fun c : ℂ => c • (1 : Module.End ℂ Fock)) (by ring)
  · simp [h]

theorem annihilate_lie_annihilate (n m : ℕ) (a b : Fin 16 → ℂ) :
    ⁅annihilate n a, annihilate m b⁆ = 0 := by
  simp [annihilate, sum_lie_sum, smul_lie, lie_smul, derivatives_commute]

theorem create_lie_create (n m : ℕ) (a b : Fin 16 → ℂ) :
    ⁅create n a, create m b⁆ = 0 := by
  simp [create, sum_lie_sum, smul_lie, lie_smul, multiplications_commute]

private def root (n : ℕ) : ℂ := modeRoot (0, n)

private theorem root_cube (n : ℕ) : root n ^ 3 = 1 := by
  change (ζ ^ ((n + 1) % 3)) ^ 3 = 1
  rw [pow_right_comm, zetaPrimitive.pow_eq_one, one_pow]

private theorem cube_square {z : ℂ} (hz : z ^ 3 = 1) : (z ^ 2) ^ 2 = z := by
  calc
    (z ^ 2) ^ 2 = z ^ 3 * z := by ring
    _ = z := by rw [hz, one_mul]

/-- The Fourier projection to the eigenvalue z² for a cube root z. -/
def project (z : ℂ) (u : Cartan) : Cartan :=
  (3 : ℂ)⁻¹ • (u + z • p48qAction u + z ^ 2 • p48qAction (p48qAction u))

private theorem action_cube_apply (u : Cartan) : p48qAction (p48qAction (p48qAction u)) = u := by
  let c := Int.castRingHom ℂ
  let P := P48qFixedRankCertificateDraft.nebeOrderThree
  have h : p48qAction ^ 3 = 1 := by
    change (c.mapMatrix Pᵀ).toLin' ^ 3 = 1
    have hP : Pᵀ ^ 3 = 1 := by
      rw [← Matrix.transpose_pow, P48qFixedRankCertificateDraft.nebeOrderThree_cube,
        Matrix.transpose_one]
    rw [← Matrix.toLin'_pow, ← map_pow, hP, map_one, Matrix.toLin'_one,
      ← Module.End.one_eq_id]
  simpa only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, Module.End.one_apply]
    using congrArg (fun A : Module.End ℂ Cartan => A u) h

theorem project_action (z : ℂ) (hz : z ^ 3 = 1) (u : Cartan) :
    p48qAction (project z u) = z ^ 2 • project z u := by
  have h₁ : z ^ 2 * z = 1 := by rw [← pow_succ, hz]
  have h₂ : z ^ 2 * z ^ 2 = z := by rw [← pow_two, cube_square hz]
  rw [project, map_smul, smul_comm (z ^ 2) ((3 : ℂ)⁻¹)]
  apply congrArg (fun v : Cartan => (3 : ℂ)⁻¹ • v)
  simp only [map_smul, map_add, action_cube_apply, smul_add, smul_smul, h₁, h₂, one_smul]
  abel

private theorem third_smul_three (u : Cartan) : (3 : ℂ)⁻¹ • (u + u + u) = u := by
  have h : u + u + u = (3 : ℂ) • u := by module
  rw [h, smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul]

theorem project_of_action (z : ℂ) (hz : z ^ 3 = 1) (u : Cartan)
    (hu : p48qAction u = z ^ 2 • u) : project z u = u := by
  have h₁ : z • p48qAction u = u := by
    rw [hu, smul_smul, mul_comm z, ← pow_succ, hz, one_smul]
  have h₂ : z ^ 2 • p48qAction (p48qAction u) = u := by
    calc
      _ = z • p48qAction (z • p48qAction u) := by rw [map_smul, smul_smul, pow_two]
      _ = u := by rw [h₁, h₁]
  rw [project, h₂, h₁]
  exact third_smul_three u

private theorem fixed_action (u : Fixed) : p48qAction (u : Cartan) = (u : Cartan) := by
  simpa only [Fixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero] using u.property

private theorem pairing_project (z : ℂ) (u v : Cartan) (hv : p48qAction v = z • v) :
    p48qForm (project z u) v = p48qForm u v := by
  have h (w : Cartan) : z * p48qForm (p48qAction w) v = p48qForm w v := by
    simpa only [hv, LinearMap.BilinForm.smul_right] using formInvariant w v
  have hh : z ^ 2 * p48qForm (p48qAction (p48qAction u)) v = p48qForm u v := by
    rw [pow_two, mul_assoc, h, h]
  simp only [project, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left, h, hh]
  ring

private theorem project_adjoint (z : ℂ) (hz : z ^ 3 = 1) (u v : Cartan) :
    p48qForm (project z u) v = p48qForm u (project (z ^ 2) v) := by
  have h₁ : p48qForm (p48qAction u) v = p48qForm u (p48qAction (p48qAction v)) := by
    simpa only [action_cube_apply] using (formInvariant u (p48qAction (p48qAction v)))
  have h₂ : p48qForm (p48qAction (p48qAction u)) v = p48qForm u (p48qAction v) := by
    simpa only [action_cube_apply] using (formInvariant (p48qAction (p48qAction u)) v).symm
  simp only [project, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, cube_square hz, h₁, h₂]
  ring

/-- The projection in (4.23) on the signed cover, with eigenvalue ζ⁻ᵏ. -/
def projectAt : ℤ → Cartan → Cartan
  | .ofNat 0 => project 1
  | .ofNat (n + 1) => project (root n)
  | .negSucc n => project (root n ^ 2)

/-- The Fourier coefficient uses the signed residue k modulo three. -/
theorem projectAt_eq_fourier (k : ℤ) (u : Cartan) :
    projectAt k u = project (ζ ^ ((k % 3).toNat)) u := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      change project 1 u = project (ζ ^ 0) u
      rw [pow_zero]
    | succ n =>
      change project (ζ ^ ((n + 1) % 3)) u =
        project (ζ ^ ((((n + 1 : ℕ) : ℤ) % 3).toNat)) u
      have h : (((n + 1 : ℕ) : ℤ) % 3).toNat = (n + 1) % 3 :=
        Int.toNat_emod (Int.natCast_nonneg (n + 1)) (by decide : (0 : ℤ) ≤ 3)
      rw [h]
  | negSucc n =>
    change project ((ζ ^ ((n + 1) % 3)) ^ 2) u =
      project (ζ ^ ((Int.negSucc n % 3).toNat)) u
    apply congrArg (fun z : ℂ => project z u)
    by_cases h₀ : (n + 1) % 3 = 0
    · have h : ((Int.negSucc n % 3).toNat) = 0 := by omega
      rw [h₀, h, pow_zero, one_pow]
    by_cases h₁ : (n + 1) % 3 = 1
    · have h : ((Int.negSucc n % 3).toNat) = 2 := by omega
      rw [h₁, h, pow_one]
    have h₂ : (n + 1) % 3 = 2 := by omega
    have h : ((Int.negSucc n % 3).toNat) = 1 := by omega
    rw [h₂, h, pow_one, cube_square zetaPrimitive.pow_eq_one]

/-- Pairing against the creator gives the positive mode's dual coordinate. -/
def annCoordinates (u : Cartan) (n : ℕ) (i : Fin 16) : ℂ :=
  p48qForm u (creator fixedDualBases (i, n))

/-- Pairing against the dual basis gives the negative mode's creation coordinate. -/
def creCoordinates (u : Cartan) (n : ℕ) (i : Fin 16) : ℂ :=
  p48qForm u (annihilatorDual fixedDualBases (i, n))

private theorem transport_creator_basis (n : ℕ) {z : ℂ} (hz : z = root n)
    (e : Module.Basis (Fin 16) ℂ (p48qAction.eigenspace z))
    (he : ∀ i, (e i : Cartan) = creator fixedDualBases (i, n)) :
    ∃ e : Module.Basis (Fin 16) ℂ (p48qAction.eigenspace (root n)),
      ∀ i, (e i : Cartan) = creator fixedDualBases (i, n) := by
  subst z
  exact ⟨e, he⟩

private theorem exists_creator_basis (n : ℕ) :
    ∃ e : Module.Basis (Fin 16) ℂ (p48qAction.eigenspace (root n)),
      ∀ i, (e i : Cartan) = creator fixedDualBases (i, n) := by
  by_cases h₀ : (n + 1) % 3 = 0
  · refine transport_creator_basis n (z := 1) ?_ fixedDualBases.creators (fun i => ?_)
    · simp only [root, modeRoot, frequency, h₀, pow_zero]
    · simp only [creator, frequency, ite_eq_left h₀]
  by_cases h₁ : (n + 1) % 3 = 1
  · refine transport_creator_basis n (z := ζ) ?_ (p48qBasis zetaPrimitive) (fun i => ?_)
    · simp only [root, modeRoot, frequency, h₁, pow_one]
    · simp only [creator, frequency, ite_eq_right h₀, ite_eq_left h₁]
  have h₂ : (n + 1) % 3 = 2 := by omega
  refine transport_creator_basis n (z := ζ ^ 2) ?_ (p48qOppositeBasis zetaPrimitive)
    (fun i => ?_)
  · simp only [root, modeRoot, frequency, h₂]
  · simp only [creator, frequency, ite_eq_right h₀, ite_eq_right h₁]

/-- The Gram-dual expansion of the negative-mode projection. -/
theorem project_negative_eq_sum (n : ℕ) (v : Cartan) :
    projectAt (.negSucc n) v =
      ∑ i, creCoordinates v n i • creator fixedDualBases (i, n) := by
  classical
  obtain ⟨e, he⟩ := exists_creator_basis n
  have hcube : (root n ^ 2) ^ 3 = 1 := by rw [pow_right_comm, root_cube, one_pow]
  have hact : p48qAction (project (root n ^ 2) v) = root n • project (root n ^ 2) v := by
    simpa only [cube_square (root_cube n)] using project_action _ hcube v
  let v' : p48qAction.eigenspace (root n) :=
    ⟨project (root n ^ 2) v, Module.End.mem_eigenspace_iff.mpr hact⟩
  have hsum : (∑ i, e.repr v' i • (e i : Cartan)) = (v' : Cartan) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg (fun x : p48qAction.eigenspace (root n) => (x : Cartan)) (e.sum_repr v')
  have hcoord (i : Fin 16) : creCoordinates v n i = e.repr v' i := by
    have hact : p48qAction (annihilatorDual fixedDualBases (i, n)) =
        root n ^ 2 • annihilatorDual fixedDualBases (i, n) :=
      annihilatorDual_action fixedDualBases (i, n)
    calc
      _ = p48qForm (v' : Cartan) (annihilatorDual fixedDualBases (i, n)) :=
        (pairing_project (root n ^ 2) v _ hact).symm
      _ = p48qForm (∑ j, e.repr v' j • (e j : Cartan))
          (annihilatorDual fixedDualBases (i, n)) := by rw [hsum]
      _ = _ := by
        rw [map_sum, LinearMap.sum_apply]
        simp only [LinearMap.BilinForm.smul_left, he, pair_modes, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  refine hsum.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hcoord, he]

private theorem negative_pairing (n : ℕ) (u v : Cartan) :
    p48qForm (projectAt (.negSucc n) u) v =
      ∑ i, creCoordinates u n i * annCoordinates v n i := by
  rw [project_negative_eq_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.smul_left]
  exact congrArg (creCoordinates u n i * ·) (formSymmetric.eq _ _)

/-- The Gram-dual contraction in the positive–negative commutator. -/
theorem positive_pairing (n : ℕ) (u v : Cartan) :
    p48qForm (projectAt (.ofNat (n + 1)) u) v =
      ∑ i, annCoordinates u n i * creCoordinates v n i := by
  change p48qForm (project (root n) u) v = _
  rw [project_adjoint _ (root_cube n), formSymmetric.eq u]
  change p48qForm (projectAt (.negSucc n) v) u = _
  rw [negative_pairing]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private def fixedProjection (u : Cartan) : Fixed :=
  ⟨projectAt 0 u, by
    simp only [Fixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    change p48qAction (project 1 u) = project 1 u
    simpa only [one_pow, one_smul] using project_action 1 (one_pow 3) u⟩

private abbrev onState (A : Module.End ℂ Fock) : Module.End ℂ State :=
  Finsupp.mapRange.linearMap A

private theorem onState_apply (A : Module.End ℂ Fock) (w : State) (p : Momentum) :
    onState A w p = A (w p) := by
  rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]

private abbrev coverSlot (k : ℤ) : ℕ := k.natAbs - 1

/-- The actual current on the full Fock and momentum state at signed cover index k. -/
def mode (u : Cartan) (k : ℤ) : Module.End ℂ State :=
  if k = 0 then P48qFixedCurrentIterate.zeroMode (fixedProjection u)
  else if 0 < k then onState (annihilate (coverSlot k) (annCoordinates u (coverSlot k)))
  else onState (create (coverSlot k) (creCoordinates u (coverSlot k)))

private theorem ofNat_succ_pos (n : ℕ) : 0 < Int.ofNat (n + 1) := by
  change ((0 : ℕ) : ℤ) < ((n + 1 : ℕ) : ℤ)
  exact Int.ofNat_lt.mpr (Nat.succ_pos n)

private theorem mode_of_pos (u : Cartan) {k : ℤ} (hk : 0 < k) :
    mode u k = onState (annihilate (coverSlot k) (annCoordinates u (coverSlot k))) := by
  rw [mode, ite_eq_right (ne_of_gt hk), ite_eq_left hk]

private theorem mode_of_neg (u : Cartan) {k : ℤ} (hk : k < 0) :
    mode u k = onState (create (coverSlot k) (creCoordinates u (coverSlot k))) := by
  rw [mode, ite_eq_right (ne_of_lt hk), ite_eq_right hk.not_gt]

private theorem mode_at_pos (u : Cartan) (n : ℕ) :
    mode u (.ofNat (n + 1)) = onState (annihilate n (annCoordinates u n)) :=
  mode_of_pos u (ofNat_succ_pos n)

private theorem mode_at_neg (u : Cartan) (n : ℕ) :
    mode u (.negSucc n) = onState (create n (creCoordinates u n)) :=
  mode_of_neg u (Int.negSucc_lt_zero n)

theorem mode_zero_apply (u : Cartan) (w : State) (p : Momentum) :
    mode u 0 w p = p48qForm u (physicalMomentum p : Cartan) • w p := by
  rw [mode, ite_eq_left (rfl : (0 : ℤ) = 0), P48qFixedCurrentIterate.zeroMode_apply]
  change p48qForm (project 1 u) (physicalMomentum p : Cartan) • w p = _
  rw [pairing_project 1 u (physicalMomentum p : Cartan)
    (by simpa only [one_smul] using fixed_action (physicalMomentum p))]

theorem mode_positive_apply (u : Cartan) (n : ℕ) (w : State) (p : Momentum) :
    mode u (.ofNat (n + 1)) w p =
      ∑ i, (scale n * annCoordinates u n i) • pderiv (i, n) (w p) := by
  simp only [mode_at_pos, onState_apply, annihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    Derivation.coeFn_coe]

theorem mode_negative_apply (u : Cartan) (n : ℕ) (w : State) (p : Momentum) :
    mode u (.negSucc n) w p = ∑ i, creCoordinates u n i • (X (i, n) * w p) := by
  simp only [mode_at_neg, onState_apply, create, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.mulLeft_apply]

/-- At a fixed index the current action is complex linear in the Cartan argument. -/
def modeLinear (k : ℤ) : Cartan →ₗ[ℂ] Module.End ℂ State where
  toFun u := mode u k
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply Finsupp.ext
    intro p
    simp only [LinearMap.add_apply, Finsupp.add_apply]
    cases k with
    | ofNat n =>
      cases n with
      | zero =>
        change mode (u + v) 0 w p = mode u 0 w p + mode v 0 w p
        simp only [mode_zero_apply, LinearMap.BilinForm.add_left, add_smul]
      | succ n =>
        simp only [mode_positive_apply, annCoordinates, LinearMap.BilinForm.add_left,
          mul_add, add_smul, Finset.sum_add_distrib]
    | negSucc n =>
      simp only [mode_negative_apply, creCoordinates, LinearMap.BilinForm.add_left,
        add_smul, Finset.sum_add_distrib]
  map_smul' c u := by
    apply LinearMap.ext
    intro w
    apply Finsupp.ext
    intro p
    simp only [RingHom.id_apply, LinearMap.smul_apply, Finsupp.smul_apply]
    cases k with
    | ofNat n =>
      cases n with
      | zero =>
        change mode (c • u) 0 w p = c • mode u 0 w p
        simp only [mode_zero_apply, LinearMap.BilinForm.smul_left, smul_smul]
      | succ n =>
        simp only [mode_positive_apply, annCoordinates, LinearMap.BilinForm.smul_left,
          Finset.smul_sum, smul_smul, mul_left_comm (scale n) c]
    | negSucc n =>
      simp only [mode_negative_apply, creCoordinates, LinearMap.BilinForm.smul_left,
        Finset.smul_sum, smul_smul]

/-- A current at k depends only on the Fourier component at that signed index. -/
theorem mode_projectAt (u : Cartan) (k : ℤ) : mode (projectAt k u) k = mode u k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero =>
      apply LinearMap.ext
      intro w
      apply Finsupp.ext
      intro p
      change mode (project 1 u) 0 w p = mode u 0 w p
      simp only [mode_zero_apply]
      rw [pairing_project 1 u (physicalMomentum p : Cartan)
        (by simpa only [one_smul] using fixed_action (physicalMomentum p))]
    | succ n =>
      have h (i : Fin 16) : annCoordinates (project (root n) u) n i = annCoordinates u n i :=
        pairing_project _ _ _ (creator_action fixedDualBases (i, n))
      simp only [mode_at_pos, projectAt, annihilate, h]
  | negSucc n =>
    have h (i : Fin 16) :
        creCoordinates (project (root n ^ 2) u) n i = creCoordinates u n i :=
      pairing_project _ _ _ (annihilatorDual_action fixedDualBases (i, n))
    simp only [mode_at_neg, projectAt, create, h]

private theorem onState_commutator_apply (A B : Module.End ℂ Fock) (w : State) (p : Momentum) :
    ⁅onState A, onState B⁆ w p = ⁅A, B⁆ (w p) := by
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply,
    onState_apply]

private theorem zero_lie_mode (u v : Cartan) (k : ℤ) : ⁅mode u 0, mode v k⁆ = 0 := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro p
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply,
    mode_zero_apply, LinearMap.zero_apply, Finsupp.zero_apply]
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp only [mode_of_neg v hk, onState_apply, mode_zero_apply, map_smul, sub_self]
  · simp only [mode_zero_apply]
    rw [smul_comm, sub_self]
  · simp only [mode_of_pos v hk, onState_apply, mode_zero_apply, map_smul, sub_self]

private theorem mode_pos_neg_apply (u v : Cartan) (n m : ℕ) (w : State) (p : Momentum) :
    ⁅mode u (.ofNat (n + 1)), mode v (.negSucc m)⁆ w p =
      if n = m then
        (scale n * p48qForm (projectAt (.ofNat (n + 1)) u) v) • w p
      else 0 := by
  rw [mode_at_pos, mode_at_neg, onState_commutator_apply, annihilate_create_commutator,
    positive_pairing]
  by_cases h : n = m <;> simp [h]

private theorem opposite_cover_iff (a b : ℕ) :
    Int.ofNat (a + 1) + Int.negSucc b = 0 ↔ a = b := by
  change (((a + 1 : ℕ) : ℤ) + -((b + 1 : ℕ) : ℤ) = 0) ↔ a = b
  rw [← sub_eq_add_neg, sub_eq_zero, Int.ofNat_inj]
  exact Nat.succ_inj

private theorem scale_pos (n : ℕ) : (Int.ofNat (n + 1) : ℂ) / 3 = scale n := by
  change ((((n + 1 : ℕ) : ℤ) : ℂ) / 3) = ((n + 1 : ℕ) : ℂ) / 3
  rw [Int.cast_natCast]

private theorem scale_neg (n : ℕ) : (Int.negSucc n : ℂ) / 3 = -scale n := by
  change ((-Int.ofNat (n + 1) : ℤ) : ℂ) / 3 = -scale n
  rw [Int.cast_neg, neg_div, scale_pos]

/-- Equation (4.23) on every momentum summand, with physical frequency k/3
and the Fourier projection on the first Cartan argument. -/
theorem mode_commutator_apply (u v : Cartan) (k l : ℤ) (w : State) (p : Momentum) :
    ⁅mode u k, mode v l⁆ w p =
      if k + l = 0 then (((k : ℂ) / 3) * p48qForm (projectAt k u) v) • w p else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [zero_lie_mode]
  by_cases hl : l = 0
  · subst l
    have hright : ⁅mode u k, mode v 0⁆ = 0 := by
      rw [← lie_skew, zero_lie_mode, neg_zero]
    simp [hright, hk]
  cases k with
  | ofNat a =>
    cases a with
    | zero => exact (hk rfl).elim
    | succ a =>
      cases l with
      | ofNat b =>
        cases b with
        | zero => exact (hl rfl).elim
        | succ b =>
          have hsum := ne_of_gt (Int.add_pos (ofNat_succ_pos a) (ofNat_succ_pos b))
          rw [ite_eq_right hsum, mode_at_pos u a, mode_at_pos v b, onState_commutator_apply,
            annihilate_lie_annihilate, LinearMap.zero_apply]
      | negSucc b =>
        rw [mode_pos_neg_apply, scale_pos]
        by_cases h : a = b
        · simp only [ite_eq_left h, ite_eq_left ((opposite_cover_iff a b).mpr h)]
        · simp only [ite_eq_right h, ite_eq_right (mt (opposite_cover_iff a b).mp h)]
  | negSucc a =>
    cases l with
    | ofNat b =>
      cases b with
      | zero => exact (hl rfl).elim
      | succ b =>
        have hop : Int.negSucc a + Int.ofNat (b + 1) = 0 ↔ b = a := by
          rw [add_comm, opposite_cover_iff]
        rw [← lie_skew, LinearMap.neg_apply, Finsupp.neg_apply, mode_pos_neg_apply]
        by_cases h : b = a
        · subst b
          rw [ite_eq_left (rfl : a = a), ite_eq_left (hop.mpr rfl), scale_neg]
          have hp : p48qForm (projectAt (.ofNat (a + 1)) v) u =
              p48qForm (projectAt (.negSucc a) u) v := by
            rw [positive_pairing, negative_pairing]
            exact Finset.sum_congr rfl fun i _ => mul_comm _ _
          rw [hp, neg_mul, neg_smul]
        · simp only [ite_eq_right h, ite_eq_right (mt hop.mp h), neg_zero]
    | negSucc b =>
      have hsum := ne_of_lt (Int.add_neg (Int.negSucc_lt_zero a) (Int.negSucc_lt_zero b))
      rw [ite_eq_right hsum, mode_at_neg u a, mode_at_neg v b, onState_commutator_apply,
        create_lie_create, LinearMap.zero_apply]

/-- The level-one central element acts as the identity on the full State. -/
theorem mode_commutator (u v : Cartan) (k l : ℤ) :
    ⁅mode u k, mode v l⁆ =
      if k + l = 0 then (((k : ℂ) / 3) * p48qForm (projectAt k u) v) • (1 : Module.End ℂ State)
      else 0 := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro p
  rw [mode_commutator_apply]
  by_cases h : k + l = 0 <;> simp [h, Finsupp.smul_apply]

/-- The bound is uniform over all Cartan directions and all momentum summands of w. -/
theorem mode_eq_zero_above_coverBound (w : State) (u : Cartan) (k : ℤ)
    (hk : (P48qFixedCurrentIterate.coverBound w : ℤ) < k) :
    mode u k w = 0 := by
  have hk₀ : 0 < k := lt_of_le_of_lt (Int.natCast_nonneg _) hk
  have habs : P48qFixedCurrentIterate.coverBound w < k.natAbs := by
    apply Int.ofNat_lt.mp
    rw [Int.natAbs_of_nonneg hk₀.le]
    exact hk
  apply Finsupp.ext
  intro p
  rw [mode_of_pos u hk₀, onState_apply, annihilate, LinearMap.sum_apply, Finsupp.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [LinearMap.smul_apply, Derivation.coeFn_coe]
  have hi : (i, coverSlot k) ∉ (w p).vars := by
    intro hv
    have hp : p ∈ w.support := Finsupp.mem_support_iff.mpr (by
      intro hz
      simp [hz] at hv)
    have hl : frequency (i, coverSlot k) ≤ (w p).vars.sup frequency := Finset.le_sup hv
    have hg : (w p).vars.sup frequency ≤ P48qFixedCurrentIterate.coverBound w :=
      Finset.le_sup (f := fun q => (w q).vars.sup frequency) hp
    have hf : frequency (i, coverSlot k) = k.natAbs :=
      P48qMovingCurrentZero.frequency_coverVariable i (ne_of_gt hk₀)
    rw [hf] at hl
    exact (not_le_of_gt habs) (hl.trans hg)
  rw [pderiv_eq_zero_of_notMem_vars hi, smul_zero]

/-- Every nonzero positive mode lies in a finite interval depending only on the state. -/
theorem positive_mode_support_subset (w : State) (u : Cartan) :
    {k : ℤ | 0 < k ∧ mode u k w ≠ 0} ⊆
      (Finset.Ioc 0 (P48qFixedCurrentIterate.coverBound w : ℤ) : Set ℤ) := by
  rintro k ⟨hk, hmode⟩
  change k ∈ Finset.Ioc 0 (P48qFixedCurrentIterate.coverBound w : ℤ)
  exact Finset.mem_Ioc.mpr
    ⟨hk, le_of_not_gt (fun h => hmode (mode_eq_zero_above_coverBound w u k h))⟩

/-- In the restriction condition of Proposition 4.2, the same cutoff
works for every Cartan direction on a given state. -/
theorem restricted_positive_modes (w : State) :
    ∃ N : ℤ, ∀ (u : Cartan) (k : ℤ), N < k → mode u k w = 0 :=
  ⟨P48qFixedCurrentIterate.coverBound w, fun u k hk => mode_eq_zero_above_coverBound w u k hk⟩

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
