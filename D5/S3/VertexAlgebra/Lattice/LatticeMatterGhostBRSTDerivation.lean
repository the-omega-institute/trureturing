/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBRSTDerivation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostBRSTDerivation
   mirror-E: none(waiver:original-coupled-BRST)
   anchors: []
   utility: none
   digest: The original coupled BRST charge acts on every homogeneous field by superderivation. -/

/-
Original all-state total-charge field superderivation. The saved source
candidate has been reconciled against the released native coupled field at
9443abecae3e805d68a61bbcbb529117aa4c7d9a. No independent review, freeze,
CI, official acceptance or full-physics completion is claimed here.

The ORIGINAL carrier, pointwise tensor field, vacuum, translation, parity,
current and totalCharge are imported unchanged. The coupled Lean supplier
has SHA-256 eef48a71479219a7ede377f6f40ab4e8c46fa40fd2a8b5bf23c96680aba87292.

Classical construction: signed zero-residue locality (Dong's argument) and
creative vacuum uniqueness. The finite shift-polynomial proof is adapted
from StateFieldResidueReconstruction.residue_nonnegative_locality; that
UNSIGNED theorem is NOT applied to a signed field. Its public sign-free
deltaEnd_iterate_apply identity is reused. Attribution of the residue proof
pattern remains Scott Carnahan / the original Apache-2.0 supplier; no
literature novelty is asserted.

proof_shape: totalCharge_field_superderivation, signed_zero_residue_locality,
polynomial_clearance, creative_unique: content
admission_basis: escape-witness
escape_witness: Explicit signed operator Jacobi expansion has coefficients
(e,f,g,fg); two independent polynomial annihilators imply the uniform
zero-residue locality order M+N+L. Covariance recursively kills every negative
vacuum coefficient of the discrepancy. Extraction at second index -1 and
ACTUAL even/odd decomposition kill its action on every original input.

All auxiliary definitions/lemmas are private and consumed on that live path.
They receive no independent content credit. First-freeze semantic classification remains
subject to independent review.
No finite support of endomorphism families, infinite-sum interchange, full
signed field Jacobi, charge square-zero, inverse Gram, rank or H condition
occurs. This is only the zeroth-residue bridge needed by the original charge.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction

set_option autoImplicit false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation

open LatticeGeneratingFieldLocality LatticeMatterGhostCoupling
open D5.S3.Quantum.Fermionic
open FieldNormalProductLocality
open StateFieldResidueReconstruction (deltaEnd_iterate_apply)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (parity_ket)

noncomputable section

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

private def signedComm (e : ℂ) (A B : VertexOperator ℂ V) :
    ℤ → ℤ → Module.End ℂ V :=
  fun i j => (A[[i]]) * (B[[j]]) - e • ((B[[j]]) * (A[[i]]))

/- The zero residue is a field because B is lower truncated on BOTH x and
A_0 x. There is no support assertion about the operator-valued family. -/
private def zeroResidue (e : ℂ) (A B : VertexOperator ℂ V) :
    VertexOperator ℂ V :=
  VertexOperator.of_coeff
    (fun power => (A[[0]]) * (B[[-power - 1]]) -
      e • ((B[[-power - 1]]) * (A[[0]]))) (by
    intro x
    refine ⟨min ((HahnModule.of ℂ).symm (B x)).order
      ((HahnModule.of ℂ).symm (B ((A[[0]]) x))).order, ?_⟩
    intro power hp
    by_contra hsmall
    have h1 : (B[[-power - 1]]) x = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    have h2 : (B[[-power - 1]]) ((A[[0]]) x) = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hp (by
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        h1, h2, map_zero, smul_zero, sub_self]))

private theorem zeroResidue_modes (e : ℂ) (A B : VertexOperator ℂ V) (n : ℤ) :
    ((zeroResidue e A B)[[n]]) =
      (A[[0]]) * (B[[n]]) - e • ((B[[n]]) * (A[[0]])) := by
  apply LinearMap.ext
  intro x
  change ((A[[0]]) * (B[[-(-n - 1) - 1]]) -
    e • ((B[[-(-n - 1) - 1]]) * (A[[0]]))) x = _
  rw [show -(-n - 1) - 1 = n by omega]

/- An organizational linear intertwining fact, used only in the signed
residue proof. Its induction has no independent admission/content credit. -/
private theorem map_power {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (S : Module.End ℂ E) (T : Module.End ℂ F) (L : E →ₗ[ℂ] F)
    (h : ∀ x, L (S x) = T (L x)) (n : ℕ) (x : E) :
    L ((S ^ n) x) = (T ^ n) (L x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [h, ih]

/- This is the finite polynomial clearance actually consumed below.
X=(x-y), Z=(y-z), X+Z=(x-z). The safe, nonoptimal exponent avoids any
special treatment of locality order zero. All sums here are finite. -/
private theorem polynomial_clearance {E : Type*} [AddCommGroup E] [Module ℂ E]
    (X Z : Module.End ℂ E) (commuting : Commute X Z) (v : E)
    (M N L : ℕ) (hx : (X ^ N) v = 0)
    (hcz : ((X + Z) ^ M * Z ^ L) v = 0) :
    (Z ^ (M + N + L)) v = 0 := by
  let C := X + Z
  have cx : Commute C X := (Commute.refl X).add_left commuting.symm
  have high (k : ℕ) (hk : N ≤ k) : (X ^ k) v = 0 := by
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, (Commute.refl X).pow_pow _ _ |>.eq,
      Module.End.mul_apply, hx, map_zero]
  have low (k : ℕ) (hk : M ≤ k) : (C ^ k * Z ^ L) v = 0 := by
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, (Commute.refl C).pow_pow _ _ |>.eq,
      mul_assoc, Module.End.mul_apply, hcz, map_zero]
  have minusCommute : Commute C (-X) := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun A : Module.End ℂ E => A x) cx.eq
    simpa only [Module.End.mul_apply, LinearMap.neg_apply, map_neg]
      using congrArg Neg.neg h
  have expansion : Z ^ (M + N) =
      ∑ k ∈ Finset.range (M + N + 1),
        C ^ k * (-X) ^ (M + N - k) * (M + N).choose k := by
    have h := minusCommute.add_pow (M + N)
    have hc : C + -X = Z := by dsimp [C]; abel
    rw [hc] at h
    exact h
  have sign (k : ℕ) : (-X) ^ k = ((-1 : ℂ) ^ k) • X ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ih, pow_succ']
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        mul_smul, neg_one_smul, map_smul, pow_succ', smul_neg]
  rw [pow_add, expansion, Finset.sum_mul, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [sign, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    Algebra.smul_mul_assoc, LinearMap.smul_apply]
  simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  by_cases large : M ≤ k
  · have hv : (C ^ k) ((X ^ (M + N - k)) ((Z ^ L) v)) = 0 := by
      change (C ^ k * X ^ (M + N - k) * Z ^ L) v = 0
      rw [(cx.pow_pow _ _).eq, mul_assoc, Module.End.mul_apply,
        low k large, map_zero]
    simp [hv]
  · have bound : N ≤ M + N - k := by
      have within : k ≤ M + N := by simpa using Finset.mem_range.mp hk
      omega
    have hv : (X ^ (M + N - k)) ((Z ^ L) v) = 0 := by
      change (X ^ (M + N - k) * Z ^ L) v = 0
      rw [(commuting.pow_pow _ _).eq, Module.End.mul_apply,
        high _ bound, map_zero]
    simp [hv]

/- Minimal signed Dong lemma: ONLY the zeroth residue, ONLY three actual
pair-locality hypotheses. No field Jacobi is assumed. e,f,g are independent
scalars; in the live application they are the three original parity signs. -/
private theorem signed_zero_residue_locality
    (e f g : ℂ) (A B C : VertexOperator ℂ V)
    (hab : ∃ N : ℕ, delta^[N] (signedComm e A B) = 0)
    (hac : ∃ M : ℕ, delta^[M] (signedComm f A C) = 0)
    (hbc : ∃ L : ℕ, delta^[L] (signedComm g B C) = 0) :
    ∃ K : ℕ, delta^[K] (signedComm (f * g) (zeroResidue e A B) C) = 0 := by
  obtain ⟨N, hn⟩ := hab
  obtain ⟨M, hm⟩ := hac
  obtain ⟨L, hl⟩ := hbc
  have hn' : (deltaEnd ^ N) (signedComm e A B) = 0 := by
    funext i j
    rw [deltaEnd_iterate_apply]
    exact congrFun (congrFun hn i) j
  have hm' : (deltaEnd ^ M) (signedComm f A C) = 0 := by
    funext i j
    rw [deltaEnd_iterate_apply]
    exact congrFun (congrFun hm i) j
  have hl' : (deltaEnd ^ L) (signedComm g B C) = 0 := by
    funext i j
    rw [deltaEnd_iterate_apply]
    exact congrFun (congrFun hl i) j
  let X : Module.End ℂ (Triple V) := plainXY
  let Z : Module.End ℂ (Triple V) := plainYZ
  let U := X + Z
  have xz : Commute X Z := by
    apply LinearMap.ext
    intro d
    funext i j k
    dsimp [X, Z, plainXY, plainYZ, shiftXY, shiftYZ]
    abel
  have uz : Commute U Z := xz.add_left (Commute.refl Z)
  have lawAB (v : V) (side : Bool) (d : ℤ → ℤ → Module.End ℂ V) :
      liftAB C v side (deltaEnd d) = X (liftAB C v side d) := by
    funext i j k
    dsimp [liftAB, deltaEnd, delta, X, plainXY, shiftXY]
    cases side <;> simp [map_sub]
  have lawAC (v : V) (side : Bool) (d : ℤ → ℤ → Module.End ℂ V) :
      liftAC B v side (deltaEnd d) = U (liftAC B v side d) := by
    funext i j k
    dsimp [liftAC, deltaEnd, delta, U, X, Z, plainXY, plainYZ, shiftXY, shiftYZ]
    cases side <;> simp [map_sub]
  have lawBC (v : V) (side : Bool) (d : ℤ → ℤ → Module.End ℂ V) :
      liftBC A v side (deltaEnd d) = Z (liftBC A v side d) := by
    funext i j k
    dsimp [liftBC, deltaEnd, delta, Z, plainYZ, shiftYZ]
    cases side <;> simp [map_sub]
  refine ⟨M + N + L, ?_⟩
  funext i j
  apply LinearMap.ext
  intro v
  let d := liftAB C v true (signedComm e A B) -
    (f * g) • liftAB C v false (signedComm e A B)
  let ac := g • liftAC B v true (signedComm f A C) -
    e • liftAC B v false (signedComm f A C)
  let bc := liftBC A v true (signedComm g B C) -
    (e * f) • liftBC A v false (signedComm g B C)
  have signedJacobi : d = ac + bc := by
    funext a b c
    dsimp [d, ac, bc, liftAB, liftAC, liftBC, signedComm]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      map_sub, map_smul, smul_sub, smul_smul]
    module
  have hd : (X ^ N) d = 0 := by
    dsimp only [d]
    rw [map_sub, map_smul,
      ← map_power deltaEnd X (liftAB C v true) (lawAB v true),
      ← map_power deltaEnd X (liftAB C v false) (lawAB v false), hn']
    simp
  have hac' : (U ^ M) ac = 0 := by
    dsimp only [ac]
    rw [map_sub, map_smul, map_smul,
      ← map_power deltaEnd U (liftAC B v true) (lawAC v true),
      ← map_power deltaEnd U (liftAC B v false) (lawAC v false), hm']
    simp
  have hbc' : (Z ^ L) bc = 0 := by
    dsimp only [bc]
    rw [map_sub, map_smul,
      ← map_power deltaEnd Z (liftBC A v true) (lawBC v true),
      ← map_power deltaEnd Z (liftBC A v false) (lawBC v false), hl']
    simp
  have hprod : (U ^ M * Z ^ L) d = 0 := by
    rw [signedJacobi, map_add]
    have ha : (U ^ M * Z ^ L) ac = 0 := by
      rw [(uz.pow_pow _ _).eq, Module.End.mul_apply, hac', map_zero]
    have hb : (U ^ M * Z ^ L) bc = 0 := by
      rw [Module.End.mul_apply, hbc', map_zero]
    rw [ha, hb, add_zero]
  have killed : (Z ^ (M + N + L)) d = 0 :=
    polynomial_clearance X Z xz d M N L hd hprod
  let extract : Triple V →ₗ[ℂ] (ℤ → ℤ → V) := {
    toFun d := d 0
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have extractLaw (d : Triple V) : extract (Z d) = plainDelta (extract d) := rfl
  have evaluateLaw (d : ℤ → ℤ → Module.End ℂ V) :
      evaluate v (deltaEnd d) = plainDelta (evaluate v d) := rfl
  have connection : extract d =
      evaluate v (signedComm (f * g) (zeroResidue e A B) C) := by
    funext a b
    dsimp [extract, d, liftAB, evaluate, signedComm]
    rw [zeroResidue_modes]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      map_sub, map_smul]
  have hk := congrArg (fun d : Triple V => extract d) killed
  change extract ((Z ^ (M + N + L)) d) = extract 0 at hk
  rw [map_power Z plainDelta extract extractLaw, connection,
    ← map_power deltaEnd plainDelta (evaluate v) evaluateLaw, map_zero] at hk
  have hp := congrFun (congrFun hk i) j
  change ((deltaEnd ^ (M + N + L))
    (signedComm (f * g) (zeroResidue e A B) C)) i j v = 0 at hp
  rw [deltaEnd_iterate_apply] at hp
  exact hp

private theorem local_sub (e : ℂ) (A B C : VertexOperator ℂ V)
    (ha : ∃ M : ℕ, delta^[M] (signedComm e A C) = 0)
    (hb : ∃ N : ℕ, delta^[N] (signedComm e B C) = 0) :
    ∃ K : ℕ, delta^[K] (signedComm e (A - B) C) = 0 := by
  obtain ⟨M, hm⟩ := ha
  obtain ⟨N, hn⟩ := hb
  have hm' := FiniteFieldLocality.monotone (signedComm e A C)
    M (max M N) (le_max_left _ _) hm
  have hn' := FiniteFieldLocality.monotone (signedComm e B C)
    N (max M N) (le_max_right _ _) hn
  have split : signedComm e (A - B) C = signedComm e A C - signedComm e B C := by
    funext i j
    simp only [signedComm, map_sub, Pi.sub_apply, mul_sub, sub_mul, smul_sub]
    module
  refine ⟨max M N, ?_⟩
  funext i j
  rw [← deltaEnd_iterate_apply, split, map_sub]
  simp only [Pi.sub_apply, deltaEnd_iterate_apply, hm', hn', Pi.zero_apply, sub_self]

private theorem parity_square (D : LatticeData) (x : State D) :
    LatticeMatterGhostStateField.parity D
      (LatticeMatterGhostStateField.parity D x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul v a =>
    simp only [LatticeMatterGhostStateField.parity, TensorProduct.map_tmul,
      LinearMap.id_apply]
    have h := LinearMap.congr_fun CountableOccupationFock.parity_involution a
    change CountableOccupationFock.parity (CountableOccupationFock.parity a) = a at h
    rw [h]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

/- The only relative uniqueness fact needed: a creative covariant field with
zero initial state and signed locality against each homogeneous ORIGINAL Y
is zero. There is no image-of-Y assumption on F. -/
private theorem creative_unique (D : LatticeData) (r : ℕ)
    (F : VertexOperator ℂ (State D))
    (creative : ∀ n : ℤ, 0 ≤ n → (F[[n]]) (LatticeMatterGhostStateField.vacuum D) = 0)
    (initial : (F[[-1]]) (LatticeMatterGhostStateField.vacuum D) = 0)
    (covariant : ∀ n : ℤ,
      LatticeMatterGhostStateField.translation D * (F[[n]]) -
        (F[[n]]) * LatticeMatterGhostStateField.translation D =
          -(n : ℂ) • (F[[n - 1]]))
    (locality : ∀ (x : State D) (q : ℕ),
      LatticeMatterGhostStateField.parity D x = (-1 : ℂ)^q • x →
        ∃ N : ℕ, delta^[N] (signedComm ((-1 : ℂ)^(r*q)) F
          (LatticeMatterGhostStateField.Y D x)) = 0) : F = 0 := by
  have original := LatticeMatterGhostStateField.stateField_vacuum_creation D
  have negative (k : ℕ) :
      (F[[-(k : ℤ) - 1]]) (LatticeMatterGhostStateField.vacuum D) = 0 := by
    induction k with
    | zero => simpa using initial
    | succ k ih =>
      have h := LinearMap.congr_fun (covariant (-(k : ℤ) - 1))
        (LatticeMatterGhostStateField.vacuum D)
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        ih, original.2.2.2, map_zero, sub_self] at h
      rw [show -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 by omega] at h
      have scalar : -((-(k : ℤ) - 1 : ℤ) : ℂ) = (k : ℂ) + 1 := by
        push_cast
        ring
      rw [scalar] at h
      have nonzero : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      exact (smul_eq_zero.mp h.symm).resolve_left nonzero
  have vacuumZero (n : ℤ) :
      (F[[n]]) (LatticeMatterGhostStateField.vacuum D) = 0 := by
    by_cases hn : 0 ≤ n
    · exact creative n hn
    · let k := (-n - 1).toNat
      rw [show n = -(k : ℤ) - 1 by dsimp [k]; omega]
      exact negative k
  have evaluateDelta (d : ℤ → ℤ → Module.End ℂ (State D)) (N : ℕ) :
      delta^[N] (fun i j => d i j (LatticeMatterGhostStateField.vacuum D)) =
        fun i j => (delta^[N] d) i j (LatticeMatterGhostStateField.vacuum D) := by
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext i j
      simp only [delta, LinearMap.sub_apply]
  have rightTail (d : ℤ → ℤ → State D)
      (h : ∀ i j : ℤ, 0 ≤ j → d i j = 0) (N : ℕ) :
      ∀ i j : ℤ, 0 ≤ j → (delta^[N] d) i j = 0 := by
    induction N with
    | zero => exact h
    | succ N ih =>
      intro i j hj
      rw [Function.iterate_succ_apply']
      simp only [delta, ih (i + 1) j hj, ih i (j + 1) (by omega), sub_self]
  have boundary (d : ℤ → ℤ → State D)
      (h : ∀ i j : ℤ, 0 ≤ j → d i j = 0) (N : ℕ) (i : ℤ) :
      (delta^[N] d) i (-1) = d (i + N) (-1) := by
    induction N generalizing i with
    | zero => simp
    | succ N ih =>
      rw [Function.iterate_succ_apply']
      change (delta^[N] d) (i + 1) (-1) - (delta^[N] d) i 0 = _
      rw [ih, rightTail d h N i 0 (by omega), sub_zero]
      apply congrArg (fun k : ℤ => d k (-1))
      omega
  have homogeneousModes (n : ℤ) (x : State D) (q : ℕ)
      (hx : LatticeMatterGhostStateField.parity D x = (-1 : ℂ)^q • x) :
      (F[[n]]) x = 0 := by
    obtain ⟨N, killed⟩ := locality x q hx
    let d : ℤ → ℤ → State D := fun i j =>
      signedComm ((-1 : ℂ)^(r*q)) F (LatticeMatterGhostStateField.Y D x)
        i j (LatticeMatterGhostStateField.vacuum D)
    have tail : ∀ i j : ℤ, 0 ≤ j → d i j = 0 := by
      intro i j hj
      dsimp [d, signedComm]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
        original.2.2.1 x j hj, vacuumZero, map_zero, smul_zero, sub_self]
    have hd : delta^[N] d = 0 := by
      rw [evaluateDelta, killed]
      rfl
    have h := congrFun (congrFun hd (n - N)) (-1)
    rw [boundary d tail N (n - N)] at h
    simpa only [d, signedComm, sub_add_cancel, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.mul_apply, vacuumZero, map_zero,
      smul_zero, sub_zero, original.2.1 x, Pi.zero_apply] using h
  have allModes (n : ℤ) (x : State D) : (F[[n]]) x = 0 := by
    let x0 := (2 : ℂ)⁻¹ • (x + LatticeMatterGhostStateField.parity D x)
    let x1 := (2 : ℂ)⁻¹ • (x - LatticeMatterGhostStateField.parity D x)
    have h0 : LatticeMatterGhostStateField.parity D x0 = (-1 : ℂ)^0 • x0 := by
      dsimp [x0]
      rw [map_smul, map_add, parity_square]
      simp only [pow_zero, one_smul]
      congr 1
      abel
    have h1 : LatticeMatterGhostStateField.parity D x1 = (-1 : ℂ)^1 • x1 := by
      dsimp [x1]
      rw [map_smul, map_sub, parity_square]
      norm_num only [pow_one]
      module
    have hx : x = x0 + x1 := by dsimp [x0, x1]; module
    rw [hx, map_add, homogeneousModes n x0 0 h0,
      homogeneousModes n x1 1 h1, add_zero]
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  simpa only [map_zero, Pi.zero_apply, LinearMap.zero_apply]
    using allModes (-power - 1) x

/- Literal current parity. This is consumed by totalCharge_field_superderivation;
it is an organizational application of the actual ghost parity suppliers. -/
private theorem current_odd (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    LatticeMatterGhostStateField.parity D (LatticeMatterGhostStateField.Jtot D H) =
      (-1 : ℂ)^1 • LatticeMatterGhostStateField.Jtot D H := by
  have hc : CountableOccupationFock.parity (CountableOccupationFock.ket {1}) =
      (-1 : ℂ)^1 • CountableOccupationFock.ket {1} := by
    simp [parity_ket]
  simp only [LatticeMatterGhostStateField.Jtot, map_add,
    LatticeMatterGhostStateField.parity, TensorProduct.map_tmul, LinearMap.id_apply,
    hc, BcGhostConformalBRSTState.current_odd, TensorProduct.tmul_smul, smul_add]

/-- Every homogeneous ORIGINAL coupled field, every integer mode, and the
ORIGINAL totalCharge. Endomorphism equality includes every original input
state. D has unrestricted rank (including zero); H is completely arbitrary. -/
theorem totalCharge_field_superderivation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (s : State D) (p : ℕ)
    (hs : LatticeMatterGhostStateField.parity D s = (-1 : ℂ)^p • s) (n : ℤ) :
    LatticeBRST.totalCharge D H * ((LatticeMatterGhostStateField.Y D s)[[n]]) -
      (-1 : ℂ)^p • (((LatticeMatterGhostStateField.Y D s)[[n]]) *
        LatticeBRST.totalCharge D H) =
      ((LatticeMatterGhostStateField.Y D (LatticeBRST.totalCharge D H s))[[n]]) := by
  let Q := LatticeBRST.totalCharge D H
  let T := LatticeMatterGhostStateField.translation D
  let A := LatticeMatterGhostStateField.Y D (LatticeMatterGhostStateField.Jtot D H)
  let B := LatticeMatterGhostStateField.Y D s
  let e : ℂ := (-1 : ℂ)^p
  let F := zeroResidue e A B
  have original := LatticeMatterGhostStateField.stateField_vacuum_creation D
  have aZero : (A[[0]]) = Q := LatticeMatterGhostStateField.current_zero_mode D H
  have qVacuum : Q (LatticeMatterGhostStateField.vacuum D) = 0 := by
    rw [← aZero]
    exact original.2.2.1 (LatticeMatterGhostStateField.Jtot D H) 0 (by omega)
  have tq : T * Q = Q * T := by
    have h := LatticeMatterGhostStateField.stateField_covariance D
      (LatticeMatterGhostStateField.Jtot D H) 0
    rw [LatticeMatterGhostStateField.current_zero_mode] at h
    simpa only [Int.cast_zero, neg_zero, zero_smul, sub_eq_zero] using h
  have fModes (m : ℤ) :
      (F[[m]]) = Q * (B[[m]]) - e • ((B[[m]]) * Q) := by
    dsimp only [F]
    rw [zeroResidue_modes, aZero]
  have fCovariant (m : ℤ) :
      T * (F[[m]]) - (F[[m]]) * T = -(m : ℂ) • (F[[m - 1]]) := by
    have commute (x : State D) : T (Q x) = Q (T x) := LinearMap.congr_fun tq x
    have covariance (x : State D) :
        T ((B[[m]]) x) = ((B[[m]]) (T x)) + -(m : ℂ) • ((B[[m - 1]]) x) := by
      have h := LinearMap.congr_fun
        (LatticeMatterGhostStateField.stateField_covariance D s m) x
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    apply LinearMap.ext
    intro x
    simp only [fModes, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      map_sub, map_smul]
    rw [commute, covariance x, map_add, map_smul, covariance (Q x), commute x]
    module
  have qParity : LatticeMatterGhostStateField.parity D * Q =
      -(Q * LatticeMatterGhostStateField.parity D) := by
    have h := LatticeMatterGhostStateField.stateField_parity D
      (LatticeMatterGhostStateField.Jtot D H) 0
    rw [current_odd, map_smul] at h
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply, pow_one, neg_one_smul,
      map_neg, Pi.neg_apply, LatticeMatterGhostStateField.current_zero_mode] at h
    change LatticeMatterGhostStateField.parity D * Q =
      (-Q) * LatticeMatterGhostStateField.parity D at h
    exact h.trans (neg_mul Q (LatticeMatterGhostStateField.parity D))
  have qsParity : LatticeMatterGhostStateField.parity D (Q s) =
      (-1 : ℂ)^(p + 1) • Q s := by
    have h := LinearMap.congr_fun qParity s
    simp only [Module.End.mul_apply, LinearMap.neg_apply, hs, map_smul] at h
    rw [h, pow_succ, mul_smul, neg_one_smul]
    module
  let R := F - LatticeMatterGhostStateField.Y D (Q s)
  have rCreative (m : ℤ) (hm : 0 ≤ m) :
      (R[[m]]) (LatticeMatterGhostStateField.vacuum D) = 0 := by
    change ((F[[m]]) - ((LatticeMatterGhostStateField.Y D (Q s))[[m]]))
      (LatticeMatterGhostStateField.vacuum D) = 0
    simp only [fModes, B, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      original.2.2.1 s m hm, original.2.2.1 (Q s) m hm,
      qVacuum, map_zero, smul_zero, sub_self]
  have rInitial : (R[[-1]]) (LatticeMatterGhostStateField.vacuum D) = 0 := by
    change ((F[[-1]]) - ((LatticeMatterGhostStateField.Y D (Q s))[[-1]]))
      (LatticeMatterGhostStateField.vacuum D) = 0
    simp only [fModes, B, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      original.2.1 s, original.2.1 (Q s), qVacuum, map_zero, smul_zero,
      sub_zero, sub_self]
  have rCovariant (m : ℤ) :
      T * (R[[m]]) - (R[[m]]) * T = -(m : ℂ) • (R[[m - 1]]) := by
    change T * ((F[[m]]) - ((LatticeMatterGhostStateField.Y D (Q s))[[m]])) -
      ((F[[m]]) - ((LatticeMatterGhostStateField.Y D (Q s))[[m]])) * T =
        -(m : ℂ) • ((F[[m - 1]]) - ((LatticeMatterGhostStateField.Y D (Q s))[[m - 1]]))
    calc
      _ = (T * (F[[m]]) - (F[[m]]) * T) -
          (T * ((LatticeMatterGhostStateField.Y D (Q s))[[m]]) -
            ((LatticeMatterGhostStateField.Y D (Q s))[[m]]) * T) := by
            simp only [mul_sub, sub_mul]
            abel
      _ = _ := by
        rw [fCovariant, LatticeMatterGhostStateField.stateField_covariance]
        module
  have rLocality (x : State D) (q : ℕ)
      (hx : LatticeMatterGhostStateField.parity D x = (-1 : ℂ)^q • x) :
      ∃ N : ℕ, delta^[N] (signedComm ((-1 : ℂ)^((p+1)*q)) R
        (LatticeMatterGhostStateField.Y D x)) = 0 := by
    have hab : ∃ N : ℕ, delta^[N] (signedComm e A B) = 0 := by
      have h := LatticeMatterGhostStateField.stateField_locality D
        (LatticeMatterGhostStateField.Jtot D H) s 1 p (current_odd D H) hs
      simp only [one_mul] at h
      exact h
    have hac : ∃ N : ℕ, delta^[N] (signedComm ((-1 : ℂ)^q) A
        (LatticeMatterGhostStateField.Y D x)) = 0 := by
      have h := LatticeMatterGhostStateField.stateField_locality D
        (LatticeMatterGhostStateField.Jtot D H) x 1 q (current_odd D H) hx
      simp only [one_mul] at h
      exact h
    have hbc : ∃ N : ℕ, delta^[N] (signedComm ((-1 : ℂ)^(p*q)) B
        (LatticeMatterGhostStateField.Y D x)) = 0 :=
      LatticeMatterGhostStateField.stateField_locality D s x p q hs hx
    have hsign : (-1 : ℂ)^q * (-1 : ℂ)^(p*q) = (-1 : ℂ)^((p+1)*q) := by
      rw [← pow_add]
      congr 1
      ring
    have hf := signed_zero_residue_locality e ((-1 : ℂ)^q) ((-1 : ℂ)^(p*q))
      A B (LatticeMatterGhostStateField.Y D x) hab hac hbc
    rw [hsign] at hf
    exact local_sub ((-1 : ℂ)^((p+1)*q)) F
      (LatticeMatterGhostStateField.Y D (Q s)) (LatticeMatterGhostStateField.Y D x) hf
      (LatticeMatterGhostStateField.stateField_locality D (Q s) x (p+1) q qsParity hx)
  have rZero : R = 0 := creative_unique D (p+1) R rCreative rInitial rCovariant rLocality
  have fields : F = LatticeMatterGhostStateField.Y D (Q s) := sub_eq_zero.mp rZero
  have modes := congrArg (fun F : VertexOperator ℂ (State D) => F[[n]]) fields
  rw [fModes] at modes
  exact modes

end
end D5.S3.VertexAlgebra.LatticeMatterGhostBRSTDerivation

